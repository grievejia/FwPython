import FwPython.Common.Forall2
import FwPython.Gradual.TypeSystem.TargetAdmissibility
import FwPython.Gradual.TypeSystem.ProgramTargetPrecision
import FwPython.Gradual.TypeSystem.ClassTable.WellFormednessCore
import FwPython.Gradual.TypeSystem.CheckedTargetPrecision
import FwPython.Gradual.TypeSystem.Method.TypeFacts

/-! # Single-type gradual source core

Core infrastructure for the safe-domain single-type gradual source front
end. Source environments store exactly one gradual type per binding; any
checked approximation is chosen later at elaboration sites. -/

/-! ## Source environment -/

structure SBinding where
  name : Identifier
  sourceTy : GTy
  deriving DecidableEq

abbrev SBindingEnv := List SBinding

def SBindingEnv.lookupBinding : SBindingEnv → Identifier → Option SBinding
  | [], _ => none
  | b :: rest, x => if b.name = x then some b else lookupBinding rest x

def SBindingEnv.lookupSource (Γ : SBindingEnv) (x : Identifier) : Option GTy :=
  (Γ.lookupBinding x).map (·.sourceTy)

def SBindingEnv.updateSource : SBindingEnv → Identifier → GTy → SBindingEnv
  | [], _, _ => []
  | b :: rest, x, S =>
    if b.name = x then { b with sourceTy := S } :: rest
    else b :: updateSource rest x S

abbrev lookupBinding := SBindingEnv.lookupBinding
abbrev lookupSource := SBindingEnv.lookupSource
abbrev updateSource := SBindingEnv.updateSource

/-! ## Source-callable admissibility -/

inductive SourceCallableTy (gct : GClassTable) : GTy → Prop where
  | any : SourceCallableTy gct .any
  | class_ : SourceCallableTy gct (.class_ C)
  | callable :
      SourceCallableTy gct P →
      RuntimePublicAnnotation gct R →
      SourceCallableTy gct (.callable P R)
  | union :
      SourceCallableTy gct G →
      SourceCallableTy gct H →
      SourceCallableTy gct (.union G H)
  | intersection :
      SourceCallableTy gct G →
      SourceCallableTy gct H →
      SourceCallableTy gct (.intersection G H)
  | bottom : SourceCallableTy gct .bottom
  | negClass : SourceCallableTy gct (.negClass cname)

private def formulaGTy_sourceCallable {gct : GClassTable} :
    (G : GTy) → FormulaGTy G → SourceCallableTy gct G
  | .any, .any => .any
  | .class_ _, .class_ => .class_
  | .union _ _, .union hf hg =>
      .union (formulaGTy_sourceCallable _ hf) (formulaGTy_sourceCallable _ hg)
  | .intersection _ _, .intersection hf hg =>
      .intersection (formulaGTy_sourceCallable _ hf) (formulaGTy_sourceCallable _ hg)
  | .bottom, .bottom => .bottom
  | .negClass _, .negClass => .negClass

private theorem checkedTargetTy_to_sourceCallableTy
    {gct : GClassTable} : (G : GTy) → CheckedTargetTy gct G → SourceCallableTy gct G
  | _, .classFormula hf => formulaGTy_sourceCallable _ hf
  | _, .callable hP hR =>
      .callable (checkedTargetTy_to_sourceCallableTy _ hP) (runtimePublicAnnotation_mk hR)
  | _, .union hG hH =>
      .union (checkedTargetTy_to_sourceCallableTy _ hG)
        (checkedTargetTy_to_sourceCallableTy _ hH)
  | _, .interCallableLeft hP hR hbm =>
      .intersection
        (.callable
          (checkedTargetTy_to_sourceCallableTy _ hP)
          (runtimePublicAnnotation_mk hR))
        (formulaGTy_sourceCallable _ hbm.toFormula)
  | _, .interCallableRight hbm hP hR =>
      .intersection
        (formulaGTy_sourceCallable _ hbm.toFormula)
        (.callable
          (checkedTargetTy_to_sourceCallableTy _ hP)
          (runtimePublicAnnotation_mk hR))

theorem runtimePublicAnnotation_to_sourceCallableTy
    {gct : GClassTable} (G : GTy) (hchecked : RuntimePublicAnnotation gct G) :
    SourceCallableTy gct G :=
  checkedTargetTy_to_sourceCallableTy G (runtimePublicAnnotation_checked hchecked)

/-! ## Environment invariants -/

def SourceEnvOk (gct : GClassTable) (Γ : SBindingEnv) : Prop :=
  ∀ b ∈ Γ,
    SourceCallableTy gct b.sourceTy ∧
    WellFormedGTy gct b.sourceTy

structure ElabBindingRel (gct : GClassTable)
    (b : SBinding) (p : Identifier × GTy) : Prop where
  name_eq : b.name = p.1
  checked_target : RuntimePublicAnnotation gct p.2
  checked_wf : WellFormedGTy gct p.2
  source_sub_checked : GradualSubtype gct b.sourceTy p.2

abbrev ElabEnvOk (gct : GClassTable) (Γ : SBindingEnv) (Δ : GTyEnv) :=
  Forall₂ (ElabBindingRel gct) Γ Δ

/-! ## Environment lemmas -/

theorem sourceEnvOk_lookup
    (hok : SourceEnvOk gct Γ)
    (hlook : Γ.lookupBinding x = some b) :
    SourceCallableTy gct b.sourceTy ∧
    WellFormedGTy gct b.sourceTy := by
  induction Γ with
  | nil =>
    simp [SBindingEnv.lookupBinding] at hlook
  | cons hd rest ih =>
    by_cases hname : hd.name = x
    · simp [SBindingEnv.lookupBinding, hname] at hlook
      cases hlook
      exact hok _ (.head _)
    · simp [SBindingEnv.lookupBinding, hname] at hlook
      exact ih (fun b' hb' => hok b' (.tail _ hb')) hlook

theorem sourceEnvOk_updateSource
    (hok : SourceEnvOk gct Γ)
    (hlook : Γ.lookupBinding x = some b)
    (hsrc : SourceCallableTy gct newSrc)
    (hwf : WellFormedGTy gct newSrc) :
    SourceEnvOk gct (Γ.updateSource x newSrc) := by
  intro b' hb'
  induction Γ with
  | nil =>
    simp [SBindingEnv.updateSource] at hb'
  | cons hd rest ih =>
    by_cases heq : hd.name = x
    · simp [SBindingEnv.updateSource, heq] at hb'
      cases hb' with
      | inl hb' =>
        cases hb'
        exact ⟨hsrc, hwf⟩
      | inr hb' =>
        exact hok b' (.tail _ hb')
    · simp [SBindingEnv.updateSource, heq] at hb'
      cases hb' with
      | inl hb' =>
        cases hb'
        exact hok _ (.head _)
      | inr hb' =>
        simp [SBindingEnv.lookupBinding, heq] at hlook
        exact ih (fun b'' hb'' => hok b'' (.tail _ hb'')) hlook hb'

theorem elabEnvOk_lookup
    (hok : ElabEnvOk gct Γ Δ)
    (hlook : Γ.lookupBinding x = some b) :
    ∃ T,
      Δ.lookup x = some T ∧
      RuntimePublicAnnotation gct T ∧
      WellFormedGTy gct T ∧
      GradualSubtype gct b.sourceTy T := by
  induction hok generalizing x b with
  | nil =>
    simp [SBindingEnv.lookupBinding] at hlook
  | @cons b₀ p₀ Γ Δ hrel hrest ih =>
    by_cases hname : b₀.name = x
    · simp [SBindingEnv.lookupBinding, hname] at hlook
      cases hlook
      refine ⟨p₀.2, ?_⟩
      have hx : x = p₀.1 := hname.symm.trans hrel.name_eq
      exact ⟨by simp [NamedEnv.lookup, hx], hrel.checked_target, hrel.checked_wf,
        by simpa using hrel.source_sub_checked⟩
    · simp [SBindingEnv.lookupBinding, hname] at hlook
      have hx : x ≠ p₀.1 := by
        intro hEq
        exact hname (hrel.name_eq.trans hEq.symm)
      have hp : p₀.1 ≠ x := by
        intro hEq
        exact hx hEq.symm
      obtain ⟨T, hΔ, hct, hwf, hsub⟩ := ih hlook
      exact ⟨T, by simp [NamedEnv.lookup, hp, hΔ], hct, hwf, hsub⟩

theorem elabEnvOk_lookup_runtimePublic
    (hok : ElabEnvOk gct Γ Δ)
    (hlookΓ : Γ.lookupBinding x = some b)
    (hlookΔ : Δ.lookup x = some T) :
    RuntimePublicAnnotation gct T := by
  obtain ⟨T', hlookΔ', hchecked, _, _⟩ := elabEnvOk_lookup hok hlookΓ
  rw [hlookΔ] at hlookΔ'
  cases hlookΔ'
  simpa using hchecked

theorem elabEnvOk_lookup_wellFormed
    (hok : ElabEnvOk gct Γ Δ)
    (hlookΓ : Γ.lookupBinding x = some b)
    (hlookΔ : Δ.lookup x = some T) :
    WellFormedGTy gct T := by
  obtain ⟨T', hlookΔ', _, hwf, _⟩ := elabEnvOk_lookup hok hlookΓ
  rw [hlookΔ] at hlookΔ'
  cases hlookΔ'
  simpa using hwf

theorem elabEnvOk_lookup_sourceSubtype
    (hok : ElabEnvOk gct Γ Δ)
    (hlookΓ : Γ.lookupBinding x = some b)
    (hlookΔ : Δ.lookup x = some T) :
    GradualSubtype gct b.sourceTy T := by
  obtain ⟨T', hlookΔ', _, _, hsub⟩ := elabEnvOk_lookup hok hlookΓ
  rw [hlookΔ] at hlookΔ'
  cases hlookΔ'
  simpa using hsub

theorem elabEnvOk_updateSource
    (hok : ElabEnvOk gct Γ Δ)
    (hlookΓ : Γ.lookupBinding x = some b)
    (hlookΔ : Δ.lookup x = some T)
    (hsub : GradualSubtype gct newSrc T) :
    ElabEnvOk gct (Γ.updateSource x newSrc) Δ := by
  induction hok generalizing x b T with
  | nil =>
    simp [SBindingEnv.lookupBinding] at hlookΓ
  | @cons b₀ p₀ Γ Δ hrel hrest ih =>
    by_cases hname : b₀.name = x
    · simp [SBindingEnv.lookupBinding, hname] at hlookΓ
      cases hlookΓ
      have hx : x = p₀.1 := hname.symm.trans hrel.name_eq
      have hT : p₀.2 = T := by
        simpa [NamedEnv.lookup, hx] using hlookΔ
      cases hT
      have hrel' : ElabBindingRel gct { b₀ with sourceTy := newSrc } p₀ := {
        name_eq := hrel.name_eq
        checked_target := hrel.checked_target
        checked_wf := hrel.checked_wf
        source_sub_checked := hsub
      }
      simpa [SBindingEnv.updateSource, hname] using (Forall₂.cons hrel' hrest)
    · simp [SBindingEnv.lookupBinding, hname] at hlookΓ
      have hx : x ≠ p₀.1 := by
        intro hEq
        exact hname (hrel.name_eq.trans hEq.symm)
      have hp : p₀.1 ≠ x := by
        intro hEq
        exact hx hEq.symm
      simpa [SBindingEnv.updateSource, hname] using
        (Forall₂.cons hrel (ih hlookΓ (by simpa [NamedEnv.lookup, hp] using hlookΔ) hsub))

theorem elabEnvOk_updateBoth
    (hok : ElabEnvOk gct Γ Δ)
    (hlookΓ : Γ.lookupBinding x = some b)
    (hlookΔ : Δ.lookup x = some T)
    (hchecked : RuntimePublicAnnotation gct newChecked)
    (hwf : WellFormedGTy gct newChecked)
    (hsub : GradualSubtype gct newSrc newChecked) :
    ElabEnvOk gct (Γ.updateSource x newSrc) (Δ.update x newChecked) := by
  induction hok generalizing x b T with
  | nil =>
    simp [SBindingEnv.lookupBinding] at hlookΓ
  | @cons b₀ p₀ Γ Δ hrel hrest ih =>
    by_cases hname : b₀.name = x
    · simp [SBindingEnv.lookupBinding, hname] at hlookΓ
      cases hlookΓ
      have hx : x = p₀.1 := hname.symm.trans hrel.name_eq
      have hp : p₀.1 = x := hrel.name_eq.symm.trans hname
      have hT : p₀.2 = T := by
        simpa [NamedEnv.lookup, hx] using hlookΔ
      cases hT
      have hrel' :
          ElabBindingRel gct { b₀ with sourceTy := newSrc } (p₀.1, newChecked) := {
        name_eq := by simpa using hrel.name_eq
        checked_target := hchecked
        checked_wf := hwf
        source_sub_checked := hsub
      }
      have hok' :
          ElabEnvOk gct ({ b₀ with sourceTy := newSrc } :: Γ) ((p₀.1, newChecked) :: Δ) :=
        .cons hrel' hrest
      simpa [SBindingEnv.updateSource, GTyEnv.update, NamedEnv.update, hname, hp] using hok'
    · simp [SBindingEnv.lookupBinding, hname] at hlookΓ
      have hx : x ≠ p₀.1 := by
        intro hEq
        exact hname (hrel.name_eq.trans hEq.symm)
      have hp : p₀.1 ≠ x := by
        intro hEq
        exact hname (hrel.name_eq.trans hEq)
      have hok' :
          ElabEnvOk gct (b₀ :: SBindingEnv.updateSource Γ x newSrc)
            (p₀ :: GTyEnv.update Δ x newChecked) :=
        .cons hrel (ih hlookΓ (by simpa [NamedEnv.lookup, hp] using hlookΔ))
      simpa [SBindingEnv.updateSource, GTyEnv.update, NamedEnv.update, hname, hp] using hok'

/-! ## Gradual subtype helpers -/

theorem gradualSubtype_union_left
    (gct : GClassTable) (G H : GTy) :
    GradualSubtype gct G (.union G H) := by
  simpa [GradualSubtype, upperBound] using IsSubtype.unionLeft IsSubtype.refl

theorem gradualSubtype_union_right
    (gct : GClassTable) (G H : GTy) :
    GradualSubtype gct H (.union G H) := by
  simpa [GradualSubtype, upperBound] using IsSubtype.unionRight IsSubtype.refl

theorem gradualSubtype_union_mono
    (hG : GradualSubtype gct G₁ G₂)
    (hH : GradualSubtype gct H₁ H₂) :
    GradualSubtype gct (.union G₁ H₁) (.union G₂ H₂) := by
  simpa [GradualSubtype, upperBound] using
    IsSubtype.unionElim
      (IsSubtype.trans hG (IsSubtype.unionLeft IsSubtype.refl))
      (IsSubtype.trans hH (IsSubtype.unionRight IsSubtype.refl))

theorem gradualSubtype_intersection_left
    (gct : GClassTable) (G H : GTy) :
    GradualSubtype gct (.intersection G H) G := by
  simpa [GradualSubtype, upperBound] using IsSubtype.interLeft IsSubtype.refl

theorem gradualSubtype_intersection_right
    (gct : GClassTable) (G H : GTy) :
    GradualSubtype gct (.intersection G H) H := by
  simpa [GradualSubtype, upperBound] using IsSubtype.interRight IsSubtype.refl

theorem gradualSubtype_intersection_mono
    (hG : GradualSubtype gct G₁ G₂)
    (hH : GradualSubtype gct H₁ H₂) :
    GradualSubtype gct (.intersection G₁ H₁) (.intersection G₂ H₂) := by
  simpa [GradualSubtype, upperBound] using
    IsSubtype.interIntro
      (IsSubtype.trans (IsSubtype.interLeft IsSubtype.refl) hG)
      (IsSubtype.trans (IsSubtype.interRight IsSubtype.refl) hH)

/-! ## Method lookup -/

theorem findGMethodType_unique
    (h1 : FindGMethodType gct C attr P₁ R₁)
    (h2 : FindGMethodType gct C attr P₂ R₂) :
    P₁ = P₂ ∧ R₁ = R₂ := by
  obtain ⟨c₁, mro₁, m₁, hfc₁, hmro₁, hfm₁, rfl, rfl⟩ := h1
  obtain ⟨c₂, mro₂, m₂, hfc₂, hmro₂, hfm₂, rfl, rfl⟩ := h2
  rw [hfc₁] at hfc₂
  cases hfc₂
  cases gComputeMro_determinism hmro₁ hmro₂
  rw [hfm₁] at hfm₂
  cases hfm₂
  exact ⟨rfl, rfl⟩

def lookupMethodTy? (gct : GClassTable) (C : Identifier)
    (attr : Identifier) : Option (GTy × GTy) :=
  match findGClass gct C with
  | none => none
  | some _ =>
      match computeGMro? gct C with
      | none => none
      | some mro =>
          match findGMethodInMro gct mro attr with
          | some m => some (m.paramTy, m.returnTy)
          | none => none

theorem lookupMethodTy?_of_find
    (hfind : FindGMethodType gct C attr P R) :
    lookupMethodTy? gct C attr = some (P, R) := by
  obtain ⟨c, mro, m, hfc, hmro, hfm, hparam, hreturn⟩ := hfind
  have hcomp : computeGMro? gct C = some mro := computeGMro?_complete hfc hmro
  subst hparam
  subst hreturn
  simp [lookupMethodTy?, hfc, hcomp, hfm]

private theorem lookupMethodTy?_find
    (hlookup : lookupMethodTy? gct C attr = some (P, R)) :
    FindGMethodType gct C attr P R := by
  unfold lookupMethodTy? at hlookup
  cases hfc : findGClass gct C with
  | none =>
      simp [hfc] at hlookup
  | some c =>
      cases hcomp : computeGMro? gct C with
      | none =>
          simp [hfc, hcomp] at hlookup
      | some mro =>
          cases hfm : findGMethodInMro gct mro attr with
          | none =>
              simp [hfc, hcomp, hfm] at hlookup
          | some m =>
              simp [hfc, hcomp, hfm] at hlookup
              obtain ⟨cls, hfc', hmro⟩ := computeGMro?_sound hcomp
              rw [hfc] at hfc'
              cases hfc'
              rcases hlookup with ⟨hparam, hreturn⟩
              exact ⟨c, mro, m, hfc, hmro, hfm, hparam, hreturn⟩

theorem lookupMethodTy?_eq_none_iff :
    lookupMethodTy? gct C attr = none ↔
      ¬ ∃ P R, FindGMethodType gct C attr P R := by
  constructor
  · intro hnone hex
    rcases hex with ⟨P, R, hfind⟩
    rw [lookupMethodTy?_of_find hfind] at hnone
    cases hnone
  · intro hnot
    cases hlookup : lookupMethodTy? gct C attr with
    | none =>
        rfl
    | some pr =>
        rcases pr with ⟨P, R⟩
        exfalso
        exact hnot ⟨P, R, lookupMethodTy?_find hlookup⟩

/-! ## Attribute typing -/

def mergeAttrUnionResult : Option GTy → Option GTy → Option GTy
  | some left, some right => some (.union left right)
  | _, _ => none

def mergeAttrIntersectionResult : Option GTy → Option GTy → Option GTy
  | none, none => none
  | some result, none => some result
  | none, some result => some result
  | some left, some right => some (.intersection left right)

def attrSourceTy? (gct : GClassTable) : GTy → Identifier → Option GTy
  | .any, _ => some .any
  | .bottom, _ => some .bottom
  | .negClass _, _ => none
  | .class_ C, attr =>
      match lookupMethodTy? gct C attr with
      | some (P, R) => some (.callable P R)
      | none => none
  | .callable _ _, attr =>
      match lookupMethodTy? gct boundMethodClass attr with
      | some (P, R) => some (.callable P R)
      | none => none
  | .union G H, attr =>
      mergeAttrUnionResult (attrSourceTy? gct G attr) (attrSourceTy? gct H attr)
  | .intersection G H, attr =>
      mergeAttrIntersectionResult
        (attrSourceTy? gct G attr)
        (attrSourceTy? gct H attr)

inductive AttrResultWitness (gct : GClassTable) (attr : Identifier) :
    GTy → Option GTy → Prop where
  | any :
      AttrResultWitness gct attr .any (some .any)
  | bottom :
      AttrResultWitness gct attr .bottom (some .bottom)
  | negClass :
      AttrResultWitness gct attr (.negClass cname) none
  | class_some
      (hlookup : lookupMethodTy? gct cname attr = some (paramTy, returnTy)) :
      AttrResultWitness gct attr (.class_ cname) (some (.callable paramTy returnTy))
  | class_none
      (hlookup : lookupMethodTy? gct cname attr = none) :
      AttrResultWitness gct attr (.class_ cname) none
  | callable_some
      (hlookup : lookupMethodTy? gct boundMethodClass attr = some (paramTy, returnTy)) :
      AttrResultWitness gct attr (.callable paramTy0 returnTy0)
        (some (.callable paramTy returnTy))
  | callable_none
      (hlookup : lookupMethodTy? gct boundMethodClass attr = none) :
      AttrResultWitness gct attr (.callable paramTy0 returnTy0) none
  | union_some
      (hleft : AttrResultWitness gct attr G (some left))
      (hright : AttrResultWitness gct attr H (some right)) :
      AttrResultWitness gct attr (.union G H) (some (.union left right))
  | union_none_left
      (hleft : AttrResultWitness gct attr G none)
      (hright : AttrResultWitness gct attr H resultH) :
      AttrResultWitness gct attr (.union G H) none
  | union_none_right
      (hleft : AttrResultWitness gct attr G (some left))
      (hright : AttrResultWitness gct attr H none) :
      AttrResultWitness gct attr (.union G H) none
  | inter_none
      (hleft : AttrResultWitness gct attr G none)
      (hright : AttrResultWitness gct attr H none) :
      AttrResultWitness gct attr (.intersection G H) none
  | inter_left
      (hleft : AttrResultWitness gct attr G (some result))
      (hright : AttrResultWitness gct attr H none) :
      AttrResultWitness gct attr (.intersection G H) (some result)
  | inter_right
      (hleft : AttrResultWitness gct attr G none)
      (hright : AttrResultWitness gct attr H (some result)) :
      AttrResultWitness gct attr (.intersection G H) (some result)
  | inter_both
      (hleft : AttrResultWitness gct attr G (some left))
      (hright : AttrResultWitness gct attr H (some right)) :
      AttrResultWitness gct attr (.intersection G H)
        (some (.intersection left right))

theorem attrSourceTy?_of_witness
    (hw : AttrResultWitness gct attr G result) :
    attrSourceTy? gct G attr = result := by
  induction hw with
  | any =>
      rfl
  | bottom =>
      rfl
  | negClass =>
      rfl
  | class_some hlookup =>
      simp [attrSourceTy?, hlookup]
  | class_none hlookup =>
      simp [attrSourceTy?, hlookup]
  | callable_some hlookup =>
      simp [attrSourceTy?, hlookup]
  | callable_none hlookup =>
      simp [attrSourceTy?, hlookup]
  | union_some _ _ ihLeft ihRight =>
      simp [attrSourceTy?, mergeAttrUnionResult, ihLeft, ihRight]
  | union_none_left _ _ ihLeft ihRight =>
      simp [attrSourceTy?, mergeAttrUnionResult, ihLeft, ihRight]
  | union_none_right _ _ ihLeft ihRight =>
      simp [attrSourceTy?, mergeAttrUnionResult, ihLeft, ihRight]
  | inter_none _ _ ihLeft ihRight =>
      simp [attrSourceTy?, mergeAttrIntersectionResult, ihLeft, ihRight]
  | inter_left _ _ ihLeft ihRight =>
      simp [attrSourceTy?, mergeAttrIntersectionResult, ihLeft, ihRight]
  | inter_right _ _ ihLeft ihRight =>
      simp [attrSourceTy?, mergeAttrIntersectionResult, ihLeft, ihRight]
  | inter_both _ _ ihLeft ihRight =>
      simp [attrSourceTy?, mergeAttrIntersectionResult, ihLeft, ihRight]

theorem attrSourceTy?_witness_of
    (hattr : attrSourceTy? gct G attr = result) :
    AttrResultWitness gct attr G result := by
  induction G generalizing attr result with
  | any =>
      simp [attrSourceTy?] at hattr
      cases hattr
      exact .any
  | bottom =>
      simp [attrSourceTy?] at hattr
      cases hattr
      exact .bottom
  | negClass cname =>
      simp [attrSourceTy?] at hattr
      cases hattr
      exact .negClass
  | class_ cname =>
      cases hlookup : lookupMethodTy? gct cname attr with
      | none =>
          simp [attrSourceTy?, hlookup] at hattr
          cases hattr
          exact .class_none hlookup
      | some methodTy =>
          rcases methodTy with ⟨paramTy, returnTy⟩
          simp [attrSourceTy?, hlookup] at hattr
          cases hattr
          exact .class_some hlookup
  | callable paramTy0 returnTy0 =>
      cases hlookup : lookupMethodTy? gct boundMethodClass attr with
      | none =>
          simp [attrSourceTy?, hlookup] at hattr
          cases hattr
          exact .callable_none hlookup
      | some methodTy =>
          rcases methodTy with ⟨paramTy, returnTy⟩
          simp [attrSourceTy?, hlookup] at hattr
          cases hattr
          exact .callable_some hlookup
  | union G H ihLeft ihRight =>
      cases hleft : attrSourceTy? gct G attr with
      | none =>
          have hwLeft : AttrResultWitness gct attr G none := ihLeft hleft
          cases hright : attrSourceTy? gct H attr with
          | none =>
              have hwRight : AttrResultWitness gct attr H none := ihRight hright
              simp [attrSourceTy?, mergeAttrUnionResult, hleft, hright] at hattr
              cases hattr
              exact .union_none_left hwLeft hwRight
          | some right =>
              have hwRight : AttrResultWitness gct attr H (some right) := ihRight hright
              simp [attrSourceTy?, mergeAttrUnionResult, hleft, hright] at hattr
              cases hattr
              exact .union_none_left hwLeft hwRight
      | some left =>
          have hwLeft : AttrResultWitness gct attr G (some left) := ihLeft hleft
          cases hright : attrSourceTy? gct H attr with
          | none =>
              have hwRight : AttrResultWitness gct attr H none := ihRight hright
              simp [attrSourceTy?, mergeAttrUnionResult, hleft, hright] at hattr
              cases hattr
              exact .union_none_right hwLeft hwRight
          | some right =>
              have hwRight : AttrResultWitness gct attr H (some right) := ihRight hright
              simp [attrSourceTy?, mergeAttrUnionResult, hleft, hright] at hattr
              cases hattr
              exact .union_some hwLeft hwRight
  | intersection G H ihLeft ihRight =>
      cases hleft : attrSourceTy? gct G attr with
      | none =>
          have hwLeft : AttrResultWitness gct attr G none := ihLeft hleft
          cases hright : attrSourceTy? gct H attr with
          | none =>
              have hwRight : AttrResultWitness gct attr H none := ihRight hright
              simp [attrSourceTy?, mergeAttrIntersectionResult, hleft, hright] at hattr
              cases hattr
              exact .inter_none hwLeft hwRight
          | some right =>
              have hwRight : AttrResultWitness gct attr H (some right) := ihRight hright
              simp [attrSourceTy?, mergeAttrIntersectionResult, hleft, hright] at hattr
              cases hattr
              exact .inter_right hwLeft hwRight
      | some left =>
          have hwLeft : AttrResultWitness gct attr G (some left) := ihLeft hleft
          cases hright : attrSourceTy? gct H attr with
          | none =>
              have hwRight : AttrResultWitness gct attr H none := ihRight hright
              simp [attrSourceTy?, mergeAttrIntersectionResult, hleft, hright] at hattr
              cases hattr
              exact .inter_left hwLeft hwRight
          | some right =>
              have hwRight : AttrResultWitness gct attr H (some right) := ihRight hright
              simp [attrSourceTy?, mergeAttrIntersectionResult, hleft, hright] at hattr
              cases hattr
              exact .inter_both hwLeft hwRight

theorem attrSourceTy?_class_find
    (hfind : FindGMethodType gct C attr P R) :
    attrSourceTy? gct (.class_ C) attr = some (.callable P R) := by
  exact attrSourceTy?_of_witness (.class_some (lookupMethodTy?_of_find hfind))

theorem attrSourceTy?_class_no_find
    (hfind : ¬ ∃ P R, FindGMethodType gct C attr P R) :
    attrSourceTy? gct (.class_ C) attr = none := by
  exact attrSourceTy?_of_witness (.class_none (lookupMethodTy?_eq_none_iff.mpr hfind))

theorem attrSourceTy?_boundMethod_find
    (hfind : FindGMethodType gct boundMethodClass attr P R) :
    attrSourceTy? gct (.callable P₀ R₀) attr = some (.callable P R) := by
  exact attrSourceTy?_of_witness (.callable_some (lookupMethodTy?_of_find hfind))

theorem attrSourceTy?_boundMethod_no_find
    (hfind : ¬ ∃ P R, FindGMethodType gct boundMethodClass attr P R) :
    attrSourceTy? gct (.callable P₀ R₀) attr = none := by
  exact attrSourceTy?_of_witness (.callable_none (lookupMethodTy?_eq_none_iff.mpr hfind))

private theorem methodTy_callable_and_wf
    (hwfct : WellFormedGClassTableCore gct)
    (hfind : FindGMethodType gct C attr P R) :
    SourceCallableTy gct (.callable P R) ∧ WellFormedGTy gct (.callable P R) :=
  let hchecked := runtimePublicAnnotation_of_findGMethodType hwfct hfind
  let hwf := wellFormedGTy_of_findGMethodType hwfct hfind
  ⟨.callable (runtimePublicAnnotation_to_sourceCallableTy _ hchecked.1)
      hchecked.2,
   .callable hwf.1 hwf.2⟩

theorem attrSourceTy?_callable_and_wf
    (hwfct : WellFormedGClassTableCore gct)
    (hattr : attrSourceTy? gct G attr = some R) :
    SourceCallableTy gct R ∧ WellFormedGTy gct R := by
  have hw := attrSourceTy?_witness_of hattr
  cases hw with
  | any =>
      exact ⟨.any, .any⟩
  | bottom =>
      exact ⟨.bottom, .bottom⟩
  | class_some hlookup =>
      exact methodTy_callable_and_wf hwfct (lookupMethodTy?_find hlookup)
  | callable_some hlookup =>
      exact methodTy_callable_and_wf hwfct (lookupMethodTy?_find hlookup)
  | union_some hleft hright =>
      exact
        ⟨.union
            (attrSourceTy?_callable_and_wf hwfct (attrSourceTy?_of_witness hleft)).1
            (attrSourceTy?_callable_and_wf hwfct (attrSourceTy?_of_witness hright)).1,
          .union
            (attrSourceTy?_callable_and_wf hwfct (attrSourceTy?_of_witness hleft)).2
            (attrSourceTy?_callable_and_wf hwfct (attrSourceTy?_of_witness hright)).2⟩
  | inter_left hleft _ =>
      exact attrSourceTy?_callable_and_wf hwfct (attrSourceTy?_of_witness hleft)
  | inter_right _ hright =>
      exact attrSourceTy?_callable_and_wf hwfct (attrSourceTy?_of_witness hright)
  | inter_both hleft hright =>
      exact
        ⟨.intersection
            (attrSourceTy?_callable_and_wf hwfct (attrSourceTy?_of_witness hleft)).1
            (attrSourceTy?_callable_and_wf hwfct (attrSourceTy?_of_witness hright)).1,
          .intersection
            (attrSourceTy?_callable_and_wf hwfct (attrSourceTy?_of_witness hleft)).2
            (attrSourceTy?_callable_and_wf hwfct (attrSourceTy?_of_witness hright)).2⟩

theorem attrSourceTy?_sourceCallable
    (hwfct : WellFormedGClassTableCore gct)
    (hattr : attrSourceTy? gct G attr = some R) :
    SourceCallableTy gct R :=
  (attrSourceTy?_callable_and_wf hwfct hattr).1

theorem attrSourceTy?_wellFormed
    (hwfct : WellFormedGClassTableCore gct)
    (hattr : attrSourceTy? gct G attr = some R) :
    WellFormedGTy gct R :=
  (attrSourceTy?_callable_and_wf hwfct hattr).2

private inductive StructuralTargetPrecision : GTy → GTy → Prop where
  | refl :
      StructuralTargetPrecision G G
  | toAny :
      StructuralTargetPrecision G .any
  | callable :
      StructuralTargetPrecision P₁ P₂ →
      StructuralTargetPrecision R₁ R₂ →
      StructuralTargetPrecision (.callable P₁ R₁) (.callable P₂ R₂)
  | union :
      StructuralTargetPrecision G₁ G₂ →
      StructuralTargetPrecision H₁ H₂ →
      StructuralTargetPrecision (.union G₁ H₁) (.union G₂ H₂)
  | intersection :
      StructuralTargetPrecision G₁ G₂ →
      StructuralTargetPrecision H₁ H₂ →
      StructuralTargetPrecision (.intersection G₁ H₁) (.intersection G₂ H₂)

private theorem checkedTargetOfGTy_injective
    (h : checkedTargetOfGTy G₁ = checkedTargetOfGTy G₂) :
    G₁ = G₂ := by
  induction G₁ generalizing G₂ with
  | any =>
      cases G₂ <;> simp [checkedTargetOfGTy] at h <;> rfl
  | class_ =>
      cases G₂ with
      | class_ _ =>
          simp [checkedTargetOfGTy] at h
          cases h
          rfl
      | any => simp [checkedTargetOfGTy] at h
      | callable _ _ => simp [checkedTargetOfGTy] at h
      | union _ _ => simp [checkedTargetOfGTy] at h
      | intersection _ _ => simp [checkedTargetOfGTy] at h
      | bottom => simp [checkedTargetOfGTy] at h
      | negClass _ => simp [checkedTargetOfGTy] at h
  | callable P R ihP ihR =>
      cases G₂ with
      | callable P' R' =>
          simp [checkedTargetOfGTy] at h
          rcases h with ⟨hP, hR⟩
          cases ihP hP
          cases ihR hR
          rfl
      | any => simp [checkedTargetOfGTy] at h
      | class_ _ => simp [checkedTargetOfGTy] at h
      | union _ _ => simp [checkedTargetOfGTy] at h
      | intersection _ _ => simp [checkedTargetOfGTy] at h
      | bottom => simp [checkedTargetOfGTy] at h
      | negClass _ => simp [checkedTargetOfGTy] at h
  | union G H ihG ihH =>
      cases G₂ with
      | union G' H' =>
          simp [checkedTargetOfGTy] at h
          rcases h with ⟨hG, hH⟩
          cases ihG hG
          cases ihH hH
          rfl
      | any => simp [checkedTargetOfGTy] at h
      | class_ _ => simp [checkedTargetOfGTy] at h
      | callable _ _ => simp [checkedTargetOfGTy] at h
      | intersection _ _ => simp [checkedTargetOfGTy] at h
      | bottom => simp [checkedTargetOfGTy] at h
      | negClass _ => simp [checkedTargetOfGTy] at h
  | intersection G H ihG ihH =>
      cases G₂ with
      | intersection G' H' =>
          simp [checkedTargetOfGTy] at h
          rcases h with ⟨hG, hH⟩
          cases ihG hG
          cases ihH hH
          rfl
      | any => simp [checkedTargetOfGTy] at h
      | class_ _ => simp [checkedTargetOfGTy] at h
      | callable _ _ => simp [checkedTargetOfGTy] at h
      | union _ _ => simp [checkedTargetOfGTy] at h
      | bottom => simp [checkedTargetOfGTy] at h
      | negClass _ => simp [checkedTargetOfGTy] at h
  | bottom =>
      cases G₂ <;> simp [checkedTargetOfGTy] at h <;> rfl
  | negClass =>
      cases G₂ with
      | negClass _ =>
          simp [checkedTargetOfGTy] at h
          cases h
          rfl
      | any => simp [checkedTargetOfGTy] at h
      | class_ _ => simp [checkedTargetOfGTy] at h
      | callable _ _ => simp [checkedTargetOfGTy] at h
      | union _ _ => simp [checkedTargetOfGTy] at h
      | intersection _ _ => simp [checkedTargetOfGTy] at h
      | bottom => simp [checkedTargetOfGTy] at h

private theorem structuralTargetPrecision_of_checkedTargetPrecision :
    ∀ {T₁ T₂ G₁ G₂},
      CheckedTargetPrecision T₁ T₂ →
      T₁ = checkedTargetOfGTy G₁ →
      T₂ = checkedTargetOfGTy G₂ →
      StructuralTargetPrecision G₁ G₂
  | _, _, G₁, G₂, .refl, hT₁, hT₂ => by
      have hEq : G₁ = G₂ :=
        checkedTargetOfGTy_injective (hT₁.symm.trans hT₂)
      cases hEq
      exact .refl
  | _, _, G₁, G₂, .toAny, hT₁, hT₂ => by
      have hEq : G₂ = .any :=
        checkedTargetOfGTy_injective hT₂.symm
      cases hEq
      exact .toAny
  | _, _, G₁, G₂, .callable hParam hReturn, hT₁, hT₂ => by
      cases G₁ with
      | callable P₁ R₁ =>
          cases hT₁
          cases G₂ with
          | callable P₂ R₂ =>
              cases hT₂
              exact
                .callable
                  (structuralTargetPrecision_of_checkedTargetPrecision hParam rfl rfl)
                  (structuralTargetPrecision_of_checkedTargetPrecision hReturn rfl rfl)
          | any => cases hT₂
          | class_ _ => cases hT₂
          | union _ _ => cases hT₂
          | intersection _ _ => cases hT₂
          | bottom => cases hT₂
          | negClass _ => cases hT₂
      | any => cases hT₁
      | class_ _ => cases hT₁
      | union _ _ => cases hT₁
      | intersection _ _ => cases hT₁
      | bottom => cases hT₁
      | negClass _ => cases hT₁
  | _, _, G₁, G₂, .union hLeft hRight, hT₁, hT₂ => by
      cases G₁ with
      | union G₁ H₁ =>
          cases hT₁
          cases G₂ with
          | union G₂ H₂ =>
              cases hT₂
              exact
                .union
                  (structuralTargetPrecision_of_checkedTargetPrecision hLeft rfl rfl)
                  (structuralTargetPrecision_of_checkedTargetPrecision hRight rfl rfl)
          | any => cases hT₂
          | class_ _ => cases hT₂
          | callable _ _ => cases hT₂
          | intersection _ _ => cases hT₂
          | bottom => cases hT₂
          | negClass _ => cases hT₂
      | any => cases hT₁
      | class_ _ => cases hT₁
      | callable _ _ => cases hT₁
      | intersection _ _ => cases hT₁
      | bottom => cases hT₁
      | negClass _ => cases hT₁
  | _, _, G₁, G₂, .intersection hLeft hRight, hT₁, hT₂ => by
      cases G₁ with
      | intersection G₁ H₁ =>
          cases hT₁
          cases G₂ with
          | intersection G₂ H₂ =>
              cases hT₂
              exact
                .intersection
                  (structuralTargetPrecision_of_checkedTargetPrecision hLeft rfl rfl)
                  (structuralTargetPrecision_of_checkedTargetPrecision hRight rfl rfl)
          | any => cases hT₂
          | class_ _ => cases hT₂
          | callable _ _ => cases hT₂
          | union _ _ => cases hT₂
          | bottom => cases hT₂
          | negClass _ => cases hT₂
      | any => cases hT₁
      | class_ _ => cases hT₁
      | callable _ _ => cases hT₁
      | union _ _ => cases hT₁
      | bottom => cases hT₁
      | negClass _ => cases hT₁

private theorem structuralTargetPrecision_of_annotationTargetPrecision
    (h : AnnotationTargetPrecision G₁ G₂) :
    StructuralTargetPrecision G₁ G₂ := by
  exact structuralTargetPrecision_of_checkedTargetPrecision h rfl rfl

private theorem annotationTargetPrecision_of_structuralTargetPrecision
    (h : StructuralTargetPrecision G₁ G₂) :
    AnnotationTargetPrecision G₁ G₂ := by
  induction h with
  | refl =>
      exact .refl
  | toAny =>
      exact .toAny
  | callable _ _ ihParam ihReturn =>
      simpa [AnnotationTargetPrecision, checkedTargetOfGTy] using
        CheckedTargetPrecision.callable ihParam ihReturn
  | union _ _ ihLeft ihRight =>
      simpa [AnnotationTargetPrecision, checkedTargetOfGTy] using
        CheckedTargetPrecision.union ihLeft ihRight
  | intersection _ _ ihLeft ihRight =>
      simpa [AnnotationTargetPrecision, checkedTargetOfGTy] using
        CheckedTargetPrecision.intersection ihLeft ihRight

/-! ## Call summaries -/

structure CallableFacet where
  paramTy : GTy
  returnTy : GTy
  deriving DecidableEq, Repr

inductive CallableSummary where
  | tainted
  | empty
  | leaf : CallableFacet -> CallableSummary
  | union : CallableSummary -> CallableSummary -> CallableSummary
  | intersection : CallableSummary -> CallableSummary -> CallableSummary
  deriving DecidableEq, Repr

def CallableFacetOk (gct : GClassTable) (f : CallableFacet) : Prop :=
  SourceCallableTy gct f.paramTy ∧
  WellFormedGTy gct f.paramTy ∧
  SourceCallableTy gct f.returnTy ∧
  WellFormedGTy gct f.returnTy

inductive CallableSummaryOk (gct : GClassTable) : CallableSummary -> Prop where
  | tainted :
      CallableSummaryOk gct .tainted
  | empty :
      CallableSummaryOk gct .empty
  | leaf
      (hfacet : CallableFacetOk gct f) :
      CallableSummaryOk gct (.leaf f)
  | union
      (hs : CallableSummaryOk gct s)
      (ht : CallableSummaryOk gct t) :
      CallableSummaryOk gct (.union s t)
  | intersection
      (hs : CallableSummaryOk gct s)
      (ht : CallableSummaryOk gct t) :
      CallableSummaryOk gct (.intersection s t)

inductive SourceBranchTag where
  | left
  | right
  deriving DecidableEq, Ord, Repr

instance : Std.LawfulEqOrd SourceBranchTag where
  compare_self := by
    intro tag
    cases tag <;> rfl
  eq_of_compare := by
    intro x y hcmp
    cases x <;> cases y <;> cases hcmp <;> rfl

abbrev SourceOriginTrace := List SourceBranchTag

private def insertSourceOriginTrace
    (trace : SourceOriginTrace) :
    List SourceOriginTrace → List SourceOriginTrace
  | [] => [trace]
  | head :: tail =>
      match compare trace head with
      | .lt => trace :: head :: tail
      | .eq => head :: tail
      | .gt => head :: insertSourceOriginTrace trace tail

/-- Canonical sorted-deduplicated origin traces. The derived `Ord` instance on
`List SourceBranchTag>` gives the intended lexicographic order with
`left < right` and shorter-prefix-first. -/
def canonicalSourceOriginSet : List SourceOriginTrace → List SourceOriginTrace
  | [] => []
  | trace :: traces =>
      insertSourceOriginTrace trace (canonicalSourceOriginSet traces)

def mergeCanonicalSourceOriginSets
    (left right : List SourceOriginTrace) :
    List SourceOriginTrace :=
  canonicalSourceOriginSet (left ++ right)

def prefixCanonicalSourceOriginSet
    (tag : SourceBranchTag)
    (origins : List SourceOriginTrace) :
    List SourceOriginTrace :=
  canonicalSourceOriginSet (origins.map (List.cons tag))

private theorem mem_insertSourceOriginTrace
    (trace : SourceOriginTrace) :
    trace ∈ insertSourceOriginTrace trace₀ traces ↔
      trace = trace₀ ∨ trace ∈ traces := by
  induction traces with
  | nil =>
      simp [insertSourceOriginTrace]
  | cons head tail ih =>
      cases hcmp : compare trace₀ head with
      | lt =>
          simp [insertSourceOriginTrace, hcmp]
      | eq =>
          have hEq : trace₀ = head := by
            exact (Std.LawfulEqOrd.compare_eq_iff_eq (a := trace₀) (b := head)).mp hcmp
          constructor
          · intro h
            simp [insertSourceOriginTrace, hEq] at h
            rcases h with h | h
            · exact Or.inl (h.trans hEq.symm)
            · exact Or.inr (by simp [h])
          · intro h
            rcases h with h | h
            · simp [insertSourceOriginTrace, hEq, h]
            · simpa [insertSourceOriginTrace, hEq] using h
      | gt =>
          simp [insertSourceOriginTrace, hcmp, ih, or_left_comm]

private theorem mem_canonicalSourceOriginSet
    (trace : SourceOriginTrace) :
    trace ∈ canonicalSourceOriginSet traces ↔ trace ∈ traces := by
  induction traces with
  | nil =>
      simp [canonicalSourceOriginSet]
  | cons trace₀ traces ih =>
      rw [canonicalSourceOriginSet]
      rw [mem_insertSourceOriginTrace]
      simp [ih]

private theorem mem_mergeCanonicalSourceOriginSets
    (trace : SourceOriginTrace) :
    trace ∈ mergeCanonicalSourceOriginSets left right ↔
      trace ∈ left ∨ trace ∈ right := by
  simp [mergeCanonicalSourceOriginSets, mem_canonicalSourceOriginSet, List.mem_append]

private theorem mem_prefixCanonicalSourceOriginSet
    (tag : SourceBranchTag)
    (trace : SourceOriginTrace) :
    trace ∈ prefixCanonicalSourceOriginSet tag origins ↔
      ∃ trace', trace = tag :: trace' ∧ trace' ∈ origins := by
  simp [prefixCanonicalSourceOriginSet, mem_canonicalSourceOriginSet, List.mem_map]
  constructor
  · rintro ⟨trace', hmem, rfl⟩
    exact ⟨trace', rfl, hmem⟩
  · rintro ⟨trace', rfl, hmem⟩
    exact ⟨trace', hmem, rfl⟩

inductive CallableFacetOrigin : GTy -> CallableFacet -> Prop where
  | callable :
      CallableFacetOrigin (.callable P R)
        { paramTy := P, returnTy := R }
  | union_left :
      CallableFacetOrigin G f ->
      CallableFacetOrigin (.union G H) f
  | union_right :
      CallableFacetOrigin H f ->
      CallableFacetOrigin (.union G H) f
  | inter_left :
      CallableFacetOrigin G f ->
      CallableFacetOrigin (.intersection G H) f
  | inter_right :
      CallableFacetOrigin H f ->
      CallableFacetOrigin (.intersection G H) f

inductive CallableFacetOriginTrace : GTy -> CallableFacet -> SourceOriginTrace -> Prop where
  | callable :
      CallableFacetOriginTrace
        (.callable P R)
        { paramTy := P, returnTy := R }
        []
  | union_left :
      CallableFacetOriginTrace G f trace ->
      CallableFacetOriginTrace (.union G H) f (.left :: trace)
  | union_right :
      CallableFacetOriginTrace H f trace ->
      CallableFacetOriginTrace (.union G H) f (.right :: trace)
  | inter_left :
      CallableFacetOriginTrace G f trace ->
      CallableFacetOriginTrace (.intersection G H) f (.left :: trace)
  | inter_right :
      CallableFacetOriginTrace H f trace ->
      CallableFacetOriginTrace (.intersection G H) f (.right :: trace)

theorem callableFacetOrigin_of_trace
    (h : CallableFacetOriginTrace G f trace) :
    CallableFacetOrigin G f := by
  induction h with
  | callable =>
      exact .callable
  | union_left _ ih =>
      exact .union_left ih
  | union_right _ ih =>
      exact .union_right ih
  | inter_left _ ih =>
      exact .inter_left ih
  | inter_right _ ih =>
      exact .inter_right ih

theorem callableFacetOrigin_has_trace
    (h : CallableFacetOrigin G f) :
    ∃ trace, CallableFacetOriginTrace G f trace := by
  induction h with
  | callable =>
      exact ⟨[], .callable⟩
  | union_left h ih =>
      rcases ih with ⟨trace, htrace⟩
      exact ⟨.left :: trace, .union_left htrace⟩
  | union_right h ih =>
      rcases ih with ⟨trace, htrace⟩
      exact ⟨.right :: trace, .union_right htrace⟩
  | inter_left h ih =>
      rcases ih with ⟨trace, htrace⟩
      exact ⟨.left :: trace, .inter_left htrace⟩
  | inter_right h ih =>
      rcases ih with ⟨trace, htrace⟩
      exact ⟨.right :: trace, .inter_right htrace⟩

inductive AttrResultOrigin (gct : GClassTable) (attr : Identifier) : GTy → GTy → Prop where
  | any :
      AttrResultOrigin gct attr .any .any
  | class_ :
      FindGMethodType gct C attr P R →
      AttrResultOrigin gct attr (.class_ C) (.callable P R)
  | callable :
      FindGMethodType gct boundMethodClass attr P R →
      AttrResultOrigin gct attr (.callable P₀ R₀) (.callable P R)
  | union_left :
      AttrResultOrigin gct attr G R →
      AttrResultOrigin gct attr (.union G H) R
  | union_right :
      AttrResultOrigin gct attr H R →
      AttrResultOrigin gct attr (.union G H) R
  | inter_left :
      AttrResultOrigin gct attr G R →
      AttrResultOrigin gct attr (.intersection G H) R
  | inter_right :
      AttrResultOrigin gct attr H R →
      AttrResultOrigin gct attr (.intersection G H) R
  | bottom :
      AttrResultOrigin gct attr .bottom .bottom

inductive AttrResultOriginTrace
    (gct : GClassTable) (attr : Identifier) :
    GTy → GTy → SourceOriginTrace → Prop where
  | any :
      AttrResultOriginTrace gct attr .any .any []
  | class_ :
      FindGMethodType gct C attr P R →
      AttrResultOriginTrace gct attr (.class_ C) (.callable P R) []
  | callable :
      FindGMethodType gct boundMethodClass attr P R →
      AttrResultOriginTrace gct attr (.callable P₀ R₀) (.callable P R) []
  | union_left :
      AttrResultOriginTrace gct attr G R trace →
      AttrResultOriginTrace gct attr (.union G H) R (.left :: trace)
  | union_right :
      AttrResultOriginTrace gct attr H R trace →
      AttrResultOriginTrace gct attr (.union G H) R (.right :: trace)
  | inter_left :
      AttrResultOriginTrace gct attr G R trace →
      AttrResultOriginTrace gct attr (.intersection G H) R (.left :: trace)
  | inter_right :
      AttrResultOriginTrace gct attr H R trace →
      AttrResultOriginTrace gct attr (.intersection G H) R (.right :: trace)
  | bottom :
      AttrResultOriginTrace gct attr .bottom .bottom []

theorem attrResultOrigin_of_trace
    (h : AttrResultOriginTrace gct attr G R trace) :
    AttrResultOrigin gct attr G R := by
  induction h with
  | any =>
      exact .any
  | class_ hfind =>
      exact .class_ hfind
  | callable hfind =>
      exact .callable hfind
  | union_left _ ih =>
      exact .union_left ih
  | union_right _ ih =>
      exact .union_right ih
  | inter_left _ ih =>
      exact .inter_left ih
  | inter_right _ ih =>
      exact .inter_right ih
  | bottom =>
      exact .bottom

theorem attrResultOrigin_has_trace
    (h : AttrResultOrigin gct attr G R) :
    ∃ trace, AttrResultOriginTrace gct attr G R trace := by
  induction h with
  | any =>
      exact ⟨[], .any⟩
  | class_ hfind =>
      exact ⟨[], .class_ hfind⟩
  | callable hfind =>
      exact ⟨[], .callable hfind⟩
  | union_left _ ih =>
      rcases ih with ⟨trace, htrace⟩
      exact ⟨.left :: trace, .union_left htrace⟩
  | union_right _ ih =>
      rcases ih with ⟨trace, htrace⟩
      exact ⟨.right :: trace, .union_right htrace⟩
  | inter_left _ ih =>
      rcases ih with ⟨trace, htrace⟩
      exact ⟨.left :: trace, .inter_left htrace⟩
  | inter_right _ ih =>
      rcases ih with ⟨trace, htrace⟩
      exact ⟨.right :: trace, .inter_right htrace⟩
  | bottom =>
      exact ⟨[], .bottom⟩

inductive SourceOperatorInputCorrespondence : GTy → GTy → Prop where
  | any :
      SourceOperatorInputCorrespondence .any .any
  | class_ :
      SourceOperatorInputCorrespondence (.class_ C) (.class_ C)
  | callable :
      SourceOperatorInputCorrespondence P₁ P₂ →
      SourceOperatorInputCorrespondence R₁ R₂ →
      SourceOperatorInputCorrespondence (.callable P₁ R₁) (.callable P₂ R₂)
  | union :
      SourceOperatorInputCorrespondence G₁ G₂ →
      SourceOperatorInputCorrespondence H₁ H₂ →
      SourceOperatorInputCorrespondence (.union G₁ H₁) (.union G₂ H₂)
  | intersection :
      SourceOperatorInputCorrespondence G₁ G₂ →
      SourceOperatorInputCorrespondence H₁ H₂ →
      SourceOperatorInputCorrespondence (.intersection G₁ H₁) (.intersection G₂ H₂)
  | bottom :
      SourceOperatorInputCorrespondence .bottom .bottom
  | negClass :
      SourceOperatorInputCorrespondence (.negClass C) (.negClass C)

theorem sourceOperatorInputCorrespondence_refl
    (G : GTy) :
    SourceOperatorInputCorrespondence G G := by
  induction G with
  | any =>
      exact .any
  | class_ =>
      exact .class_
  | callable _ _ ihP ihR =>
      exact .callable ihP ihR
  | union _ _ ihG ihH =>
      exact .union ihG ihH
  | intersection _ _ ihG ihH =>
      exact .intersection ihG ihH
  | bottom =>
      exact .bottom
  | negClass =>
      exact .negClass

inductive SourceOperatorInputAlignment : GTy → GTy → Prop where
  | any :
      SourceOperatorInputAlignment .any .any
  | toAny :
      SourceOperatorInputAlignment G .any
  | class_ :
      SourceOperatorInputAlignment (.class_ C) (.class_ C)
  | callable :
      SourceOperatorInputAlignment P₁ P₂ →
      SourceOperatorInputAlignment R₁ R₂ →
      SourceOperatorInputAlignment (.callable P₁ R₁) (.callable P₂ R₂)
  | union :
      SourceOperatorInputAlignment G₁ G₂ →
      SourceOperatorInputAlignment H₁ H₂ →
      SourceOperatorInputAlignment (.union G₁ H₁) (.union G₂ H₂)
  | intersection :
      SourceOperatorInputAlignment G₁ G₂ →
      SourceOperatorInputAlignment H₁ H₂ →
      SourceOperatorInputAlignment (.intersection G₁ H₁) (.intersection G₂ H₂)
  | bottom :
      SourceOperatorInputAlignment .bottom .bottom
  | negClass :
      SourceOperatorInputAlignment (.negClass C) (.negClass C)

theorem sourceOperatorInputAlignment_refl
    (G : GTy) :
    SourceOperatorInputAlignment G G := by
  induction G with
  | any =>
      exact .any
  | class_ =>
      exact .class_
  | callable _ _ ihP ihR =>
      exact .callable ihP ihR
  | union _ _ ihG ihH =>
      exact .union ihG ihH
  | intersection _ _ ihG ihH =>
      exact .intersection ihG ihH
  | bottom =>
      exact .bottom
  | negClass =>
      exact .negClass

theorem sourceOperatorInputAlignment_of_correspondence
    (h : SourceOperatorInputCorrespondence G₁ G₂) :
    SourceOperatorInputAlignment G₁ G₂ := by
  induction h with
  | any =>
      exact .any
  | class_ =>
      exact .class_
  | callable _ _ ihP ihR =>
      exact .callable ihP ihR
  | union _ _ ihG ihH =>
      exact .union ihG ihH
  | intersection _ _ ihG ihH =>
      exact .intersection ihG ihH
  | bottom =>
      exact .bottom
  | negClass =>
      exact .negClass

private theorem sourceOperatorInputAlignment_of_structuralTargetPrecision
    (h : StructuralTargetPrecision G₁ G₂) :
    SourceOperatorInputAlignment G₁ G₂ := by
  induction h with
  | refl =>
      exact sourceOperatorInputAlignment_refl _
  | toAny =>
      exact .toAny
  | callable _ _ ihP ihR =>
      exact .callable ihP ihR
  | union _ _ ihG ihH =>
      exact .union ihG ihH
  | intersection _ _ ihG ihH =>
      exact .intersection ihG ihH

theorem sourceOperatorInputAlignment_of_annotationTargetPrecision
    (h : AnnotationTargetPrecision G₁ G₂) :
    SourceOperatorInputAlignment G₁ G₂ :=
  sourceOperatorInputAlignment_of_structuralTargetPrecision
    (structuralTargetPrecision_of_annotationTargetPrecision h)


/-! ## Call Typing -/

def calleeSummarySrc (gct : GClassTable) : GTy → CallableSummary
  | .any => .tainted
  | .class_ _ => .empty
  | .callable P R => .leaf { paramTy := P, returnTy := R }
  | .union G H => .union (calleeSummarySrc gct G) (calleeSummarySrc gct H)
  | .intersection G H => .intersection (calleeSummarySrc gct G) (calleeSummarySrc gct H)
  | .bottom => .empty
  | .negClass _ => .empty

def mergeCallUnionResult : Option GTy → Option GTy → Option GTy
  | some left, some right => some (.union left right)
  | _, _ => none

def mergeCallIntersectionResult : Option GTy → Option GTy → Option GTy
  | none, none => none
  | some result, none => some result
  | none, some result => some result
  | some _, some _ => some .any

private theorem callableSummaryOk_leaf_inv
    (hsum : CallableSummaryOk gct (.leaf f)) :
    CallableFacetOk gct f := by
  cases hsum with
  | leaf hfacet =>
      exact hfacet

private theorem callableSummaryOk_union_inv
    (hsum : CallableSummaryOk gct (.union s t)) :
    CallableSummaryOk gct s ∧ CallableSummaryOk gct t := by
  cases hsum with
  | union hs ht =>
      exact ⟨hs, ht⟩

private theorem callableSummaryOk_intersection_inv
    (hsum : CallableSummaryOk gct (.intersection s t)) :
    CallableSummaryOk gct s ∧ CallableSummaryOk gct t := by
  cases hsum with
  | intersection hs ht =>
      exact ⟨hs, ht⟩

def callSourceTy? (gct : GClassTable) {s : CallableSummary} {argTy : GTy}
    (hwfct : WellFormedGClassTableCore gct)
    (hsum : CallableSummaryOk gct s)
    (hwfArg : WellFormedGTy gct argTy) : Option GTy :=
  match s with
  | .tainted =>
      some .any
  | .empty =>
      none
  | .leaf f =>
      have hfacet : CallableFacetOk gct f := callableSummaryOk_leaf_inv hsum
      have hwfParam : WellFormedGTy gct f.paramTy := hfacet.2.1
      haveI : Decidable (AssignableTo gct argTy f.paramTy) :=
        assignableTo_decidable hwfct hwfArg hwfParam
      if AssignableTo gct argTy f.paramTy then some f.returnTy else none
  | .union s₁ s₂ =>
      let hchildren := callableSummaryOk_union_inv hsum
      mergeCallUnionResult
        (callSourceTy? (gct := gct) (s := s₁) (argTy := argTy) hwfct hchildren.1 hwfArg)
        (callSourceTy? (gct := gct) (s := s₂) (argTy := argTy) hwfct hchildren.2 hwfArg)
  | .intersection s₁ s₂ =>
      let hchildren := callableSummaryOk_intersection_inv hsum
      mergeCallIntersectionResult
        (callSourceTy? (gct := gct) (s := s₁) (argTy := argTy) hwfct hchildren.1 hwfArg)
        (callSourceTy? (gct := gct) (s := s₂) (argTy := argTy) hwfct hchildren.2 hwfArg)

inductive CallResultWitness (gct : GClassTable) (argTy : GTy) :
    CallableSummary → Option GTy → Prop where
  | tainted :
      CallResultWitness gct argTy .tainted (some .any)
  | empty :
      CallResultWitness gct argTy .empty none
  | leaf_hit
      (happ : AssignableTo gct argTy f.paramTy) :
      CallResultWitness gct argTy (.leaf f) (some f.returnTy)
  | leaf_miss
      (hmiss : ¬ AssignableTo gct argTy f.paramTy) :
      CallResultWitness gct argTy (.leaf f) none
  | union_some
      (hleft : CallResultWitness gct argTy s (some left))
      (hright : CallResultWitness gct argTy t (some right)) :
      CallResultWitness gct argTy (.union s t) (some (.union left right))
  | union_none_left
      (hleft : CallResultWitness gct argTy s none)
      (hright : CallResultWitness gct argTy t resultT) :
      CallResultWitness gct argTy (.union s t) none
  | union_none_right
      (hleft : CallResultWitness gct argTy s (some left))
      (hright : CallResultWitness gct argTy t none) :
      CallResultWitness gct argTy (.union s t) none
  | inter_none
      (hleft : CallResultWitness gct argTy s none)
      (hright : CallResultWitness gct argTy t none) :
      CallResultWitness gct argTy (.intersection s t) none
  | inter_left
      (hleft : CallResultWitness gct argTy s (some result))
      (hright : CallResultWitness gct argTy t none) :
      CallResultWitness gct argTy (.intersection s t) (some result)
  | inter_right
      (hleft : CallResultWitness gct argTy s none)
      (hright : CallResultWitness gct argTy t (some result)) :
      CallResultWitness gct argTy (.intersection s t) (some result)
  | inter_both
      (hleft : CallResultWitness gct argTy s (some left))
      (hright : CallResultWitness gct argTy t (some right)) :
      CallResultWitness gct argTy (.intersection s t) (some .any)

theorem callSourceTy?_of_witness
    {hwfct : WellFormedGClassTableCore gct}
    {hsum : CallableSummaryOk gct s}
    {hwfArg : WellFormedGTy gct argTy}
    (hw : CallResultWitness gct argTy s result) :
    callSourceTy? (gct := gct) (s := s) (argTy := argTy) hwfct hsum hwfArg = result := by
  induction hw with
  | tainted =>
      simp [callSourceTy?]
  | empty =>
      simp [callSourceTy?]
  | leaf_hit happ =>
      rename_i f
      have hfacet : CallableFacetOk gct f := callableSummaryOk_leaf_inv hsum
      have hwfParam : WellFormedGTy gct f.paramTy := hfacet.2.1
      haveI : Decidable (AssignableTo gct argTy f.paramTy) :=
        assignableTo_decidable hwfct hwfArg hwfParam
      simp [callSourceTy?, happ]
  | leaf_miss hmiss =>
      rename_i f
      have hfacet : CallableFacetOk gct f := callableSummaryOk_leaf_inv hsum
      have hwfParam : WellFormedGTy gct f.paramTy := hfacet.2.1
      haveI : Decidable (AssignableTo gct argTy f.paramTy) :=
        assignableTo_decidable hwfct hwfArg hwfParam
      simp [callSourceTy?, hmiss]
  | union_some _ _ ihLeft ihRight =>
      simp [callSourceTy?, mergeCallUnionResult,
        ihLeft (hsum := (callableSummaryOk_union_inv hsum).1),
        ihRight (hsum := (callableSummaryOk_union_inv hsum).2)]
  | union_none_left _ _ ihLeft ihRight =>
      simp [callSourceTy?, mergeCallUnionResult,
        ihLeft (hsum := (callableSummaryOk_union_inv hsum).1),
        ihRight (hsum := (callableSummaryOk_union_inv hsum).2)]
  | union_none_right _ _ ihLeft ihRight =>
      simp [callSourceTy?, mergeCallUnionResult,
        ihLeft (hsum := (callableSummaryOk_union_inv hsum).1),
        ihRight (hsum := (callableSummaryOk_union_inv hsum).2)]
  | inter_none _ _ ihLeft ihRight =>
      simp [callSourceTy?, mergeCallIntersectionResult,
        ihLeft (hsum := (callableSummaryOk_intersection_inv hsum).1),
        ihRight (hsum := (callableSummaryOk_intersection_inv hsum).2)]
  | inter_left _ _ ihLeft ihRight =>
      simp [callSourceTy?, mergeCallIntersectionResult,
        ihLeft (hsum := (callableSummaryOk_intersection_inv hsum).1),
        ihRight (hsum := (callableSummaryOk_intersection_inv hsum).2)]
  | inter_right _ _ ihLeft ihRight =>
      simp [callSourceTy?, mergeCallIntersectionResult,
        ihLeft (hsum := (callableSummaryOk_intersection_inv hsum).1),
        ihRight (hsum := (callableSummaryOk_intersection_inv hsum).2)]
  | inter_both _ _ ihLeft ihRight =>
      simp [callSourceTy?, mergeCallIntersectionResult,
        ihLeft (hsum := (callableSummaryOk_intersection_inv hsum).1),
        ihRight (hsum := (callableSummaryOk_intersection_inv hsum).2)]

theorem callSourceTy?_witness_of
    {hwfct : WellFormedGClassTableCore gct}
    {hsum : CallableSummaryOk gct s}
    {hwfArg : WellFormedGTy gct argTy}
    (hcall : callSourceTy? (gct := gct) (s := s) (argTy := argTy) hwfct hsum hwfArg = result) :
    CallResultWitness gct argTy s result := by
  induction s generalizing result with
  | tainted =>
      cases hsum
      simp [callSourceTy?] at hcall
      cases hcall
      exact .tainted
  | empty =>
      cases hsum
      simp [callSourceTy?] at hcall
      cases hcall
      exact .empty
  | leaf f =>
      cases hsum with
      | leaf hfacet =>
          have hwfParam : WellFormedGTy gct f.paramTy := hfacet.2.1
          haveI : Decidable (AssignableTo gct argTy f.paramTy) :=
            assignableTo_decidable hwfct hwfArg hwfParam
          by_cases happ : AssignableTo gct argTy f.paramTy
          · simp [callSourceTy?, happ] at hcall
            cases hcall
            exact .leaf_hit happ
          · simp [callSourceTy?, happ] at hcall
            cases hcall
            exact .leaf_miss happ
  | union s₁ s₂ ih₁ ih₂ =>
      cases hsum with
      | union hsum₁ hsum₂ =>
          cases hleft :
              callSourceTy? (gct := gct) (s := s₁) (argTy := argTy) hwfct hsum₁ hwfArg with
          | none =>
              have hwLeft : CallResultWitness gct argTy s₁ none :=
                ih₁ (hsum := hsum₁) hleft
              cases hright :
                  callSourceTy? (gct := gct) (s := s₂) (argTy := argTy) hwfct hsum₂ hwfArg with
              | none =>
                  have hwRight : CallResultWitness gct argTy s₂ none :=
                    ih₂ (hsum := hsum₂) hright
                  simp [callSourceTy?, mergeCallUnionResult, hleft, hright] at hcall
                  cases hcall
                  exact .union_none_left hwLeft hwRight
              | some right =>
                  have hwRight : CallResultWitness gct argTy s₂ (some right) :=
                    ih₂ (hsum := hsum₂) hright
                  simp [callSourceTy?, mergeCallUnionResult, hleft, hright] at hcall
                  cases hcall
                  exact .union_none_left hwLeft hwRight
          | some left =>
              have hwLeft : CallResultWitness gct argTy s₁ (some left) :=
                ih₁ (hsum := hsum₁) hleft
              cases hright :
                  callSourceTy? (gct := gct) (s := s₂) (argTy := argTy) hwfct hsum₂ hwfArg with
              | none =>
                  have hwRight : CallResultWitness gct argTy s₂ none :=
                    ih₂ (hsum := hsum₂) hright
                  simp [callSourceTy?, mergeCallUnionResult, hleft, hright] at hcall
                  cases hcall
                  exact .union_none_right hwLeft hwRight
              | some right =>
                  have hwRight : CallResultWitness gct argTy s₂ (some right) :=
                    ih₂ (hsum := hsum₂) hright
                  simp [callSourceTy?, mergeCallUnionResult, hleft, hright] at hcall
                  cases hcall
                  exact .union_some hwLeft hwRight
  | intersection s₁ s₂ ih₁ ih₂ =>
      cases hsum with
      | intersection hsum₁ hsum₂ =>
          cases hleft :
              callSourceTy? (gct := gct) (s := s₁) (argTy := argTy) hwfct hsum₁ hwfArg with
          | none =>
              have hwLeft : CallResultWitness gct argTy s₁ none :=
                ih₁ (hsum := hsum₁) hleft
              cases hright :
                  callSourceTy? (gct := gct) (s := s₂) (argTy := argTy) hwfct hsum₂ hwfArg with
              | none =>
                  have hwRight : CallResultWitness gct argTy s₂ none :=
                    ih₂ (hsum := hsum₂) hright
                  simp [callSourceTy?, mergeCallIntersectionResult, hleft, hright] at hcall
                  cases hcall
                  exact .inter_none hwLeft hwRight
              | some right =>
                  have hwRight : CallResultWitness gct argTy s₂ (some right) :=
                    ih₂ (hsum := hsum₂) hright
                  simp [callSourceTy?, mergeCallIntersectionResult, hleft, hright] at hcall
                  cases hcall
                  exact .inter_right hwLeft hwRight
          | some left =>
              have hwLeft : CallResultWitness gct argTy s₁ (some left) :=
                ih₁ (hsum := hsum₁) hleft
              cases hright :
                  callSourceTy? (gct := gct) (s := s₂) (argTy := argTy) hwfct hsum₂ hwfArg with
              | none =>
                  have hwRight : CallResultWitness gct argTy s₂ none :=
                    ih₂ (hsum := hsum₂) hright
                  simp [callSourceTy?, mergeCallIntersectionResult, hleft, hright] at hcall
                  cases hcall
                  exact .inter_left hwLeft hwRight
              | some right =>
                  have hwRight : CallResultWitness gct argTy s₂ (some right) :=
                    ih₂ (hsum := hsum₂) hright
                  simp [callSourceTy?, mergeCallIntersectionResult, hleft, hright] at hcall
                  cases hcall
                  exact .inter_both hwLeft hwRight

theorem callSourceTy?_witness_result_eq
    {hwfct : WellFormedGClassTableCore gct}
    {hsum : CallableSummaryOk gct s}
    {hwfArg : WellFormedGTy gct argTy}
    (hw₁ : CallResultWitness gct argTy s result₁)
    (hw₂ : CallResultWitness gct argTy s result₂) :
    result₁ = result₂ := by
  rw [← callSourceTy?_of_witness (hwfct := hwfct) (hsum := hsum) (hwfArg := hwfArg) hw₁]
  rw [← callSourceTy?_of_witness (hwfct := hwfct) (hsum := hsum) (hwfArg := hwfArg) hw₂]

theorem callableSummaryOk_calleeSummarySrc
    (hsrc : SourceCallableTy gct G)
    (hwf : WellFormedGTy gct G) :
    CallableSummaryOk gct (calleeSummarySrc gct G) := by
  induction hsrc with
  | any =>
      cases hwf
      exact .tainted
  | class_ =>
      cases hwf
      exact .empty
  | callable hP hR ihP =>
      cases hwf with
      | callable hwfP hwfR =>
          exact
            .leaf
              ⟨hP, hwfP, runtimePublicAnnotation_to_sourceCallableTy _ hR, hwfR⟩
  | union hG hH ihG ihH =>
      cases hwf with
      | union hwfG hwfH =>
          exact .union (ihG hwfG) (ihH hwfH)
  | intersection hG hH ihG ihH =>
      cases hwf with
      | intersection hwfG hwfH =>
          exact .intersection (ihG hwfG) (ihH hwfH)
  | bottom =>
      cases hwf
      exact .empty
  | negClass =>
      cases hwf
      exact .empty

private theorem calleeSummarySrc_transport :
    calleeSummarySrc gct₁ G = calleeSummarySrc gct₂ G := by
  induction G <;> simp [calleeSummarySrc, *]

private theorem callResultWitness_transport
    (hct : ClassTableAnnotationPrecision gct₁ gct₂)
    (hw : CallResultWitness gct₁ argTy s result) :
    CallResultWitness gct₂ argTy s result := by
  induction hw with
  | tainted =>
      exact .tainted
  | empty =>
      exact .empty
  | leaf_hit happ =>
      exact .leaf_hit ((assignableTo_transport hct).mp happ)
  | leaf_miss hmiss =>
      exact
        .leaf_miss (by
          intro happ₂
          exact hmiss ((assignableTo_transport hct).mpr happ₂))
  | union_some _ _ ihLeft ihRight =>
      exact .union_some ihLeft ihRight
  | union_none_left _ _ ihLeft ihRight =>
      exact .union_none_left ihLeft ihRight
  | union_none_right _ _ ihLeft ihRight =>
      exact .union_none_right ihLeft ihRight
  | inter_none _ _ ihLeft ihRight =>
      exact .inter_none ihLeft ihRight
  | inter_left _ _ ihLeft ihRight =>
      exact .inter_left ihLeft ihRight
  | inter_right _ _ ihLeft ihRight =>
      exact .inter_right ihLeft ihRight
  | inter_both _ _ ihLeft ihRight =>
      exact .inter_both ihLeft ihRight

private theorem callResultWitness_callable_and_wf
    (hsum : CallableSummaryOk gct s)
    (hw : CallResultWitness gct argTy s (some R)) :
    SourceCallableTy gct R ∧ WellFormedGTy gct R := by
  cases hw with
  | tainted =>
      exact ⟨.any, .any⟩
  | leaf_hit happ =>
      rename_i f
      have hfacet : CallableFacetOk gct f := callableSummaryOk_leaf_inv hsum
      rcases hfacet with ⟨_, _, hret, hwfRet⟩
      exact ⟨hret, hwfRet⟩
  | union_some hleft hright =>
      have hchildren := callableSummaryOk_union_inv hsum
      rcases callResultWitness_callable_and_wf hchildren.1 hleft with ⟨hsrcLeft, hwfLeft⟩
      rcases callResultWitness_callable_and_wf hchildren.2 hright with ⟨hsrcRight, hwfRight⟩
      exact ⟨.union hsrcLeft hsrcRight, .union hwfLeft hwfRight⟩
  | inter_left hleft _ =>
      have hchildren := callableSummaryOk_intersection_inv hsum
      exact callResultWitness_callable_and_wf hchildren.1 hleft
  | inter_right _ hright =>
      have hchildren := callableSummaryOk_intersection_inv hsum
      exact callResultWitness_callable_and_wf hchildren.2 hright
  | inter_both _ _ =>
      exact ⟨.any, .any⟩

theorem callSourceTy?_callable_and_wf
    (hwfct : WellFormedGClassTableCore gct)
    (hsum : CallableSummaryOk gct s)
    (hwfArg : WellFormedGTy gct argTy)
    (hcall : callSourceTy? (gct := gct) (s := s) (argTy := argTy) hwfct hsum hwfArg = some R) :
    SourceCallableTy gct R ∧ WellFormedGTy gct R := by
  exact callResultWitness_callable_and_wf hsum (callSourceTy?_witness_of hcall)

theorem callSourceTy?_sourceCallable
    (hwfct : WellFormedGClassTableCore gct)
    (hsum : CallableSummaryOk gct s)
    (hwfArg : WellFormedGTy gct argTy)
    (hcall : callSourceTy? (gct := gct) (s := s) (argTy := argTy) hwfct hsum hwfArg = some R) :
    SourceCallableTy gct R :=
  (callSourceTy?_callable_and_wf hwfct hsum hwfArg hcall).1

theorem callSourceTy?_wellFormed
    (hwfct : WellFormedGClassTableCore gct)
    (hsum : CallableSummaryOk gct s)
    (hwfArg : WellFormedGTy gct argTy)
    (hcall : callSourceTy? (gct := gct) (s := s) (argTy := argTy) hwfct hsum hwfArg = some R) :
    WellFormedGTy gct R :=
  (callSourceTy?_callable_and_wf hwfct hsum hwfArg hcall).2

theorem callSourceTy?_transport
    (hct : ClassTableAnnotationPrecision gct₁ gct₂)
    (hwfct₁ : WellFormedGClassTableCore gct₁)
    (hwfct₂ : WellFormedGClassTableCore gct₂)
    (hsum₁ : CallableSummaryOk gct₁ s)
    (hsum₂ : CallableSummaryOk gct₂ s)
    (hwfArg₁ : WellFormedGTy gct₁ argTy)
    (hwfArg₂ : WellFormedGTy gct₂ argTy) :
    callSourceTy? (gct := gct₁) (s := s) (argTy := argTy) hwfct₁ hsum₁ hwfArg₁ =
      callSourceTy? (gct := gct₂) (s := s) (argTy := argTy) hwfct₂ hsum₂ hwfArg₂ := by
  let result :=
    callSourceTy? (gct := gct₁) (s := s) (argTy := argTy) hwfct₁ hsum₁ hwfArg₁
  have hw₁ : CallResultWitness gct₁ argTy s result := by
    exact callSourceTy?_witness_of (result := result) rfl
  have hw₂ : CallResultWitness gct₂ argTy s result :=
    callResultWitness_transport hct hw₁
  have h₂ :
      callSourceTy? (gct := gct₂) (s := s) (argTy := argTy) hwfct₂ hsum₂ hwfArg₂ = result :=
    callSourceTy?_of_witness (hwfct := hwfct₂) (hsum := hsum₂) (hwfArg := hwfArg₂) hw₂
  exact h₂.symm
