import FwPython.Common.Forall2
import FwPython.Gradual.TypeSystem.TargetAdmissibility
import FwPython.Gradual.TypeSystem.ClassTable.WellFormednessCore
import FwPython.Gradual.TypeSystem.Method.TypeFacts

open FwPython.Static.Subtyping

/-! # Source environments and type inference

Each source binding stores one gradual type.
The compiler selects types for runtime checks at each use of an expression.
The call checker selects a result type from the function and argument annotations. -/

/-! ## Source environment -/

/-- A variable name and its type in the source program. -/
structure SBinding where
  /-- The name used to look up the variable. -/
  name : Identifier
  /-- The source type assigned to the variable. -/
  sourceTy : GTy
  deriving DecidableEq

/-- Source bindings in lookup order; the first matching name controls each variable. -/
abbrev SBindingEnv := List SBinding

/-- Return the first source binding with the requested variable name. -/
def SBindingEnv.lookupBinding : SBindingEnv → Identifier → Option SBinding
  | [], _ => none
  | b :: rest, x => if b.name = x then some b else lookupBinding rest x

/-- Change the type of the first matching binding while preserving names and order.
A variable with no binding leaves the environment unchanged. -/
def SBindingEnv.updateSource : SBindingEnv → Identifier → GTy → SBindingEnv
  | [], _, _ => []
  | b :: rest, x, S =>
    if b.name = x then { b with sourceTy := S } :: rest
    else b :: updateSource rest x S

/-! ## Environment invariants -/

/-- A source binding and its checked binding name the same variable.
The checked type includes the source type's upper bound under the supplied hierarchy. -/
structure ElabBindingRel (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct))
    (b : SBinding) (p : Identifier × GTy) : Prop where
  /-- Both bindings have the same variable lookup name. -/
  name_eq : b.name = p.1
  /-- The checked binding's type can be represented by runtime checks. -/
  checked_target : CheckedTargetTy gct p.2
  /-- Every class name in the checked type exists and has an MRO. -/
  checked_wf : WellFormedGTy gct p.2
  /-- The source upper bound is below the checked upper bound.
  The subtype proof certifies known source names; the table's MRO evidence
  then establishes validity of the source annotation. -/
  source_sub_checked : GradualSubtype gct structural b.sourceTy p.2

abbrev ElabEnvOk (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (Γ : SBindingEnv) (Δ : GTyEnv) :=
  Forall₂ (ElabBindingRel gct structural) Γ Δ

section

/-! ## Environment lemmas -/

variable {gct : GClassTable} {structural : WellFormedClassHierarchy (eraseClassTable gct)}

theorem elabEnvOk_lookup
    (hok : ElabEnvOk gct structural Γ Δ)
    (hlook : Γ.lookupBinding x = some b) :
    ∃ T,
      Δ.lookup x = some T ∧
      CheckedTargetTy gct T ∧
      WellFormedGTy gct T ∧
      GradualSubtype gct structural b.sourceTy T := by
  induction hok generalizing x b with
  | nil =>
    simp [SBindingEnv.lookupBinding] at hlook
  | @cons b₀ p₀ Γ Δ hrel _ ih =>
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

theorem elabEnvOk_updateBoth
    (hok : ElabEnvOk gct structural Γ Δ)
    (hlookΓ : Γ.lookupBinding x = some b)
    (hlookΔ : Δ.lookup x = some T)
    (hchecked : CheckedTargetTy gct newChecked)
    (hwf : WellFormedGTy gct newChecked)
    (hsub : GradualSubtype gct structural newSrc newChecked) :
    ElabEnvOk gct structural (Γ.updateSource x newSrc) (Δ.update x newChecked) := by
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
          ElabBindingRel gct structural { b₀ with sourceTy := newSrc } (p₀.1, newChecked) := {
        name_eq := by simpa using hrel.name_eq
        checked_target := hchecked
        checked_wf := hwf
        source_sub_checked := hsub
      }
      have hok' :
          ElabEnvOk gct structural ({ b₀ with sourceTy := newSrc } :: Γ) ((p₀.1, newChecked) :: Δ) :=
        .cons hrel' hrest
      simpa [SBindingEnv.updateSource, GTyEnv.update, NamedEnv.update, hname, hp] using hok'
    · simp [SBindingEnv.lookupBinding, hname] at hlookΓ
      have hp : p₀.1 ≠ x := by
        intro hEq
        exact hname (hrel.name_eq.trans hEq)
      have hok' :
          ElabEnvOk gct structural (b₀ :: SBindingEnv.updateSource Γ x newSrc)
            (p₀ :: GTyEnv.update Δ x newChecked) :=
        .cons hrel (ih hlookΓ (by simpa [NamedEnv.lookup, hp] using hlookΔ))
      simpa [SBindingEnv.updateSource, GTyEnv.update, NamedEnv.update, hname, hp] using hok'

/-! ## Method lookup -/

end

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

/-- Attribute inference returns a type whose classes and MROs are valid. -/
theorem attrSourceTy?_wellFormed
    (hwfct : WellFormedGClassTableCore gct)
    (hattr : attrSourceTy? gct G attr = some R) :
    WellFormedGTy gct R := by
  have hw := attrSourceTy?_witness_of hattr
  cases hw with
  | any => exact .any
  | bottom => exact .bottom
  | class_some hlookup | callable_some hlookup =>
      have methodValid := wellFormedGTy_of_findGMethodType hwfct (lookupMethodTy?_find hlookup)
      exact .callable methodValid.1 methodValid.2
  | union_some hleft hright =>
      exact .union
        (attrSourceTy?_wellFormed hwfct (attrSourceTy?_of_witness hleft))
        (attrSourceTy?_wellFormed hwfct (attrSourceTy?_of_witness hright))
  | inter_left hleft _ =>
      exact attrSourceTy?_wellFormed hwfct (attrSourceTy?_of_witness hleft)
  | inter_right _ hright =>
      exact attrSourceTy?_wellFormed hwfct (attrSourceTy?_of_witness hright)
  | inter_both hleft hright =>
      exact .intersection
        (attrSourceTy?_wellFormed hwfct (attrSourceTy?_of_witness hleft))
        (attrSourceTy?_wellFormed hwfct (attrSourceTy?_of_witness hright))

/-! ## Call summaries -/

/-- An input and result pair used by call selection.
Pairs represent declared requirements, their combinations, or unknown and empty types. -/
private structure CallableFacet (gct : GClassTable) where
  /-- The required input annotation and proof that its classes and MROs are valid. -/
  paramTy : WellFormedGradualType gct
  /-- The required result annotation and proof that its classes and MROs are valid. -/
  returnTy : WellFormedGradualType gct
  deriving DecidableEq

/-- The input and result requirements found in a source function type. -/
private inductive CallableSummary (gct : GClassTable) where
  /-- The source type supplies no function input or result requirements. -/
  | empty
  /-- The source type permits no callable value. -/
  | bottom
  /-- One input and result type pair. -/
  | leaf : CallableFacet gct -> CallableSummary gct
  /-- The function can have either type. Both alternatives must permit the call. -/
  | union : CallableSummary gct -> CallableSummary gct -> CallableSummary gct
  /-- The same function satisfies both sets of type requirements. -/
  | intersection : CallableSummary gct -> CallableSummary gct -> CallableSummary gct

/-! ## Call Typing -/

/-- Extract the input and result requirements that can apply to a callable value.
A source type can combine function requirements with class types and exclusions,
called class literals. The summary tests each name against BoundMethod's MRO.
Outside that MRO, sealing makes BoundMethod & C bottom; inside it, inheritance
and class contradiction make BoundMethod & negClass C bottom. These literals
rule out every callable value, so their summary is `.bottom`.

For the remaining literals, inheritance gives BoundMethod & C ≈ BoundMethod when
C is in its MRO. Sealing and the class complement equations give
BoundMethod & negClass C ≈ BoundMethod when C is outside its MRO. These literals
add no parameter or result annotation, so their summary is `.empty`. Function
types and `any` supply those requirements. Object also admits ordinary objects,
so `callSourceTy?` checks acceptance using the full callee type. -/
private def calleeSummarySrc (gct : GClassTable) (hwfct : WellFormedGClassTableCore gct) :
    (type : GTy) → WellFormedGTy gct type → CallableSummary gct
  | .any, _ => .leaf ⟨.any, .any⟩
  | .class_ name, _ =>
      if name ∈ hwfct.raw.boundMethodExists.mro then .empty else .bottom
  | .callable P R, valid =>
      .leaf ⟨⟨P, by cases valid with | callable input _ => exact input⟩,
        ⟨R, by cases valid with | callable _ result => exact result⟩⟩
  | .union G H, valid =>
      let leftValid : WellFormedGTy gct G := by cases valid with | union left _ => exact left
      let rightValid : WellFormedGTy gct H := by cases valid with | union _ right => exact right
      match calleeSummarySrc gct hwfct G leftValid, calleeSummarySrc gct hwfct H rightValid with
      | .bottom, other => other
      | other, .bottom => other
      | left, right => .union left right
  | .intersection G H, valid =>
      let leftValid : WellFormedGTy gct G := by cases valid with | intersection left _ => exact left
      let rightValid : WellFormedGTy gct H := by cases valid with | intersection _ right => exact right
      match calleeSummarySrc gct hwfct G leftValid, calleeSummarySrc gct hwfct H rightValid with
      | .bottom, _ | _, .bottom => .bottom
      | left, right => .intersection left right
  | .bottom, _ => .bottom
  | .negClass name, _ =>
      if name ∈ hwfct.raw.boundMethodExists.mro then .bottom else .empty

/-- Apply a union or intersection without copying exactly equal operands. -/
private def combineCallTypes (combine : WellFormedGradualType gct → WellFormedGradualType gct → WellFormedGradualType gct)
    (left right : WellFormedGradualType gct) : WellFormedGradualType gct :=
  if left = right then left else combine left right

/-- List the function's input and result requirements.
An intersection can accept an argument through several requirements together.
Include the individual requirements and their nonempty combinations.
If only one input overlaps the argument upper bound, use that pair directly.
If neither overlaps, retain the right pair; its empty overlap adds no reachable result.
A union can select either function, so each pair must cover both alternatives.
An unknown callee part gives `any -> any`; it can add a result restriction.
A summary with no callable values gives `any -> bottom`. -/
private def callFacetCandidates (hwfct : WellFormedGClassTableCore gct)
    (argument : WellFormedType ((eraseClassTable gct).map ClassDecl.name))
    (s : CallableSummary gct) : List (CallableFacet gct) :=
  match s with
  | .empty => []
  | .bottom => [⟨.any, .bottom⟩]
  | .leaf f => [f]
  | .union left right =>
      let leftCandidates := callFacetCandidates hwfct argument left
      let rightCandidates := callFacetCandidates hwfct argument right
      (leftCandidates.flatMap (fun l => rightCandidates.map (fun r => {
        paramTy := combineCallTypes WellFormedGradualType.intersection l.paramTy r.paramTy,
        returnTy := combineCallTypes WellFormedGradualType.union l.returnTy r.returnTy }))).eraseDups
  | .intersection left right =>
      let leftCandidates := callFacetCandidates hwfct argument left
      let rightCandidates := callFacetCandidates hwfct argument right
      (leftCandidates ++ rightCandidates ++
        leftCandidates.flatMap (fun l => rightCandidates.map (combineIntersection l))).eraseDups
where
  /-- Combine two input requirements that overlap the argument upper bound.
  If only one input overlaps, use its pair directly.
  If neither overlaps, retain the right pair; no argument value can select it. -/
  combineIntersection (left right : CallableFacet gct) : CallableFacet gct :=
    let leftInput := WellFormedType.intersection argument
      (upperBoundType hwfct.toWellFormedClassHierarchy left.paramTy.wellFormed)
    let rightInput := WellFormedType.intersection argument
      (upperBoundType hwfct.toWellFormedClassHierarchy right.paramTy.wellFormed)
    haveI : Decidable (IsSubtype hwfct.toWellFormedClassHierarchy leftInput.raw .bottom) :=
      WellFormedType.subtypeDecidable hwfct.toWellFormedClassHierarchy leftInput .bottom
    haveI : Decidable (IsSubtype hwfct.toWellFormedClassHierarchy rightInput.raw .bottom) :=
      WellFormedType.subtypeDecidable hwfct.toWellFormedClassHierarchy rightInput .bottom
    if IsSubtype hwfct.toWellFormedClassHierarchy leftInput.raw .bottom then right
    else if IsSubtype hwfct.toWellFormedClassHierarchy rightInput.raw .bottom then left
    else ⟨combineCallTypes WellFormedGradualType.union left.paramTy right.paramTy,
      combineCallTypes WellFormedGradualType.union left.returnTy right.returnTy⟩

/-- Detect an unknown type anywhere inside a function input.
Such unknown inputs can change which result requirements apply after materialization.
Bounds alone do not preserve that information. -/
private def GTy.hasUnknownFunctionInput : GTy → Bool
  | .callable parameter result => containsAny parameter || result.hasUnknownFunctionInput
  | .union left right | .intersection left right =>
      left.hasUnknownFunctionInput || right.hasUnknownFunctionInput
  | _ => false
where
  /-- Detect unknown type information in an input annotation. -/
  containsAny : GTy → Bool
    | .any => true
    | .callable left right | .union left right | .intersection left right =>
        containsAny left || containsAny right
    | _ => false

/-- Compare the bounds of valid gradual packages without checking their names again. -/
private def WellFormedGradualType.boundsSubtypeDecidable
    (hwfct : WellFormedGClassTableCore gct) (source target : WellFormedGradualType gct) :
    Decidable (BoundsSubtype gct hwfct.toWellFormedClassHierarchy source.raw target.raw) := by
  unfold BoundsSubtype
  let structural := hwfct.toWellFormedClassHierarchy
  exact @instDecidableAnd _ _
    (WellFormedType.subtypeDecidable structural
      (lowerBoundType structural source.wellFormed) (lowerBoundType structural target.wellFormed))
    (WellFormedType.subtypeDecidable structural
      (upperBoundType structural source.wellFormed) (upperBoundType structural target.wellFormed))

/-- Compare the bounds intervals of two valid gradual packages without checking their names again. -/
private def WellFormedGradualType.moreStaticDecidable
    (hwfct : WellFormedGClassTableCore gct) (source target : WellFormedGradualType gct) :
    Decidable (MoreStatic gct hwfct.toWellFormedClassHierarchy source.raw target.raw) := by
  unfold MoreStatic
  let structural := hwfct.toWellFormedClassHierarchy
  exact @instDecidableAnd _ _
    (WellFormedType.subtypeDecidable structural
      (lowerBoundType structural target.wellFormed) (lowerBoundType structural source.wellFormed))
    (WellFormedType.subtypeDecidable structural
      (upperBoundType structural source.wellFormed) (upperBoundType structural target.wellFormed))

/-- Intersect result requirements that apply to the same input.
Keep equal results unchanged.
Use bounds to omit a distinct part only when neither type has an unknown function input.
Otherwise retain both requirements, including their separate materializations. -/
private def mergeCallResults (hwfct : WellFormedGClassTableCore gct)
    (left right : WellFormedGradualType gct) : WellFormedGradualType gct :=
  if left = right then left
  else if left.raw.hasUnknownFunctionInput || right.raw.hasUnknownFunctionInput then .intersection left right
  else
    haveI := WellFormedGradualType.boundsSubtypeDecidable hwfct left right
    if BoundsSubtype gct hwfct.toWellFormedClassHierarchy left.raw right.raw then left
    else
      haveI := WellFormedGradualType.boundsSubtypeDecidable hwfct right left
      if BoundsSubtype gct hwfct.toWellFormedClassHierarchy right.raw left.raw then right
      else .intersection left right

/-- Fold results in list order, leaving an empty list without a selected result. -/
private def foldCallResults {α : Type} (combine : α → α → α) (results : List α) : Option α :=
  results.foldr (fun result retained =>
    some (match retained with
      | none => result
      | some other => combine result other)) none

/-- Decide whether another result covers this result's bounds interval.
Equal types need no approximation. For distinct types, both must have known function inputs.
Unknown function inputs can change which requirements apply after materialization. -/
private def callResultCoveredBy (hwfct : WellFormedGClassTableCore gct)
    (result other : WellFormedGradualType gct) : Bool :=
  result == other ||
    if result.raw.hasUnknownFunctionInput || other.raw.hasUnknownFunctionInput then false
    else
      haveI := WellFormedGradualType.moreStaticDecidable hwfct result other
      decide (MoreStatic gct hwfct.toWellFormedClassHierarchy result.raw other.raw)

/-- Combine results from different argument materializations.
Remove duplicate results and bounds intervals covered by another retained result.
Build one approximation from all retained results: their intersection, or an unknown
part limited to their union. Each retained result occurs twice in the final type.
A single retained result needs no approximation. -/
private def combineCallResults (hwfct : WellFormedGClassTableCore gct)
    (results : List (WellFormedGradualType gct)) : Option (WellFormedGradualType gct) :=
  match retain results with
  | [] => none
  | [result] => some result
  | retained =>
      (foldCallResults WellFormedGradualType.intersection retained).bind fun intersection =>
        (foldCallResults WellFormedGradualType.union retained).map fun union =>
          .union intersection (.intersection .any union)
where
  /-- Drop a result when another retained result has a strictly wider interval.
  Otherwise keep the first occurrence and remove equal or narrower retained intervals. -/
  retain : List (WellFormedGradualType gct) → List (WellFormedGradualType gct)
    | [] => []
    | result :: rest =>
        let retained := retain rest
        if retained.any (fun other => callResultCoveredBy hwfct result other &&
            !callResultCoveredBy hwfct other result) then retained
        else result :: retained.filter (fun other => !callResultCoveredBy hwfct other result)

/-- One call requirement and the static bounds used to select its applicable results. -/
private structure CallRequirementBounds (gct : GClassTable) where
  /-- The original source input and result annotations of the requirement. -/
  requirement : CallableFacet gct
  /-- A simplified static type equivalent to the requirement's parameter lower bound. -/
  parameterLowerBound : WellFormedType ((eraseClassTable gct).map ClassDecl.name)
  /-- The static argument type considered for this requirement's case.
  It is equivalent to `upperBound argTy & upperBound requirement.paramTy`. -/
  caseInput : WellFormedType ((eraseClassTable gct).map ClassDecl.name)

/-- Compute a call result from the function requirements in the callee summary.
Each occurrence of `any` in an annotation can be filled with a static type.
The selected result follows the call rule for that filling, not every result type
that static expression typing could assign to the call.

For each listed `P -> R`, keep the case if `lowerBound argTy <: upperBound P`.
Form `T = upperBound argTy & upperBound P`.
Filter the full candidate list to keep the selected requirement and those whose
input lower bounds include T. Keep each exactly equal result once, in its first
position. Fold these results in the original list order.
Equal filtered lists therefore give exactly equal results.
Remove duplicate pairs and results. Combine the distinct case results in one approximation.
The bounds used by these comparisons approximate the materializations. -/
private def callResult? (gct : GClassTable) (s : CallableSummary gct) (argTy : GTy)
    (hwfct : WellFormedGClassTableCore gct)
    (argumentValid : WellFormedGTy gct argTy) : Option (WellFormedGradualType gct) :=
  let argumentLowerBound := lowerBoundType hwfct.toWellFormedClassHierarchy argumentValid
  let requirements := callFacetCandidates hwfct (upperBoundType hwfct.toWellFormedClassHierarchy argumentValid) s
  let rows := requirements.map withInputBounds
  let parameterLowerBounds := (rows.map (·.parameterLowerBound)).eraseDups
  let caseInputs := (rows.map (·.caseInput)).eraseDups
  -- Each case input shares the list of parameter lower bounds that include it.
  let caseInputChecks := caseInputs.map fun caseInput =>
    (caseInput, parameterLowerBounds.filter fun parameterLowerBound =>
      haveI := WellFormedType.subtypeDecidable hwfct.toWellFormedClassHierarchy caseInput parameterLowerBound
      decide (IsSubtype hwfct.toWellFormedClassHierarchy caseInput.raw parameterLowerBound.raw))
  combineCallResults hwfct (rows.filterMap fun row =>
    let parameterUpperBound :=
      upperBoundType hwfct.toWellFormedClassHierarchy row.requirement.paramTy.wellFormed
    haveI := WellFormedType.subtypeDecidable
      hwfct.toWellFormedClassHierarchy argumentLowerBound parameterUpperBound
    if IsSubtype hwfct.toWellFormedClassHierarchy argumentLowerBound.raw parameterUpperBound.raw then
      -- Every case input occurs in caseInputChecks, so lookup supplies its cached tests.
      some (resultForInput row.requirement rows ((caseInputChecks.lookup row.caseInput).getD []))
    else none)
where
  /-- Compute the requirement's parameter lower bound and case input.
  Equivalent reductions let cases with equal static bounds share subtype tests. -/
  withInputBounds (requirement : CallableFacet gct) :
      CallRequirementBounds gct :=
    { requirement := requirement
      parameterLowerBound :=
        (simplifySubtypeOperand hwfct.toWellFormedClassHierarchy
          (lowerBoundType hwfct.toWellFormedClassHierarchy requirement.paramTy.wellFormed)).val
      caseInput := (simplifySubtypeOperand hwfct.toWellFormedClassHierarchy
        (.intersection (upperBoundType hwfct.toWellFormedClassHierarchy argumentValid)
          (upperBoundType hwfct.toWellFormedClassHierarchy requirement.paramTy.wellFormed))).val }

  /-- Select the requirements for one argument materialization in the full list's order.
  The caller supplies a selected requirement from this list and the parameter
  lower bounds that include its case input. Exact equality always keeps the
  selected requirement, even if its parameter lower bound does not include that input.
  Equal returned requirements impose the same constraint, so retain each once. -/
  resultForInput (requirement : CallableFacet gct) (rows : List (CallRequirementBounds gct))
      (includedParameterLowerBounds : List (WellFormedType ((eraseClassTable gct).map ClassDecl.name))) :
      WellFormedGradualType gct :=
    let applicable := rows.filter fun row =>
      row.requirement == requirement || row.parameterLowerBound ∈ includedParameterLowerBounds
    -- The selected requirement is in applicable, so this nonempty fold cannot use the fallback.
    (foldCallResults (mergeCallResults hwfct)
      (applicable.map (·.requirement.returnTy)).eraseDups).getD requirement.returnTy

/-- Decide call acceptance with `lowerBound calleeTy <: (lowerBound argTy -> Object)`.
The bounds approximate filling each `any` with a static type. Object leaves the
result unrestricted during acceptance, while checking the full callee accounts
for class types and exclusions even when no function requirement is explicitly declared.
This comparison also validates both annotations' names, so later checks can
reuse the resulting packages.

After acceptance, `callResult?` selects a result for later source checks. A
single `P -> R` keeps R, including its declared unknown parts; an empty callee
gives bottom because no value can reach the call. If selection finds no result,
the fallback is bottom for an empty argument upper bound and any otherwise.
The selected package proves result validity, and runtime checks test the actual
function, argument, and result. -/
def callSourceTy? (gct : GClassTable) (calleeTy argTy : GTy)
    (hwfct : WellFormedGClassTableCore gct) : Option GTy :=
  haveI := hwfct.subtypeDecidable (lowerBound calleeTy) (.callable (lowerBound argTy) staticTop)
  if accepted : IsSubtype hwfct.toWellFormedClassHierarchy (lowerBound calleeTy)
      (.callable (lowerBound argTy) staticTop) then
    let calleeValid := (wellFormedGTy_of_boundsNamesKnown hwfct.raw calleeTy).1 accepted.sourceWellFormed
    let argumentValid := (wellFormedGTy_of_boundsNamesKnown hwfct.raw argTy).1 accepted.targetWellFormed.callable_param
    haveI : Decidable (IsSubtype hwfct.toWellFormedClassHierarchy (upperBound argTy) .bottom) :=
      WellFormedType.subtypeDecidable hwfct.toWellFormedClassHierarchy
        (upperBoundType hwfct.toWellFormedClassHierarchy argumentValid) .bottom
    some ((callResult? gct (calleeSummarySrc gct hwfct calleeTy calleeValid) argTy hwfct argumentValid).getD
      (if IsSubtype hwfct.toWellFormedClassHierarchy (upperBound argTy) .bottom then .bottom else .any)).raw
  else none

/-- An accepted call returns a type whose classes and MROs are valid. -/
theorem callSourceTy?_wellFormed
    (hwfct : WellFormedGClassTableCore gct)
    (hcall : callSourceTy? gct calleeTy argTy hwfct = some R) :
    WellFormedGTy gct R := by
  unfold callSourceTy? at hcall
  split at hcall
  · exact (Option.some.inj hcall) ▸ WellFormedGradualType.wellFormed _
  · contradiction

/-- A call is accepted exactly when the callee lower bound accepts the argument lower bound.
This statement uses a fixed class table with valid class structure. -/
theorem callSourceTy?_accepts_iff
    (hwfct : WellFormedGClassTableCore gct) :
    (∃ R, callSourceTy? gct calleeTy argTy hwfct = some R) ↔
      IsSubtype hwfct.toWellFormedClassHierarchy (lowerBound calleeTy)
        (.callable (lowerBound argTy) staticTop) := by
  unfold callSourceTy?
  split
  · rename_i accepted
    constructor
    · exact fun _ => accepted
    · exact fun _ => ⟨_, rfl⟩
  · rename_i rejected
    exact ⟨fun ⟨_, impossible⟩ => False.elim (by contradiction),
      fun accepted => False.elim (rejected accepted)⟩

/-- Acceptance supplies valid class names for the argument annotation. -/
theorem callSourceTy?_argumentWellFormed (hwfct : WellFormedGClassTableCore gct)
    (accepted : callSourceTy? gct calleeTy argTy hwfct = some R) :
    WellFormedGTy gct argTy :=
  (wellFormedGTy_of_boundsNamesKnown hwfct.raw argTy).1
    ((callSourceTy?_accepts_iff hwfct).mp ⟨R, accepted⟩).targetWellFormed.callable_param

/-- Enlarging either annotation's bounds interval preserves call acceptance.
`MoreStatic` compares these intervals. It does not compare individual fillings
of unknown function inputs or the result types selected for later calls.
The theorem uses the same valid class table for both calls. -/
theorem callSourceTy?_moreStatic
    (hwfct : WellFormedGClassTableCore gct)
    (calleePrecision : MoreStatic gct hwfct.toWellFormedClassHierarchy calleeTy₁ calleeTy₂)
    (argumentPrecision : MoreStatic gct hwfct.toWellFormedClassHierarchy argTy₁ argTy₂)
    (accepted : callSourceTy? gct calleeTy₁ argTy₁ hwfct = some R₁) :
    ∃ R₂, callSourceTy? gct calleeTy₂ argTy₂ hwfct = some R₂ := by
  apply (callSourceTy?_accepts_iff hwfct).mpr
  exact .trans calleePrecision.1
    (.trans ((callSourceTy?_accepts_iff hwfct).mp ⟨R₁, accepted⟩)
      (.callable argumentPrecision.1 (.refl (WellFormedTy.object hwfct.toWellFormedClassHierarchy))))
