import FwPython.Gradual.MRO.Compute
import FwPython.Gradual.Contracts
import FwPython.Gradual.TypeSystem.CheckedTargetPrecision

/-! ## Admissible target fragment

The admissible target fragment restricts the gradual types that can appear
as machine-facing targets in the checked layer. This ensures preservation
only needs exact enforcement evidence, not generic witness subsumption. -/

/-- A gradual type is a *formula* when it is built entirely from
    class heads, unions, intersections, class negations, `any`, and
    `bottom`. No positive callable occurrence; gradual negation only
    appears at the class atom (`negClass`) by construction. -/
inductive FormulaGTy : GTy → Prop where
  | any : FormulaGTy .any
  | class_ : FormulaGTy (.class_ cname)
  | union : FormulaGTy F → FormulaGTy G → FormulaGTy (.union F G)
  | intersection : FormulaGTy F → FormulaGTy G → FormulaGTy (.intersection F G)
  | bottom : FormulaGTy .bottom
  | negClass : FormulaGTy (.negClass cname)

private def formulaGTy_decide : (G : GTy) → Decidable (FormulaGTy G)
  | .any => .isTrue .any
  | .class_ _ => .isTrue .class_
  | .callable _ _ => .isFalse fun h => nomatch h
  | .union F G =>
      match formulaGTy_decide F, formulaGTy_decide G with
      | .isTrue hF, .isTrue hG => .isTrue (.union hF hG)
      | .isFalse hF, _ => .isFalse fun | .union hF' _ => hF hF'
      | _, .isFalse hG => .isFalse fun | .union _ hG' => hG hG'
  | .intersection F G =>
      match formulaGTy_decide F, formulaGTy_decide G with
      | .isTrue hF, .isTrue hG => .isTrue (.intersection hF hG)
      | .isFalse hF, _ => .isFalse fun | .intersection hF' _ => hF hF'
      | _, .isFalse hG => .isFalse fun | .intersection _ hG' => hG hG'
  | .bottom => .isTrue .bottom
  | .negClass _ => .isTrue .negClass

instance : Decidable (FormulaGTy G) :=
  formulaGTy_decide G

/-- MRO-relative recursive predicate: `FormulaHoldsForMro mro F` holds
    when the formula `F` is satisfied by the given MRO. For non-formula
    types (callable) the result is `False`. -/
def FormulaHoldsForMro (mro : List Identifier) : GTy → Prop
  | .any => True
  | .class_ cname => cname ∈ mro
  | .callable _ _ => False
  | .union F G => FormulaHoldsForMro mro F ∨ FormulaHoldsForMro mro G
  | .intersection F G => FormulaHoldsForMro mro F ∧ FormulaHoldsForMro mro G
  | .bottom => False
  | .negClass cname => cname ∉ mro

/-- A formula is BM-compatible when it is a `FormulaGTy` and holds for
    every verified `BoundMethod` MRO in the class table. -/
def BMCompatibleFormula (gct : GClassTable) (F : GTy) : Prop :=
  FormulaGTy F ∧
  ∀ bmcls bmmro,
    findGClass gct boundMethodClass = some bmcls →
    GComputeMro gct bmcls bmmro →
    FormulaHoldsForMro bmmro F

private inductive LocalTypePrecision : GTy → GTy → Prop where
  | refl :
      LocalTypePrecision G G
  | toAny :
      LocalTypePrecision G .any
  | callable :
      LocalTypePrecision P₁ P₂ →
      LocalTypePrecision R₁ R₂ →
      LocalTypePrecision (.callable P₁ R₁) (.callable P₂ R₂)
  | union :
      LocalTypePrecision G₁ G₂ →
      LocalTypePrecision H₁ H₂ →
      LocalTypePrecision (.union G₁ H₁) (.union G₂ H₂)
  | intersection :
      LocalTypePrecision G₁ G₂ →
      LocalTypePrecision H₁ H₂ →
      LocalTypePrecision (.intersection G₁ H₁) (.intersection G₂ H₂)

private theorem localTypePrecision_of_checkedTargetPrecision
    (hprec : CheckedTargetPrecision T₁ T₂) :
    LocalTypePrecision (interpTarget T₁) (interpTarget T₂) := by
  induction hprec with
  | refl =>
      exact .refl
  | toAny =>
      exact .toAny
  | callable _ _ ihParam ihReturn =>
      exact .callable ihParam ihReturn
  | union _ _ ihLeft ihRight =>
      exact .union ihLeft ihRight
  | intersection _ _ ihLeft ihRight =>
      exact .intersection ihLeft ihRight

/-! ### Formula transport through structural precision -/

private theorem formulaGTy_precision
    (hprec : LocalTypePrecision F₁ F₂)
    (hformula : FormulaGTy F₁) :
    FormulaGTy F₂ := by
  induction hprec with
  | refl => exact hformula
  | toAny => exact .any
  | callable => cases hformula
  | union _ _ ihF ihG =>
    let .union hF hG := hformula
    exact .union (ihF hF) (ihG hG)
  | intersection _ _ ihF ihG =>
    let .intersection hF hG := hformula
    exact .intersection (ihF hF) (ihG hG)

private theorem formulaHoldsForMro_precision
    (hprec : LocalTypePrecision F₁ F₂)
    (hformula : FormulaGTy F₁)
    (hh : FormulaHoldsForMro mro F₁) :
    FormulaHoldsForMro mro F₂ := by
  induction hprec with
  | refl => exact hh
  | toAny => exact trivial
  | callable => cases hformula
  | union _ _ ihF ihG =>
    let .union hF hG := hformula
    exact hh.imp (ihF hF) (ihG hG)
  | intersection _ _ ihF ihG =>
    let .intersection hF hG := hformula
    exact ⟨ihF hF hh.1, ihG hG hh.2⟩

/-- The admissible checked target type fragment. Machine-facing target
    types must lie in this fragment so that preservation can use exact
    enforcement evidence without generic witness subsumption.

    Allowed shapes:
    1. Any class formula
    2. `callable P R` with admissible P and R
    3. `union G H` with both sides admissible
    4. `intersection (callable P R) F` with admissible callable and BM-compatible formula
    5. `intersection F (callable P R)` with the same side condition

    Not allowed: two positive callable branches in one intersection,
    callable intersected with a formula not guaranteed on BM-backed values,
    or arbitrary negation targets. -/
inductive CheckedTargetTy (gct : GClassTable) : GTy → Prop where
  /-- Any formula is admissible. -/
  | classFormula : FormulaGTy G → CheckedTargetTy gct G
  /-- Callable with admissible parameter and return types. -/
  | callable :
      CheckedTargetTy gct P →
      CheckedTargetTy gct R →
      CheckedTargetTy gct (.callable P R)
  /-- Union of admissible types. -/
  | union :
      CheckedTargetTy gct G →
      CheckedTargetTy gct H →
      CheckedTargetTy gct (.union G H)
  /-- Callable intersected with a BM-compatible formula (callable first). -/
  | interCallableLeft :
      CheckedTargetTy gct P →
      CheckedTargetTy gct R →
      BMCompatibleFormula gct F →
      CheckedTargetTy gct (.intersection (.callable P R) F)
  /-- Callable intersected with a BM-compatible formula (formula first). -/
  | interCallableRight :
      BMCompatibleFormula gct F →
      CheckedTargetTy gct P →
      CheckedTargetTy gct R →
      CheckedTargetTy gct (.intersection F (.callable P R))

/-! ### Admissible fragment closure lemmas -/

/-- BM-compatible formulas are formulas. -/
theorem BMCompatibleFormula.toFormula (h : BMCompatibleFormula gct F) :
    FormulaGTy F := h.1

/-- BM-compatible formulas are admissible target types. -/
theorem BMCompatibleFormula.toCheckedTargetTy (h : BMCompatibleFormula gct F) :
    CheckedTargetTy gct F := .classFormula h.toFormula

/-- A runtime/public checked target is a normalized checked target whose
interpreted source type lies in the admissible fragment. -/
def RuntimePublicCheckedTarget (gct : GClassTable) (T : CheckedTarget) : Prop :=
  RuntimePublicCheckedTargetShape T ∧ CheckedTargetTy gct (interpTarget T)

theorem runtimePublicCheckedTarget_shape
    (h : RuntimePublicCheckedTarget gct T) :
    RuntimePublicCheckedTargetShape T :=
  h.1

theorem runtimePublicCheckedTarget_checked
    (h : RuntimePublicCheckedTarget gct T) :
    CheckedTargetTy gct (interpTarget T) :=
  h.2

theorem runtimePublicCheckedTarget_mk
    (hshape : RuntimePublicCheckedTargetShape T)
    (hchecked : CheckedTargetTy gct (interpTarget T)) :
    RuntimePublicCheckedTarget gct T :=
  ⟨hshape, hchecked⟩

theorem runtimePublicCheckedTarget_normalize
    (hchecked : CheckedTargetTy gct (interpTarget T)) :
    RuntimePublicCheckedTarget gct (coreNormalizeCheckedTarget T) := by
  refine ⟨runtimePublicCheckedTargetShape_normalized T, ?_⟩
  simpa using hchecked

/-- Source-level admissibility phrased through the explicit checked-target
image of `G`. -/
def RuntimePublicAnnotation (gct : GClassTable) (G : GTy) : Prop :=
  RuntimePublicCheckedTarget gct (checkedTargetOfGTy G)

theorem runtimePublicAnnotation_shape
    (h : RuntimePublicAnnotation gct G) :
    RuntimePublicCheckedTargetShape (checkedTargetOfGTy G) :=
  h.1

theorem runtimePublicAnnotation_checked
    (h : RuntimePublicAnnotation gct G) :
    CheckedTargetTy gct G :=
  by simpa using h.2

theorem runtimePublicAnnotation_mk
    (hchecked : CheckedTargetTy gct G) :
    RuntimePublicAnnotation gct G :=
  ⟨runtimePublicCheckedTargetShape_all _, by simpa using hchecked⟩

theorem runtimePublicAnnotation_iff_checkedTargetTy
    (gct : GClassTable) (G : GTy) :
    RuntimePublicAnnotation gct G ↔ CheckedTargetTy gct G := by
  constructor
  · intro h
    simpa using h.2
  · intro h
    exact runtimePublicAnnotation_mk h

theorem bmCompatibleFormula_iff_computeGMro
    (gct : GClassTable) (F : GTy) :
    BMCompatibleFormula gct F ↔
      FormulaGTy F ∧
        match computeGMro? gct boundMethodClass with
        | some bmmro => FormulaHoldsForMro bmmro F
        | none => True := by
  cases hcomp : computeGMro? gct boundMethodClass with
  | none =>
      constructor
      · intro h
        exact ⟨h.1, trivial⟩
      · intro h
        refine ⟨h.1, ?_⟩
        intro bmcls bmmro hfind hmro
        have hsome : computeGMro? gct boundMethodClass = some bmmro :=
          computeGMro?_complete hfind hmro
        rw [hcomp] at hsome
        cases hsome
  | some bmmro =>
      constructor
      · intro h
        obtain ⟨bmcls, hfind, hmro⟩ :=
          computeGMro?_sound (gct := gct) (cname := boundMethodClass) (mro := bmmro) hcomp
        exact ⟨h.1, h.2 bmcls bmmro hfind hmro⟩
      · intro h
        refine ⟨h.1, ?_⟩
        intro bmcls' bmmro' hfind' hmro'
        obtain ⟨bmcls, hfind, hmro⟩ :=
          computeGMro?_sound (gct := gct) (cname := boundMethodClass) (mro := bmmro) hcomp
        rw [hfind] at hfind'
        cases hfind'
        have hmroEq : bmmro = bmmro' :=
          gComputeMro_determinism hmro hmro'
        simpa [hmroEq] using h.2

private theorem bmCompatibleFormula_precision
    (hprec : LocalTypePrecision F₁ F₂)
    (hbm : BMCompatibleFormula gct F₁) :
    BMCompatibleFormula gct F₂ := by
  refine ⟨formulaGTy_precision hprec hbm.1, ?_⟩
  intro bmcls bmmro hfind hmro
  exact formulaHoldsForMro_precision hprec hbm.1 (hbm.2 bmcls bmmro hfind hmro)

/-- Decidability of MRO satisfaction for formula types. -/
instance formulaHoldsForMro_decidable (mro : List Identifier) (F : GTy) :
    Decidable (FormulaHoldsForMro mro F) :=
  match F with
  | .any => .isTrue trivial
  | .class_ cname => inferInstanceAs (Decidable (cname ∈ mro))
  | .callable _ _ => .isFalse id
  | .union F G =>
    have := formulaHoldsForMro_decidable mro F
    have := formulaHoldsForMro_decidable mro G
    inferInstanceAs (Decidable (_ ∨ _))
  | .intersection F G =>
    have := formulaHoldsForMro_decidable mro F
    have := formulaHoldsForMro_decidable mro G
    inferInstanceAs (Decidable (_ ∧ _))
  | .bottom => .isFalse id
  | .negClass cname =>
    inferInstanceAs (Decidable (cname ∉ mro))

instance : Decidable (BMCompatibleFormula gct F) := by
  rw [bmCompatibleFormula_iff_computeGMro]
  cases hcomp : computeGMro? gct boundMethodClass <;> infer_instance

private theorem checkedTargetTy_intersection_iff
    (gct : GClassTable) (A B : GTy) :
    CheckedTargetTy gct (.intersection A B) ↔
      (FormulaGTy A ∧ FormulaGTy B) ∨
      (match A with
       | .callable P R => CheckedTargetTy gct P ∧ CheckedTargetTy gct R ∧ BMCompatibleFormula gct B
       | _ => False) ∨
      (match B with
       | .callable P R => BMCompatibleFormula gct A ∧ CheckedTargetTy gct P ∧ CheckedTargetTy gct R
       | _ => False) := by
  constructor
  · intro h
    cases h with
    | classFormula hF =>
        cases hF with
        | intersection hA hB =>
            exact Or.inl ⟨hA, hB⟩
    | interCallableLeft hP hR hB =>
        exact Or.inr <| Or.inl ⟨hP, hR, hB⟩
    | interCallableRight hA hP hR =>
        exact Or.inr <| Or.inr ⟨hA, hP, hR⟩
  · intro h
    rcases h with hFormula | hLeft | hRight
    · exact .classFormula (.intersection hFormula.1 hFormula.2)
    · cases A with
      | callable P R =>
          exact .interCallableLeft hLeft.1 hLeft.2.1 hLeft.2.2
      | any | class_ | union | intersection | bottom | negClass =>
          cases hLeft
    · cases B with
      | callable P R =>
          exact .interCallableRight hRight.1 hRight.2.1 hRight.2.2
      | any | class_ | union | intersection | bottom | negClass =>
          cases hRight

private def checkedTargetTy_decide (gct : GClassTable) : (G : GTy) → Decidable (CheckedTargetTy gct G)
  | .any => .isTrue (.classFormula .any)
  | .class_ _ => .isTrue (.classFormula .class_)
  | .bottom => .isTrue (.classFormula .bottom)
  | .negClass _ => .isTrue (.classFormula .negClass)
  | .callable P R =>
      match checkedTargetTy_decide gct P, checkedTargetTy_decide gct R with
      | .isTrue hP, .isTrue hR => .isTrue (.callable hP hR)
      | .isFalse hP, _ => .isFalse fun
          | .classFormula hF => nomatch hF
          | .callable hP' _ => hP hP'
      | _, .isFalse hR => .isFalse fun
          | .classFormula hF => nomatch hF
          | .callable _ hR' => hR hR'
  | .union G H =>
      match checkedTargetTy_decide gct G, checkedTargetTy_decide gct H with
      | .isTrue hG, .isTrue hH => .isTrue (.union hG hH)
      | .isFalse hG, _ => .isFalse fun
          | .classFormula (.union hG' _) => hG (.classFormula hG')
          | .union hG' _ => hG hG'
      | _, .isFalse hH => .isFalse fun
          | .classFormula (.union _ hH') => hH (.classFormula hH')
          | .union _ hH' => hH hH'
  | .intersection A B =>
      let hLeft : Decidable (FormulaGTy A ∧ FormulaGTy B) := inferInstance
      let hMid : Decidable
          (match A with
           | .callable P R => CheckedTargetTy gct P ∧ CheckedTargetTy gct R ∧ BMCompatibleFormula gct B
           | _ => False) := by
            cases A with
            | callable P R =>
                have := checkedTargetTy_decide gct P
                have := checkedTargetTy_decide gct R
                infer_instance
            | any | class_ | union | intersection | bottom | negClass =>
                exact .isFalse (by intro h; cases h)
      let hRight : Decidable
          (match B with
           | .callable P R => BMCompatibleFormula gct A ∧ CheckedTargetTy gct P ∧ CheckedTargetTy gct R
           | _ => False) := by
            cases B with
            | callable P R =>
                have := checkedTargetTy_decide gct P
                have := checkedTargetTy_decide gct R
                infer_instance
            | any | class_ | union | intersection | bottom | negClass =>
                exact .isFalse (by intro h; cases h)
      match hLeft, hMid, hRight with
      | .isTrue hLeft', _, _ =>
          .isTrue ((checkedTargetTy_intersection_iff gct A B).2 <| Or.inl hLeft')
      | .isFalse hLeft', .isTrue hMid', _ =>
          .isTrue ((checkedTargetTy_intersection_iff gct A B).2 <| Or.inr <| Or.inl hMid')
      | .isFalse hLeft', .isFalse hMid', .isTrue hRight' =>
          .isTrue ((checkedTargetTy_intersection_iff gct A B).2 <| Or.inr <| Or.inr hRight')
      | .isFalse hLeft', .isFalse hMid', .isFalse hRight' =>
          .isFalse (by
            intro h
            rcases (checkedTargetTy_intersection_iff gct A B).1 h with hLeft'' | hMid'' | hRight'' 
            · exact hLeft' hLeft''
            · exact hMid' hMid''
            · exact hRight' hRight'')

instance : Decidable (CheckedTargetTy gct G) :=
  checkedTargetTy_decide gct G

instance runtimePublicCheckedTarget_decidable
    (gct : GClassTable) (T : CheckedTarget) :
    Decidable (RuntimePublicCheckedTarget gct T) := by
  dsimp [RuntimePublicCheckedTarget]
  infer_instance

instance runtimePublicAnnotation_decidable
    (gct : GClassTable) (G : GTy) :
    Decidable (RuntimePublicAnnotation gct G) := by
  dsimp [RuntimePublicAnnotation]
  infer_instance

private theorem checkedTargetTy_precision
    (hprec : LocalTypePrecision G₁ G₂)
    (h : CheckedTargetTy gct G₁) :
    CheckedTargetTy gct G₂ := by
  induction h generalizing G₂ with
  | classFormula hformula =>
      exact .classFormula (formulaGTy_precision hprec hformula)
  | callable hP hR ihP ihR =>
      cases hprec with
      | refl =>
          exact .callable hP hR
      | toAny =>
          exact .classFormula .any
      | callable hprecP hprecR =>
          exact .callable (ihP hprecP) (ihR hprecR)
  | union hG hH ihG ihH =>
      cases hprec with
      | refl =>
          exact .union hG hH
      | toAny =>
          exact .classFormula .any
      | union hprecG hprecH =>
          exact .union (ihG hprecG) (ihH hprecH)
  | interCallableLeft hP hR hbm ihP ihR =>
      cases hprec with
      | refl =>
          exact .interCallableLeft hP hR hbm
      | toAny =>
          exact .classFormula .any
      | intersection hprecCall hprecF =>
          cases hprecCall with
          | refl =>
              exact .interCallableLeft hP hR
                (bmCompatibleFormula_precision hprecF hbm)
          | toAny =>
              exact .classFormula
                (.intersection .any (formulaGTy_precision hprecF hbm.1))
          | callable hprecP hprecR =>
              exact .interCallableLeft
                (ihP hprecP)
                (ihR hprecR)
                (bmCompatibleFormula_precision hprecF hbm)
  | interCallableRight hbm hP hR ihP ihR =>
      cases hprec with
      | refl =>
          exact .interCallableRight hbm hP hR
      | toAny =>
          exact .classFormula .any
      | intersection hprecF hprecCall =>
          cases hprecCall with
          | refl =>
              exact .interCallableRight
                (bmCompatibleFormula_precision hprecF hbm)
                hP hR
          | toAny =>
              exact .classFormula
                (.intersection (formulaGTy_precision hprecF hbm.1) .any)
          | callable hprecP hprecR =>
              exact .interCallableRight
                (bmCompatibleFormula_precision hprecF hbm)
                (ihP hprecP)
                (ihR hprecR)

theorem formulaGTy_annotationPrecision
    (hprec : AnnotationTargetPrecision F₁ F₂)
    (hformula : FormulaGTy F₁) :
    FormulaGTy F₂ := by
  exact formulaGTy_precision
    (by
      simpa [AnnotationTargetPrecision] using
        localTypePrecision_of_checkedTargetPrecision hprec)
    hformula

theorem formulaHoldsForMro_annotationPrecision
    (hprec : AnnotationTargetPrecision F₁ F₂)
    (hformula : FormulaGTy F₁)
    (hh : FormulaHoldsForMro mro F₁) :
    FormulaHoldsForMro mro F₂ := by
  exact formulaHoldsForMro_precision
    (by
      simpa [AnnotationTargetPrecision] using
        localTypePrecision_of_checkedTargetPrecision hprec)
    hformula
    hh

theorem bmCompatibleFormula_annotationPrecision
    (hprec : AnnotationTargetPrecision F₁ F₂)
    (hbm : BMCompatibleFormula gct F₁) :
    BMCompatibleFormula gct F₂ := by
  exact bmCompatibleFormula_precision
    (by
      simpa [AnnotationTargetPrecision] using
        localTypePrecision_of_checkedTargetPrecision hprec)
    hbm

theorem checkedTargetTy_annotationPrecision
    (hprec : AnnotationTargetPrecision G₁ G₂)
    (h : CheckedTargetTy gct G₁) :
    CheckedTargetTy gct G₂ := by
  exact checkedTargetTy_precision
    (by
      simpa [AnnotationTargetPrecision] using
        localTypePrecision_of_checkedTargetPrecision hprec)
    h

private theorem checkedTargetTy_checkedTargetPrecision
    (h : CheckedTargetTy gct (interpTarget T₁))
    (hprec : CheckedTargetPrecision T₁ T₂) :
    CheckedTargetTy gct (interpTarget T₂) := by
  have hprec' : AnnotationTargetPrecision (interpTarget T₁) (interpTarget T₂) := by
    simpa [AnnotationTargetPrecision] using hprec
  exact checkedTargetTy_annotationPrecision hprec' h

/-- Class negations are admissible class formulas. -/
theorem checkedTargetTy_negClass :
    CheckedTargetTy gct (.negClass cname) :=
  .classFormula .negClass

/-! ### Preservation of `runtimePublicTy` -/

/-- `runtimePublicTy` preserves the formula fragment. -/
theorem formulaGTy_runtimePublicTy (h : FormulaGTy G) : FormulaGTy (runtimePublicTy G) := by
  induction h with
  | any => exact .any
  | class_ => exact .class_
  | bottom => exact .bottom
  | negClass => exact .negClass
  | union _ _ ihF ihG => simp only [runtimePublicTy]; exact .union ihF ihG
  | intersection _ _ ihF ihG => simp only [runtimePublicTy]; exact .intersection ihF ihG

/-- `FormulaHoldsForMro` is preserved by `runtimePublicTy` for formulas. -/
theorem formulaHoldsForMro_runtimePublicTy
    (hf : FormulaGTy G)
    (hh : FormulaHoldsForMro mro G) :
    FormulaHoldsForMro mro (runtimePublicTy G) := by
  induction hf with
  | any => exact trivial
  | class_ => exact hh
  | bottom => exact hh
  | negClass => exact hh
  | union _ _ ihF ihG =>
    simp only [runtimePublicTy, FormulaHoldsForMro] at hh ⊢
    exact hh.elim (.inl ∘ ihF) (.inr ∘ ihG)
  | intersection _ _ ihF ihG =>
    simp only [runtimePublicTy, FormulaHoldsForMro] at hh ⊢
    exact ⟨ihF hh.1, ihG hh.2⟩

/-- `runtimePublicTy` preserves BM-compatibility. -/
theorem bmCompatibleFormula_runtimePublicTy
    (h : BMCompatibleFormula gct G) :
    BMCompatibleFormula gct (runtimePublicTy G) :=
  ⟨formulaGTy_runtimePublicTy h.1,
   fun _ _ hfind hmro =>
     formulaHoldsForMro_runtimePublicTy h.1 (h.2 _ _ hfind hmro)⟩

/-- `runtimePublicTy` preserves the admissible checked target fragment. -/
theorem checkedTargetTy_runtimePublicTy
    (h : CheckedTargetTy gct G) : CheckedTargetTy gct (runtimePublicTy G) := by
  induction h with
  | classFormula hf => exact .classFormula (formulaGTy_runtimePublicTy hf)
  | callable _ _ ihP ihR => simp only [runtimePublicTy]; exact .callable ihP ihR
  | union _ _ ihG ihH => simp only [runtimePublicTy]; exact .union ihG ihH
  | interCallableLeft _ _ hbm ihP ihR =>
    simp only [runtimePublicTy]
    exact .interCallableLeft ihP ihR (bmCompatibleFormula_runtimePublicTy hbm)
  | interCallableRight hbm _ _ ihP ihR =>
    simp only [runtimePublicTy]
    exact .interCallableRight (bmCompatibleFormula_runtimePublicTy hbm) ihP ihR
