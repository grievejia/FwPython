import FwPython.Gradual.TypeSystem.TargetAdmissibility
import FwPython.Gradual.TypeSystem.WellFormedness
import FwPython.Gradual.Invariants
import FwPython.Gradual.Statics
import FwPython.Gradual.MRO.LookupLemmas
import FwPython.Static.Subtyping.Completeness

/-! ## Core gradual class-table well-formedness

Contains the structural invariants, gradual Liskov override
compatibility, and method signature admissibility. -/

/-- Method overrides satisfy the gradual Liskov substitution principle:
    parent parameter assignable to child parameter (contravariant),
    child return assignable to parent return (covariant).
    Uses `AssignableTo` rather than `IsSubtype` since gradual types
    may involve `any`. -/
def GradualLiskovCondition (gct : GClassTable) : Prop :=
  ∀ cname aname c_cls a_cls mro_c mro_a methodName m_c m_a,
    findGClass gct cname = some c_cls →
    GComputeMro gct c_cls mro_c →
    aname ∈ mro_c →
    findGClass gct aname = some a_cls →
    GComputeMro gct a_cls mro_a →
    findGMethodInMro gct mro_c methodName = some m_c →
    findGMethodInMro gct mro_a methodName = some m_a →
    AssignableTo gct m_a.paramTy m_c.paramTy ∧
      AssignableTo gct m_c.returnTy m_a.returnTy

/-- Core well-formedness for a gradual class table: raw structural
    invariants plus method signature admissibility and gradual Liskov
    compatibility. -/
structure WellFormedGClassTableCore (gct : GClassTable) where
  /-- Raw structural invariants (MRO existence, built-in classes, etc.). -/
  raw : WellFormedGClassTable gct
  /-- Method overrides satisfy gradual Liskov. -/
  gradualLiskovCondition : GradualLiskovCondition gct
  /-- Method names are unique within each class. -/
  allMethodNamesDistinct : ∀ cname c,
    findGClass gct cname = some c →
    List.Nodup (c.methods.map MethodDecl.name)
  /-- Every method signature uses well-formed gradual types. -/
  allMethodSignaturesWellFormed : ∀ cname c m,
    findGClass gct cname = some c →
    m ∈ c.methods →
    WellFormedGTy gct m.paramTy ∧ WellFormedGTy gct m.returnTy
  /-- Every method signature lies in the runtime/public checked-target
      fragment through the explicit checked-target image. -/
  allMethodSignaturesRuntimePublic : ∀ cname c m,
    findGClass gct cname = some c →
    m ∈ c.methods →
    RuntimePublicAnnotation gct m.paramTy ∧ RuntimePublicAnnotation gct m.returnTy

instance wellFormedGClassTableCore_subsingleton :
    Subsingleton (WellFormedGClassTableCore gct) :=
  ⟨fun ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ => by congr 1 <;> exact Subsingleton.elim _ _⟩

/-- The static-side well-formedness of the erased class table. -/
private def WellFormedGClassTableCore.eraseWf
    (hwfct : WellFormedGClassTableCore gct) :
    WellFormedClassTable (eraseClassTable gct) :=
  eraseClassTable_wellFormed hwfct.raw hwfct.allMethodNamesDistinct

private theorem bounds_wellFormed
    (hwfct : WellFormedGClassTableCore gct)
    (hwfG : WellFormedGTy gct G) :
    WellFormedTy (eraseClassTable gct) (lowerBound G) ∧
      WellFormedTy (eraseClassTable gct) (upperBound G) := by
  induction hwfG with
  | any =>
      exact ⟨.bottom, wellFormed_object_type hwfct.eraseWf⟩
  | bottom =>
      exact ⟨.bottom, .bottom⟩
  | class_ hfind hmro =>
      let hwfClass :=
        WellFormedTy.class_ (findClass_eraseClassTable hfind) (gComputeMro_eraseClassTable hmro)
      exact ⟨by simpa [lowerBound] using hwfClass, by simpa [upperBound] using hwfClass⟩
  | callable _ _ ihP ihR =>
      exact ⟨by
                simpa [lowerBound, upperBound] using WellFormedTy.callable ihP.2 ihR.1,
             by
                simpa [lowerBound, upperBound] using WellFormedTy.callable ihP.1 ihR.2⟩
  | union _ _ ihT ihU =>
      exact ⟨by
                simpa [lowerBound] using WellFormedTy.union ihT.1 ihU.1,
             by
                simpa [upperBound] using WellFormedTy.union ihT.2 ihU.2⟩
  | intersection _ _ ihT ihU =>
      exact ⟨by
                simpa [lowerBound] using WellFormedTy.intersection ihT.1 ihU.1,
             by
                simpa [upperBound] using WellFormedTy.intersection ihT.2 ihU.2⟩
  | negClass hfind hmro =>
      let hwfNeg :=
        WellFormedTy.negClass (findClass_eraseClassTable hfind) (gComputeMro_eraseClassTable hmro)
      exact ⟨by simpa [lowerBound] using hwfNeg, by simpa [upperBound] using hwfNeg⟩

theorem lowerBound_wellFormed
    (hwfct : WellFormedGClassTableCore gct)
    (hwfG : WellFormedGTy gct G) :
    WellFormedTy (eraseClassTable gct) (lowerBound G) :=
  (bounds_wellFormed hwfct hwfG).1

theorem upperBound_wellFormed
    (hwfct : WellFormedGClassTableCore gct)
    (hwfG : WellFormedGTy gct G) :
    WellFormedTy (eraseClassTable gct) (upperBound G) :=
  (bounds_wellFormed hwfct hwfG).2

def gradualSubtype_decidable
    (hwfct : WellFormedGClassTableCore gct)
    (hwfG₁ : WellFormedGTy gct G₁)
    (hwfG₂ : WellFormedGTy gct G₂) :
    Decidable (GradualSubtype gct G₁ G₂) := by
  unfold GradualSubtype
  exact isSubtype_decidable hwfct.eraseWf
    (upperBound_wellFormed hwfct hwfG₁)
    (upperBound_wellFormed hwfct hwfG₂)

def assignableTo_decidable
    (hwfct : WellFormedGClassTableCore gct)
    (hwfG₁ : WellFormedGTy gct G₁)
    (hwfG₂ : WellFormedGTy gct G₂) :
    Decidable (AssignableTo gct G₁ G₂) := by
  unfold AssignableTo
  exact isSubtype_decidable hwfct.eraseWf
    (lowerBound_wellFormed hwfct hwfG₁)
    (upperBound_wellFormed hwfct hwfG₂)

/-! ### `runtimePublicTy` preserves well-formedness -/

/-- `runtimePublicTy` preserves well-formedness of gradual types. -/
theorem wellFormedGTy_runtimePublicTy
    (h : WellFormedGTy gct G) : WellFormedGTy gct (runtimePublicTy G) := by
  induction h with
  | any => exact .any
  | bottom => exact .bottom
  | class_ hfind hmro => exact .class_ hfind hmro
  | callable _ _ ihP ihR => simp only [runtimePublicTy]; exact .callable ihP ihR
  | union _ _ ih₁ ih₂ => simp only [runtimePublicTy]; exact .union ih₁ ih₂
  | intersection _ _ ih₁ ih₂ => simp only [runtimePublicTy]; exact .intersection ih₁ ih₂
  | negClass hfind hmro => exact .negClass hfind hmro
