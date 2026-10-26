import FwPython.Gradual.TypeSystem.TargetAdmissibility
import FwPython.Gradual.Statics
import FwPython.Gradual.MRO.LookupLemmas
import FwPython.Static.Subtyping.Decision

/-! ## Core gradual class-table well-formedness

Contains the structural invariants, gradual Liskov override
compatibility, and method signature admissibility.
The subtype decision helper compares static types in the erased class table. -/

/-- Method overrides satisfy the gradual Liskov substitution principle:
    parent parameter assignable to child parameter (contravariant),
    child return assignable to parent return (covariant).
    Uses `AssignableTo` rather than `IsSubtype` since gradual types
    may involve `any`. -/
def GradualLiskovCondition (gct : GClassTable)
    (structural : WellFormedClassHierarchy (eraseClassTable gct)) : Prop :=
  ∀ cname aname c_cls a_cls mro_c mro_a methodName m_c m_a,
    findGClass gct cname = some c_cls →
    GComputeMro gct c_cls mro_c →
    aname ∈ mro_c →
    findGClass gct aname = some a_cls →
    GComputeMro gct a_cls mro_a →
    findGMethodInMro gct mro_c methodName = some m_c →
    findGMethodInMro gct mro_a methodName = some m_a →
    AssignableTo gct structural m_a.paramTy m_c.paramTy ∧
      AssignableTo gct structural m_c.returnTy m_a.returnTy

/-- Core well-formedness for a gradual class table: raw structural
    invariants plus method signature admissibility and gradual Liskov
    compatibility. -/
structure WellFormedGClassTableCore (gct : GClassTable) where
  /-- Raw structural invariants (MRO existence, built-in classes, etc.). -/
  raw : WellFormedGClassTable gct
  /-- Method overrides satisfy gradual Liskov. -/
  gradualLiskovCondition : GradualLiskovCondition gct (eraseClassTable_structural raw)
  /-- Each class declaration permits one method per name. This is a source language rule. -/
  allMethodNamesDistinct : ∀ cname c,
    findGClass gct cname = some c →
    List.Nodup (c.methods.map MethodDecl.name)
  /-- Every method signature uses well-formed gradual types. -/
  allMethodSignaturesWellFormed : ∀ cname c m,
    findGClass gct cname = some c →
    m ∈ c.methods →
    WellFormedGTy gct m.paramTy ∧ WellFormedGTy gct m.returnTy
  /-- Every method signature lies in the admissible checked-target fragment. -/
  allMethodSignaturesCheckedTarget : ∀ cname c m,
    findGClass gct cname = some c →
    m ∈ c.methods →
    CheckedTargetTy gct m.paramTy ∧ CheckedTargetTy gct m.returnTy

instance wellFormedGClassTableCore_subsingleton :
    Subsingleton (WellFormedGClassTableCore gct) :=
  ⟨fun ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ => by congr 1 <;> exact Subsingleton.elim _ _⟩

/-- The static hierarchy used to compare the bounds of gradual annotations. -/
def WellFormedGClassTableCore.toWellFormedClassHierarchy
    (hwfct : WellFormedGClassTableCore gct) : WellFormedClassHierarchy (eraseClassTable gct) :=
  eraseClassTable_structural hwfct.raw

/-- Decide static subtyping in the hierarchy of the erased gradual class table. -/
def WellFormedGClassTableCore.subtypeDecidable
    (hwfct : WellFormedGClassTableCore gct) (source target : Ty) :
    Decidable (IsSubtype hwfct.toWellFormedClassHierarchy source target) :=
  isSubtype_decidable (T := source) (U := target) (eraseClassTable_structural hwfct.raw)
