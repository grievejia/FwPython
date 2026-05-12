import FwPython.Gradual.TypeSystem.ClassTable.WellFormednessCore
import FwPython.Gradual.TypeSystem.Method.Lookup

/-! ## Method-type lookup facts

Well-formedness and checked-target admissibility of method types found
via `FindGMethodType`. These are method-lookup facts, not elaboration
facts. -/

/-- Method types found via `FindGMethodType` are well-formed. -/
theorem wellFormedGTy_of_findGMethodType
    (hwfct : WellFormedGClassTableCore gct)
    (hfind : FindGMethodType gct cname methodName paramTy returnTy) :
    WellFormedGTy gct paramTy ∧ WellFormedGTy gct returnTy := by
  obtain ⟨c, mro, m, hfc, hmro, hmeth, rfl, rfl⟩ := hfind
  obtain ⟨dname, d, _, hfd, hm_in_d⟩ := findGMethodInMro_provenance hmeth
  exact hwfct.allMethodSignaturesWellFormed dname d m hfd hm_in_d

/-- Method types found via `FindGMethodType` lie in the runtime/public
checked-target fragment through their explicit checked-target images. -/
theorem runtimePublicAnnotation_of_findGMethodType
    (hwfct : WellFormedGClassTableCore gct)
    (hfind : FindGMethodType gct cname methodName paramTy returnTy) :
    RuntimePublicAnnotation gct paramTy ∧ RuntimePublicAnnotation gct returnTy := by
  obtain ⟨c, mro, m, hfc, hmro, hmeth, rfl, rfl⟩ := hfind
  obtain ⟨dname, d, _, hfd, hm_in_d⟩ := findGMethodInMro_provenance hmeth
  exact hwfct.allMethodSignaturesRuntimePublic dname d m hfd hm_in_d
