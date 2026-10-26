import FwPython.Gradual.TypeSystem.ClassTable.WellFormednessCore
import FwPython.Gradual.TypeSystem.Method.Lookup

/-! ## Method-type lookup facts

A method lookup returns valid parameter and result annotations. -/

/-- Method types found via `FindGMethodType` are well-formed. -/
theorem wellFormedGTy_of_findGMethodType
    (hwfct : WellFormedGClassTableCore gct)
    (hfind : FindGMethodType gct cname methodName paramTy returnTy) :
    WellFormedGTy gct paramTy ∧ WellFormedGTy gct returnTy := by
  obtain ⟨_, _, m, _, _, hmeth, rfl, rfl⟩ := hfind
  obtain ⟨dname, d, _, hfd, hm_in_d⟩ := findGMethodInMro_provenance hmeth
  exact hwfct.allMethodSignaturesWellFormed dname d m hfd hm_in_d
