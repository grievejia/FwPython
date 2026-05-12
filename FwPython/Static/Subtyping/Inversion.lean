import FwPython.Static.Subtyping.Core
import FwPython.Static.Subtyping.AbstractSemantics

/-! ## Subtyping inversion via semantic witnesses -/

/-- Build the canonical `CurrentOrd` from class lookup/MRO witnesses. -/
private def currentOrdOf (cname : Identifier) (hfind : findClass ct cname = some cls)
    (hmro : ComputeMro ct cls mro) : CurrentOrd ct :=
  { cname, cls, mro, hfind, hmro }

/-- Callable subtyping inversion: if `callable(P,R) <: callable(P',R')`,
then `P' <: P` and `R <: R'`. -/
theorem callable_subtype_inv
    (hBMFind : findClass ct boundMethodClass = some bmCls)
    (hBMMro : ComputeMro ct bmCls bmMro)
    (h : IsSubtype ct (.callable P R) (.callable P' R')) :
    IsSubtype ct P' P ∧ IsSubtype ct R R' := by
  let bm : BoundMethodOrd ct :=
    { actualParam := P, actualReturn := R, cls := bmCls, mro := bmMro,
      hfind := hBMFind, hmro := hBMMro }
  simpa [Ty.semDenotes] using
    semDenotes_at_obj_sound (obj := .boundMethod bm) h (boundMethod_denotes_callable_self bm)

/-- Class subtyping MRO membership: if `class_ c <: class_ a`,
then `a` is in the MRO of `c`. -/
theorem class_subtype_mem_mro
    (hsub : IsSubtype ct (.class_ c) (.class_ a))
    (hfc : findClass ct c = some cls) (hmro : ComputeMro ct cls mro) :
    a ∈ mro := by
  let cur := currentOrdOf c hfc hmro
  have hseed : Ty.semDenotes ct (.class_ c) (.ordinaryCurrent cur) := by
    simpa [Ty.semDenotes, SemObject.hasAncestor, CurrentOrd.hasAncestor] using cur.self_mem
  simpa [Ty.semDenotes, SemObject.hasAncestor, CurrentOrd.hasAncestor] using
    semDenotes_at_obj_sound (obj := .ordinaryCurrent cur) hsub hseed
