import FwPython.Static.Subtyping.Carrier

/-! ## `SemObject` helper lemmas -/

theorem SemObject.object_mem (obj : SemObject ct) :
    obj.hasAncestor objectClass := by
  cases obj with
  | ordinaryCurrent cur =>
      exact cur.object_mem
  | ordinaryFresh fr =>
      exact fr.object_mem
  | boundMethod bm =>
      exact bm.object_mem

theorem SemObject.hasAncestor_closed
    (obj : SemObject ct)
    (hanc : obj.hasAncestor A)
    (hfind : findClass ct A = some acls)
    (hmro : ComputeMro ct acls amro)
    (hmem : B ∈ amro) :
    obj.hasAncestor B := by
  cases obj with
  | ordinaryCurrent cur =>
      exact cur.hasAncestor_closed hanc hfind hmro hmem
  | ordinaryFresh fr =>
      exact fr.hasAncestor_closed hanc hfind hmro hmem
  | boundMethod bm =>
      exact bm.hasAncestor_closed hanc hfind hmro hmem
