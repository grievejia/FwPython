import FwPython.Gradual.MRO.Compute

/-! # Gradual method lookup via MRO -/

/-- Find a method by searching each class in the gradual MRO in order. -/
abbrev findGMethodInMro (ct : GClassTable) (mro : List Identifier)
    (mname : Identifier) : Option GMethod :=
  findMethodInMro ct mro mname

/-- Method `m` is the result of MRO name lookup from the receiver's class. -/
abbrev GMethodInReceiverMro (ct : GClassTable) (recvClass : Identifier)
    (m : GMethod) : Prop :=
  MethodInReceiverMroOf GComputeMro ct recvClass m
