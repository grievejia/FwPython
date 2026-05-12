import FwPython.Static.MRO.Compute

/-! # Method lookup via MRO -/

/-- Method `m` is the result of MRO name lookup from the receiver's class. -/
abbrev MethodInReceiverMro (ct : ClassTable) (recvClass : Identifier) (m : Method) : Prop :=
  MethodInReceiverMroOf ComputeMro ct recvClass m
