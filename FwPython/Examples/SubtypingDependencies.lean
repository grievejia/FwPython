import FwPython

/-! # Subtyping dependencies and constructive proofs

The root library includes the subtype comparison, expression checker, safety
proofs, and future hierarchy construction. Subtyping proofs use only type
equations and hierarchy facts. Two identifier guards check that the root import
leaves the specific names `BehavioralValue` and `RelationalInterpretation`
undefined.

The axiom guards separately cover subtype and expression decisions, comparison
correctness, callable inversion, value lower bounds, compiler typing, static
safety, no-blame, and future-hierarchy proofs. They allow only propext and Quot.sound.
-/

/-! ## Import guards -/

/-- error: Unknown identifier `FwPython.Static.Subtyping.BehavioralValue` -/
#guard_msgs in
#check FwPython.Static.Subtyping.BehavioralValue

/-- error: Unknown identifier `FwPython.Static.Subtyping.RelationalInterpretation` -/
#guard_msgs in
#check FwPython.Static.Subtyping.RelationalInterpretation

/-! ## Subtype and expression decisions -/

/-- info: 'FwPython.Static.Subtyping.checkSubtypeBool_iff_subtype' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FwPython.Static.Subtyping.checkSubtypeBool_iff_subtype

/-- info: 'FwPython.Static.Subtyping.WellFormedType.subtypeDecidable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FwPython.Static.Subtyping.WellFormedType.subtypeDecidable

/-- info: 'checkHasType?_iff_hasType' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkHasType?_iff_hasType

/-! ## Function inversion -/

/-- info: 'callable_domain_subtype' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms callable_domain_subtype

/-- info: 'callable_return_subtype' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms callable_return_subtype

/-! ## Heap value typing and static safety -/

/-- info: 'valueHasType_lowerBound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms valueHasType_lowerBound

/-- info: 'valueHasType_bottom_impossible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms valueHasType_bottom_impossible

/-- info: 'SmallStep.soundness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SmallStep.soundness

/-! ## Compiler typing and no-blame -/

/-- info: 'compileCheck_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms compileCheck_checked

/-- info: 'embedded_static_no_blame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms embedded_static_no_blame

/-! ## Future class hierarchies -/

/-- info: 'FwPython.Static.Subtyping.classIntersectionOfExtension_includesClass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FwPython.Static.Subtyping.classIntersectionOfExtension_includesClass

/-- info: 'FwPython.Static.Subtyping.extendWithClassIntersection' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FwPython.Static.Subtyping.extendWithClassIntersection

/-- info: 'FwPython.Static.Subtyping.ValidExtension.noCommonClass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FwPython.Static.Subtyping.ValidExtension.noCommonClass
