import FwPython.Static.Subtyping.Equations
import FwPython.Static.Subtyping.Core
import FwPython.Static.Subtyping.SubtypeCheck

set_option autoImplicit false

/-! # Deciding subtyping from equations

`isSubtype_decidable` validates the class names in both type annotations.
`WellFormedType.subtypeDecidable` compares validated packages without repeating
these name checks. The normal-form comparison accepts exactly the type pairs
that have algebraic subtype proofs.
Type reduction and simple equality, bottom, and Object cases keep kernel
evaluation manageable. The decision returns a subtype proof or a proof that
subtyping does not hold.
-/

open FwPython.Static.Subtyping

/-- Simplify unions and intersections with bottom, Object, or two equal components.
Each result carries name validity and subtype proofs in both directions. -/
def simplifySubtypeOperand {ct : ClassTable} (structural : WellFormedClassHierarchy ct)
    (type : WellFormedType (ct.map ClassDecl.name)) :
    { result : WellFormedType (ct.map ClassDecl.name) //
      IsSubtype structural type.raw result.raw ∧ IsSubtype structural result.raw type.raw } :=
  let context := structural.typeContext
  let objectKnown := context.valid.objectKnown
  let rec reduce (raw : Ty) (known : TypeNamesKnown context.names raw) :
      { result : WellFormedType context.names // TypeEquivalence context ⟨raw, known⟩ result } :=
    match raw with
    | .bottom => ⟨⟨.bottom, known⟩, .refl⟩
    | .class_ name => ⟨⟨.class_ name, known⟩, .refl⟩
    | .negClass name => ⟨⟨.negClass name, known⟩, .refl⟩
    | .callable parameter result =>
        let input := reduce parameter known.callable_param
        let output := reduce result known.callable_return
        ⟨.callable input.val output.val, .callable input.property output.property⟩
    | .union left right =>
        let l := reduce left known.union_left
        let r := reduce right known.union_right
        let equation := TypeEquivalence.union l.property r.property
        if empty : l.val.raw = .bottom then
          have equal : l.val = .bottom := WellFormedType.ext empty
          ⟨r.val, .trans equation (by rw [equal]; exact .trans .unionCommutative .unionBottom)⟩
        else if empty : r.val.raw = .bottom then
          have equal : r.val = .bottom := WellFormedType.ext empty
          ⟨l.val, .trans equation (by rw [equal]; exact .unionBottom)⟩
        else if top : l.val.raw = .class_ objectClass then
          have equal : l.val = .class_ objectClass objectKnown := WellFormedType.ext top
          ⟨l.val, .trans equation (by rw [equal]; exact .trans .unionCommutative TypeEquivalence.unionObject)⟩
        else if top : r.val.raw = .class_ objectClass then
          have equal : r.val = .class_ objectClass objectKnown := WellFormedType.ext top
          ⟨r.val, .trans equation (by rw [equal]; exact TypeEquivalence.unionObject)⟩
        else if equal : l.val.raw = r.val.raw then
          have equalTypes : l.val = r.val := WellFormedType.ext equal
          ⟨l.val, .trans equation (by rw [← equalTypes]; exact TypeEquivalence.unionIdempotent)⟩
        else
          ⟨.union l.val r.val, equation⟩
    | .intersection left right =>
        let l := reduce left known.intersection_left
        let r := reduce right known.intersection_right
        let equation := TypeEquivalence.intersection l.property r.property
        if empty : l.val.raw = .bottom then
          have equal : l.val = .bottom := WellFormedType.ext empty
          ⟨l.val, .trans equation (by rw [equal]; exact .trans .intersectionCommutative TypeEquivalence.meetBottom)⟩
        else if empty : r.val.raw = .bottom then
          have equal : r.val = .bottom := WellFormedType.ext empty
          ⟨r.val, .trans equation (by rw [equal]; exact TypeEquivalence.meetBottom)⟩
        else if top : l.val.raw = .class_ objectClass then
          have equal : l.val = .class_ objectClass objectKnown := WellFormedType.ext top
          ⟨r.val, .trans equation (by rw [equal]; exact .trans .intersectionCommutative .intersectionObject)⟩
        else if top : r.val.raw = .class_ objectClass then
          have equal : r.val = .class_ objectClass objectKnown := WellFormedType.ext top
          ⟨l.val, .trans equation (by rw [equal]; exact .intersectionObject)⟩
        else if equal : l.val.raw = r.val.raw then
          have equalTypes : l.val = r.val := WellFormedType.ext equal
          ⟨l.val, .trans equation (by rw [← equalTypes]; exact TypeEquivalence.intersectionIdempotent)⟩
        else
          ⟨.intersection l.val r.val, equation⟩
  let result := reduce type.raw type.namesKnown
  ⟨result.val, TypeEquivalence.toSubtype result.property,
    TypeEquivalence.toSubtype result.property.symm⟩

/-- Decide subtyping of packages without repeating name validation.
Equivalent reduction and the equality, bottom, and Object cases precede normal-form comparison. -/
def FwPython.Static.Subtyping.WellFormedType.subtypeDecidable {ct : ClassTable}
    (structural : WellFormedClassHierarchy ct)
    (source target : WellFormedType (ct.map ClassDecl.name)) :
    Decidable (IsSubtype structural source.raw target.raw) :=
  let first := simplifySubtypeOperand structural source
  let second := simplifySubtypeOperand structural target
  if equal : first.val.raw = second.val.raw then
    .isTrue (.trans first.property.1 (equal ▸ second.property.2))
  else if empty : first.val.raw = .bottom then
    .isTrue (.trans first.property.1
      (.trans (empty ▸ TypeEquivalence.Subtype.bottom second.val.namesKnown) second.property.2))
  else if top : second.val.raw = .class_ objectClass then
    .isTrue (.trans first.property.1
      (.trans (top ▸ TypeEquivalence.Subtype.objectTop first.val.namesKnown) second.property.2))
  else
    have equivalent := checkSubtypeBool_iff_subtype structural.typeContext first.val second.val
    decidable_of_iff (checkSubtypeBool structural.typeContext first.val second.val = true)
      ⟨fun accepted => .trans first.property.1 (.trans (equivalent.mp accepted) second.property.2),
        fun included => equivalent.mpr (.trans first.property.2 (.trans included second.property.1))⟩

/-- Decide subtyping of raw syntax. Both endpoints must name known classes.
A query with an unknown class name has no subtype proof. -/
def isSubtype_decidable {ct : ClassTable} {T U : Ty} (structural : WellFormedClassHierarchy ct) :
    Decidable (IsSubtype structural T U) :=
  match typeNamesKnown_decidable (ct.map ClassDecl.name) T with
  | .isFalse invalid => .isFalse (fun included => invalid included.sourceWellFormed)
  | .isTrue sourceKnown =>
      match typeNamesKnown_decidable (ct.map ClassDecl.name) U with
      | .isFalse invalid => .isFalse (fun included => invalid included.targetWellFormed)
      | .isTrue targetKnown =>
          WellFormedType.subtypeDecidable structural ⟨T, sourceKnown⟩ ⟨U, targetKnown⟩
