import FwPython.Gradual.Contracts.Labels

/-! ## Compilation from GTy to BoundaryContract -/

/-- Structural compilation: maps each `GTy` constructor to its
    `BoundaryContract` counterpart. `any` compiles to `.unknown`. -/
def compileBoundaryRaw : GTy → BoundaryContract
  | .any => .unknown
  | .class_ c => .class_ c
  | .callable p r => .callable (compileBoundaryRaw p) (compileBoundaryRaw r)
  | .union t u => .union (compileBoundaryRaw t) (compileBoundaryRaw u)
  | .intersection t u => .intersection (compileBoundaryRaw t) (compileBoundaryRaw u)
  | .bottom => .bottom
  | .negClass c => .negClass c

/-- Normalize a boundary contract so that `.unknown` absorbs through
    union (`unknown ∪ c = unknown`) and passes through intersection
    (`unknown ∩ c = c`). `.negClass` is atomic so no nested normalization
    is needed at negation. All other constructors normalize recursively. -/
def normalizeBoundary : BoundaryContract → BoundaryContract
  | .unknown => .unknown
  | .class_ c => .class_ c
  | .callable d r => .callable (normalizeBoundary d) (normalizeBoundary r)
  | .union l r =>
    match normalizeBoundary l, normalizeBoundary r with
    | .unknown, _ => .unknown
    | _, .unknown => .unknown
    | l', r' => .union l' r'
  | .intersection l r =>
    match normalizeBoundary l, normalizeBoundary r with
    | .unknown, r' => r'
    | l', .unknown => l'
    | l', r' => .intersection l' r'
  | .bottom => .bottom
  | .negClass c => .negClass c

/-- Compile a gradual type to a normalized boundary contract.
    `compileBoundary = normalizeBoundary ∘ compileBoundaryRaw`. -/
def compileBoundary (g : GTy) : BoundaryContract :=
  normalizeBoundary (compileBoundaryRaw g)

/-- Compile a callable boundary from domain and codomain gradual types. -/
def compileCallableBoundary (domain codomain : GTy) : CallableBoundaryContract :=
  ⟨compileBoundary domain, compileBoundary codomain⟩

/-! ## Compilation facts -/

@[simp] theorem compileBoundary_any : compileBoundary .any = .unknown := rfl

@[simp] theorem normalizeBoundary_unknown :
    normalizeBoundary .unknown = .unknown := rfl

@[simp] theorem normalizeBoundary_negClass :
    normalizeBoundary (.negClass cname) = .negClass cname := rfl

theorem normalizeBoundary_union_unknown_left (c : BoundaryContract) :
    normalizeBoundary (.union .unknown c) = .unknown := by
  simp [normalizeBoundary]

theorem normalizeBoundary_union_unknown_right (c : BoundaryContract) :
    normalizeBoundary (.union c .unknown) = .unknown := by
  simp [normalizeBoundary]
  cases normalizeBoundary c <;> rfl

theorem normalizeBoundary_intersection_unknown_left (c : BoundaryContract) :
    normalizeBoundary (.intersection .unknown c) = normalizeBoundary c := by
  simp [normalizeBoundary]

theorem normalizeBoundary_intersection_unknown_right (c : BoundaryContract) :
    normalizeBoundary (.intersection c .unknown) = normalizeBoundary c := by
  simp [normalizeBoundary]
  cases normalizeBoundary c <;> rfl

