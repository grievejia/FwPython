import FwPython.Gradual.Contracts.Core

/-! ## Dependent paths through boundary contracts -/

/-- The total number of labels stored in a boundary tree for `c`. -/
def BoundaryContract.labelCount : BoundaryContract → Nat
  | .unknown => 1
  | .class_ _ => 1
  | .callable domC codC => 1 + domC.labelCount + codC.labelCount
  | .union c₁ c₂ => 1 + c₁.labelCount + c₂.labelCount
  | .intersection c₁ c₂ => 1 + c₁.labelCount + c₂.labelCount
  | .bottom => 1
  | .negClass _ => 1

/-- A path to a subcontract of `c`. Leaves admit only `.here`. -/
inductive BoundaryPath : (c : BoundaryContract) → Type where
  | here : BoundaryPath c
  | callableDomain :
      BoundaryPath domC → BoundaryPath (.callable domC codC)
  | callableCodomain :
      BoundaryPath codC → BoundaryPath (.callable domC codC)
  | unionLeft :
      BoundaryPath c₁ → BoundaryPath (.union c₁ c₂)
  | unionRight :
      BoundaryPath c₂ → BoundaryPath (.union c₁ c₂)
  | intersectionLeft :
      BoundaryPath c₁ → BoundaryPath (.intersection c₁ c₂)
  | intersectionRight :
      BoundaryPath c₂ → BoundaryPath (.intersection c₁ c₂)
  deriving DecidableEq, Repr

/-- The subcontract reached by a path. -/
def subContract : (c : BoundaryContract) → BoundaryPath c → BoundaryContract
  | c, .here => c
  | .callable domC _codC, .callableDomain p => subContract domC p
  | .callable _domC codC, .callableCodomain p => subContract codC p
  | .union c₁ _c₂, .unionLeft p => subContract c₁ p
  | .union _c₁ c₂, .unionRight p => subContract c₂ p
  | .intersection c₁ _c₂, .intersectionLeft p => subContract c₁ p
  | .intersection _c₁ c₂, .intersectionRight p => subContract c₂ p

/-- Append a path inside a subtree to the outer path reaching that subtree. -/
def BoundaryPath.append : (p : BoundaryPath c) →
    BoundaryPath (subContract c p) → BoundaryPath c
  | .here, q => q
  | .callableDomain p, q => .callableDomain (p.append q)
  | .callableCodomain p, q => .callableCodomain (p.append q)
  | .unionLeft p, q => .unionLeft (p.append q)
  | .unionRight p, q => .unionRight (p.append q)
  | .intersectionLeft p, q => .intersectionLeft (p.append q)
  | .intersectionRight p, q => .intersectionRight (p.append q)

/-- Compute the blame polarity at a boundary subtree. -/
def BoundaryPath.polarityFrom (rootPol : BoundaryPolarity) : BoundaryPath c → BoundaryPolarity
  | .here => rootPol
  | .callableDomain p => p.polarityFrom rootPol.flip
  | .callableCodomain p => p.polarityFrom rootPol
  | .unionLeft p => p.polarityFrom rootPol
  | .unionRight p => p.polarityFrom rootPol
  | .intersectionLeft p => p.polarityFrom rootPol
  | .intersectionRight p => p.polarityFrom rootPol

/-- Compute the blame owner at a boundary subtree. -/
def BoundaryPath.ownerFrom (rootPol : BoundaryPolarity) (p : BoundaryPath c) : BlameOwner :=
  BlameOwner.ofPolarity (BoundaryPath.polarityFrom rootPol p)

@[simp] theorem BoundaryPath.polarityFrom_here
    (rootPol : BoundaryPolarity) :
    BoundaryPath.polarityFrom rootPol (.here : BoundaryPath c) = rootPol := rfl

@[simp] theorem BoundaryPath.polarityFrom_callableDomain
    (rootPol : BoundaryPolarity) (p : BoundaryPath domC) :
    BoundaryPath.polarityFrom rootPol (.callableDomain p : BoundaryPath (.callable domC codC)) =
      BoundaryPath.polarityFrom rootPol.flip p := rfl

@[simp] theorem BoundaryPath.polarityFrom_callableCodomain
    (rootPol : BoundaryPolarity) (p : BoundaryPath codC) :
    BoundaryPath.polarityFrom rootPol (.callableCodomain p : BoundaryPath (.callable domC codC)) =
      BoundaryPath.polarityFrom rootPol p := rfl

@[simp] theorem BoundaryPath.polarityFrom_unionLeft
    (rootPol : BoundaryPolarity) (p : BoundaryPath c₁) :
    BoundaryPath.polarityFrom rootPol (.unionLeft p : BoundaryPath (.union c₁ c₂)) =
      BoundaryPath.polarityFrom rootPol p := rfl

@[simp] theorem BoundaryPath.polarityFrom_unionRight
    (rootPol : BoundaryPolarity) (p : BoundaryPath c₂) :
    BoundaryPath.polarityFrom rootPol (.unionRight p : BoundaryPath (.union c₁ c₂)) =
      BoundaryPath.polarityFrom rootPol p := rfl

@[simp] theorem BoundaryPath.polarityFrom_intersectionLeft
    (rootPol : BoundaryPolarity) (p : BoundaryPath c₁) :
    BoundaryPath.polarityFrom rootPol (.intersectionLeft p : BoundaryPath (.intersection c₁ c₂)) =
      BoundaryPath.polarityFrom rootPol p := rfl

@[simp] theorem BoundaryPath.polarityFrom_intersectionRight
    (rootPol : BoundaryPolarity) (p : BoundaryPath c₂) :
    BoundaryPath.polarityFrom rootPol (.intersectionRight p : BoundaryPath (.intersection c₁ c₂)) =
      BoundaryPath.polarityFrom rootPol p := rfl

/-- The preorder position of a path inside its contract tree. -/
def BoundaryPath.offset : (p : BoundaryPath c) → Nat
  | .here => 0
  | @BoundaryPath.callableDomain domC _codC p => 1 + p.offset
  | @BoundaryPath.callableCodomain _codC domC p => 1 + domC.labelCount + p.offset
  | @BoundaryPath.unionLeft c₁ _c₂ p => 1 + p.offset
  | @BoundaryPath.unionRight _c₂ c₁ p => 1 + c₁.labelCount + p.offset
  | @BoundaryPath.intersectionLeft c₁ _c₂ p => 1 + p.offset
  | @BoundaryPath.intersectionRight _c₂ c₁ p => 1 + c₁.labelCount + p.offset

theorem BoundaryPath.offset_lt_count : (p : BoundaryPath c) → p.offset < c.labelCount
  | .here => by cases c <;> simp [BoundaryPath.offset, BoundaryContract.labelCount] <;> omega
  | .callableDomain p | .callableCodomain p | .unionLeft p | .unionRight p
  | .intersectionLeft p | .intersectionRight p => by
      have ih := BoundaryPath.offset_lt_count p
      simp [BoundaryPath.offset, BoundaryContract.labelCount]; omega

theorem BoundaryPath.offset_injective
    {p₁ p₂ : BoundaryPath c} (h : p₁.offset = p₂.offset) : p₁ = p₂ := by
  cases c with
  | unknown | class_ _ | bottom | negClass _ => cases p₁; cases p₂; rfl
  | callable dom _ =>
      cases p₁ with
      | here =>
          cases p₂ with
          | here => rfl
          | callableDomain _ | callableCodomain _ => simp [BoundaryPath.offset] at h; omega
      | callableDomain p =>
          cases p₂ with
          | here => simp [BoundaryPath.offset] at h
          | callableDomain q =>
              simp [BoundaryPath.offset] at h
              exact congrArg BoundaryPath.callableDomain (BoundaryPath.offset_injective h)
          | callableCodomain q =>
              have := BoundaryPath.offset_lt_count p
              simp [BoundaryPath.offset] at h; omega
      | callableCodomain p =>
          cases p₂ with
          | here => simp [BoundaryPath.offset] at h
          | callableDomain q =>
              have := BoundaryPath.offset_lt_count q
              simp [BoundaryPath.offset] at h; omega
          | callableCodomain q =>
              simp [BoundaryPath.offset] at h
              exact congrArg BoundaryPath.callableCodomain (BoundaryPath.offset_injective h)
  | union c₁ _ =>
      cases p₁ with
      | here =>
          cases p₂ with
          | here => rfl
          | unionLeft _ | unionRight _ => simp [BoundaryPath.offset] at h; omega
      | unionLeft p =>
          cases p₂ with
          | here => simp [BoundaryPath.offset] at h
          | unionLeft q =>
              simp [BoundaryPath.offset] at h
              exact congrArg BoundaryPath.unionLeft (BoundaryPath.offset_injective h)
          | unionRight q =>
              have := BoundaryPath.offset_lt_count p
              simp [BoundaryPath.offset] at h; omega
      | unionRight p =>
          cases p₂ with
          | here => simp [BoundaryPath.offset] at h
          | unionLeft q =>
              have := BoundaryPath.offset_lt_count q
              simp [BoundaryPath.offset] at h; omega
          | unionRight q =>
              simp [BoundaryPath.offset] at h
              exact congrArg BoundaryPath.unionRight (BoundaryPath.offset_injective h)
  | intersection c₁ _ =>
      cases p₁ with
      | here =>
          cases p₂ with
          | here => rfl
          | intersectionLeft _ | intersectionRight _ => simp [BoundaryPath.offset] at h; omega
      | intersectionLeft p =>
          cases p₂ with
          | here => simp [BoundaryPath.offset] at h
          | intersectionLeft q =>
              simp [BoundaryPath.offset] at h
              exact congrArg BoundaryPath.intersectionLeft (BoundaryPath.offset_injective h)
          | intersectionRight q =>
              have := BoundaryPath.offset_lt_count p
              simp [BoundaryPath.offset] at h; omega
      | intersectionRight p =>
          cases p₂ with
          | here => simp [BoundaryPath.offset] at h
          | intersectionLeft q =>
              have := BoundaryPath.offset_lt_count q
              simp [BoundaryPath.offset] at h; omega
          | intersectionRight q =>
              simp [BoundaryPath.offset] at h
              exact congrArg BoundaryPath.intersectionRight (BoundaryPath.offset_injective h)

/-- A tree of labels matching the shape of a boundary contract. -/
inductive BoundaryLabels : (c : BoundaryContract) → Type where
  | unknown : Label → BoundaryLabels .unknown
  | class_ : Label → BoundaryLabels (.class_ cname)
  | callable :
      Label →
      BoundaryLabels domC →
      BoundaryLabels codC →
      BoundaryLabels (.callable domC codC)
  | union :
      Label →
      BoundaryLabels c₁ →
      BoundaryLabels c₂ →
      BoundaryLabels (.union c₁ c₂)
  | intersection :
      Label →
      BoundaryLabels c₁ →
      BoundaryLabels c₂ →
      BoundaryLabels (.intersection c₁ c₂)
  | bottom : Label → BoundaryLabels .bottom
  | negClass : Label → BoundaryLabels (.negClass cname)
  deriving DecidableEq, Repr

/-- Read the label at a path. -/
def BoundaryLabels.at : BoundaryLabels c → BoundaryPath c → Label
  | .unknown ℓ, .here => ℓ
  | .class_ ℓ, .here => ℓ
  | .callable ℓ _ _, .here => ℓ
  | .callable _ domLabels _codLabels, .callableDomain p => domLabels.at p
  | .callable _ _domLabels codLabels, .callableCodomain p => codLabels.at p
  | .union ℓ _ _, .here => ℓ
  | .union _ leftLabels _rightLabels, .unionLeft p => leftLabels.at p
  | .union _ _leftLabels rightLabels, .unionRight p => rightLabels.at p
  | .intersection ℓ _ _, .here => ℓ
  | .intersection _ leftLabels _rightLabels, .intersectionLeft p => leftLabels.at p
  | .intersection _ _leftLabels rightLabels, .intersectionRight p => rightLabels.at p
  | .bottom ℓ, .here => ℓ
  | .negClass ℓ, .here => ℓ

/-- The root label of a boundary tree. -/
def BoundaryLabels.direct (labels : BoundaryLabels c) : Label :=
  labels.at .here

/-- Exact containment specification for a label inside a boundary tree. -/
def BoundaryLabels.contains (labels : BoundaryLabels c) (ℓ : Label) : Prop :=
  ∃ p, labels.at p = ℓ

/-- Restrict a boundary-label tree to a subtree. -/
def BoundaryLabels.subtree : BoundaryLabels c → (p : BoundaryPath c) → BoundaryLabels (subContract c p)
  | labels, .here => labels
  | .callable _ domLabels _codLabels, .callableDomain p => domLabels.subtree p
  | .callable _ _domLabels codLabels, .callableCodomain p => codLabels.subtree p
  | .union _ leftLabels _rightLabels, .unionLeft p => leftLabels.subtree p
  | .union _ _leftLabels rightLabels, .unionRight p => rightLabels.subtree p
  | .intersection _ leftLabels _rightLabels, .intersectionLeft p => leftLabels.subtree p
  | .intersection _ _leftLabels rightLabels, .intersectionRight p => rightLabels.subtree p

theorem BoundaryLabels.at_subtree :
    ∀ (labels : BoundaryLabels c) (p : BoundaryPath c) (q : BoundaryPath (subContract c p)),
      (labels.subtree p).at q = labels.at (BoundaryPath.append p q)
  | labels, .here, q => by
      simp [BoundaryLabels.subtree, BoundaryPath.append, subContract]
  | .callable _ domLabels _codLabels, .callableDomain p, q =>
      BoundaryLabels.at_subtree domLabels p q
  | .callable _ _domLabels codLabels, .callableCodomain p, q =>
      BoundaryLabels.at_subtree codLabels p q
  | .union _ leftLabels _rightLabels, .unionLeft p, q =>
      BoundaryLabels.at_subtree leftLabels p q
  | .union _ _leftLabels rightLabels, .unionRight p, q =>
      BoundaryLabels.at_subtree rightLabels p q
  | .intersection _ leftLabels _rightLabels, .intersectionLeft p, q =>
      BoundaryLabels.at_subtree leftLabels p q
  | .intersection _ _leftLabels rightLabels, .intersectionRight p, q =>
      BoundaryLabels.at_subtree rightLabels p q

theorem BoundaryLabels.at_cast
    {c c' : BoundaryContract}
    (h : c = c')
    (labels : BoundaryLabels c)
    (p : BoundaryPath c) :
    (cast (congrArg BoundaryLabels h) labels).at
        (cast (congrArg BoundaryPath h) p) =
      labels.at p := by
  cases h
  rfl

theorem BoundaryPath.polarityFrom_cast
    {c c' : BoundaryContract}
    (h : c = c')
    (rootPol : BoundaryPolarity)
    (p : BoundaryPath c) :
    (cast (congrArg BoundaryPath h) p).polarityFrom rootPol =
      p.polarityFrom rootPol := by
  cases h
  rfl

theorem BoundaryPath.ownerFrom_cast
    {c c' : BoundaryContract}
    (h : c = c')
    (rootPol : BoundaryPolarity)
    (p : BoundaryPath c) :
    (cast (congrArg BoundaryPath h) p).ownerFrom rootPol =
      p.ownerFrom rootPol := by
  cases h
  rfl

