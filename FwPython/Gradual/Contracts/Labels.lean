import FwPython.Gradual.Contracts.Paths

/-! ## Label generation -/

/-- Allocate a single fresh label. -/
def freshLabel (scope : LabelScope) (owner : BlameOwner) (n : Nat) : Label × Nat :=
  ({ scope, site := n, owner }, n + 1)

theorem freshLabel_owner : (freshLabel scope owner n).1.owner = owner := by
  simp [freshLabel]

/-- Generate a full tree of boundary labels with a contiguous site interval. -/
def mkBoundaryLabels (scope : LabelScope) (pol : BoundaryPolarity) :
    (c : BoundaryContract) → Nat → BoundaryLabels c × Nat
  | .unknown, n =>
      let (ℓ, n') := freshLabel scope (BlameOwner.ofPolarity pol) n
      (.unknown ℓ, n')
  | .class_ _cname, n =>
      let (ℓ, n') := freshLabel scope (BlameOwner.ofPolarity pol) n
      (.class_ ℓ, n')
  | .callable domC codC, n =>
      let root := (freshLabel scope (BlameOwner.ofPolarity pol) n).1
      let domLabels := (mkBoundaryLabels scope pol.flip domC (n + 1)).1
      let codLabels := (mkBoundaryLabels scope pol codC (n + 1 + domC.labelCount)).1
      (.callable root domLabels codLabels,
        n + (BoundaryContract.callable domC codC).labelCount)
  | .union c₁ c₂, n =>
      let root := (freshLabel scope (BlameOwner.ofPolarity pol) n).1
      let leftLabels := (mkBoundaryLabels scope pol c₁ (n + 1)).1
      let rightLabels := (mkBoundaryLabels scope pol c₂ (n + 1 + c₁.labelCount)).1
      (.union root leftLabels rightLabels,
        n + (BoundaryContract.union c₁ c₂).labelCount)
  | .intersection c₁ c₂, n =>
      let root := (freshLabel scope (BlameOwner.ofPolarity pol) n).1
      let leftLabels := (mkBoundaryLabels scope pol c₁ (n + 1)).1
      let rightLabels := (mkBoundaryLabels scope pol c₂ (n + 1 + c₁.labelCount)).1
      (.intersection root leftLabels rightLabels,
        n + (BoundaryContract.intersection c₁ c₂).labelCount)
  | .bottom, n =>
      let (ℓ, n') := freshLabel scope (BlameOwner.ofPolarity pol) n
      (.bottom ℓ, n')
  | .negClass _cname, n =>
      let (ℓ, n') := freshLabel scope (BlameOwner.ofPolarity pol) n
      (.negClass ℓ, n')

@[simp] theorem mkBoundaryLabels_next :
    (mkBoundaryLabels scope pol c n).2 = n + c.labelCount := by
  cases c <;> simp [mkBoundaryLabels, BoundaryContract.labelCount, freshLabel]

theorem mkBoundaryLabels_scope_fixed :
    ∀ (c : BoundaryContract) (p : BoundaryPath c)
      (scope : LabelScope) (pol : BoundaryPolarity) (n : Nat),
      (((mkBoundaryLabels scope pol c n).1).at p).scope = scope
  | c, .here, _, _, _ => by
      cases c <;> simp [mkBoundaryLabels, BoundaryLabels.at, freshLabel]
  | .callable domC _, .callableDomain p, scope, pol, n => by
      simpa [mkBoundaryLabels, BoundaryLabels.at] using
        mkBoundaryLabels_scope_fixed domC p scope pol.flip (n + 1)
  | .callable _ codC, .callableCodomain p, scope, pol, n => by
      simpa [mkBoundaryLabels, BoundaryLabels.at] using
        mkBoundaryLabels_scope_fixed codC p scope pol (n + 1 + _)
  | .union c₁ _, .unionLeft p, scope, pol, n => by
      simpa [mkBoundaryLabels, BoundaryLabels.at] using
        mkBoundaryLabels_scope_fixed c₁ p scope pol (n + 1)
  | .union _ c₂, .unionRight p, scope, pol, n => by
      simpa [mkBoundaryLabels, BoundaryLabels.at] using
        mkBoundaryLabels_scope_fixed c₂ p scope pol (n + 1 + _)
  | .intersection c₁ _, .intersectionLeft p, scope, pol, n => by
      simpa [mkBoundaryLabels, BoundaryLabels.at] using
        mkBoundaryLabels_scope_fixed c₁ p scope pol (n + 1)
  | .intersection _ c₂, .intersectionRight p, scope, pol, n => by
      simpa [mkBoundaryLabels, BoundaryLabels.at] using
        mkBoundaryLabels_scope_fixed c₂ p scope pol (n + 1 + _)

theorem mkBoundaryLabels_at_owner :
    ∀ (c : BoundaryContract) (p : BoundaryPath c)
      (scope : LabelScope) (pol : BoundaryPolarity) (n : Nat),
      (((mkBoundaryLabels scope pol c n).1).at p).owner = p.ownerFrom pol
  | c, .here, _, _, _ => by
      cases c <;> simp [mkBoundaryLabels, BoundaryLabels.at, freshLabel, BoundaryPath.ownerFrom]
  | .callable domC _, .callableDomain p, scope, pol, n => by
      simpa [mkBoundaryLabels, BoundaryLabels.at, BoundaryPath.ownerFrom] using
        mkBoundaryLabels_at_owner domC p scope pol.flip (n + 1)
  | .callable _ codC, .callableCodomain p, scope, pol, n => by
      simpa [mkBoundaryLabels, BoundaryLabels.at, BoundaryPath.ownerFrom] using
        mkBoundaryLabels_at_owner codC p scope pol (n + 1 + _)
  | .union c₁ _, .unionLeft p, scope, pol, n => by
      simpa [mkBoundaryLabels, BoundaryLabels.at, BoundaryPath.ownerFrom] using
        mkBoundaryLabels_at_owner c₁ p scope pol (n + 1)
  | .union _ c₂, .unionRight p, scope, pol, n => by
      simpa [mkBoundaryLabels, BoundaryLabels.at, BoundaryPath.ownerFrom] using
        mkBoundaryLabels_at_owner c₂ p scope pol (n + 1 + _)
  | .intersection c₁ _, .intersectionLeft p, scope, pol, n => by
      simpa [mkBoundaryLabels, BoundaryLabels.at, BoundaryPath.ownerFrom] using
        mkBoundaryLabels_at_owner c₁ p scope pol (n + 1)
  | .intersection _ c₂, .intersectionRight p, scope, pol, n => by
      simpa [mkBoundaryLabels, BoundaryLabels.at, BoundaryPath.ownerFrom] using
        mkBoundaryLabels_at_owner c₂ p scope pol (n + 1 + _)

theorem mkBoundaryLabels_at_site :
    ∀ (c : BoundaryContract) (p : BoundaryPath c)
      (scope : LabelScope) (pol : BoundaryPolarity) (n : Nat),
      (((mkBoundaryLabels scope pol c n).1).at p).site = n + p.offset
  | c, .here, _, _, _ => by
      cases c <;> simp [mkBoundaryLabels, BoundaryLabels.at, BoundaryPath.offset, freshLabel]
  | .callable domC _, .callableDomain p, scope, pol, n => by
      have ih := mkBoundaryLabels_at_site domC p scope pol.flip (n + 1)
      simp [mkBoundaryLabels, BoundaryLabels.at, BoundaryPath.offset] at ih ⊢
      omega
  | .callable domC codC, .callableCodomain p, scope, pol, n => by
      have ih := mkBoundaryLabels_at_site codC p scope pol (n + 1 + domC.labelCount)
      simp [mkBoundaryLabels, BoundaryLabels.at, BoundaryPath.offset] at ih ⊢
      omega
  | .union c₁ _, .unionLeft p, scope, pol, n => by
      have ih := mkBoundaryLabels_at_site c₁ p scope pol (n + 1)
      simp [mkBoundaryLabels, BoundaryLabels.at, BoundaryPath.offset] at ih ⊢
      omega
  | .union c₁ c₂, .unionRight p, scope, pol, n => by
      have ih := mkBoundaryLabels_at_site c₂ p scope pol (n + 1 + c₁.labelCount)
      simp [mkBoundaryLabels, BoundaryLabels.at, BoundaryPath.offset] at ih ⊢
      omega
  | .intersection c₁ _, .intersectionLeft p, scope, pol, n => by
      have ih := mkBoundaryLabels_at_site c₁ p scope pol (n + 1)
      simp [mkBoundaryLabels, BoundaryLabels.at, BoundaryPath.offset] at ih ⊢
      omega
  | .intersection c₁ c₂, .intersectionRight p, scope, pol, n => by
      have ih := mkBoundaryLabels_at_site c₂ p scope pol (n + 1 + c₁.labelCount)
      simp [mkBoundaryLabels, BoundaryLabels.at, BoundaryPath.offset] at ih ⊢
      omega

theorem mkBoundaryLabels_interval :
    n ≤ (((mkBoundaryLabels scope pol c n).1).at p).site ∧
      (((mkBoundaryLabels scope pol c n).1).at p).site < (mkBoundaryLabels scope pol c n).2 := by
  rw [mkBoundaryLabels_at_site c p scope pol n, mkBoundaryLabels_next]
  have hlt := BoundaryPath.offset_lt_count p
  exact ⟨Nat.le_add_right n p.offset, Nat.add_lt_add_left hlt n⟩

theorem mkBoundaryLabels_at_site_eq_iff_path_eq
    {p₁ p₂ : BoundaryPath c} :
    (((mkBoundaryLabels scope pol c n).1).at p₁).site =
        (((mkBoundaryLabels scope pol c n).1).at p₂).site ↔
      p₁ = p₂ := by
  constructor
  · intro hsite
    rw [mkBoundaryLabels_at_site c p₁ scope pol n, mkBoundaryLabels_at_site c p₂ scope pol n] at hsite
    apply BoundaryPath.offset_injective
    omega
  · intro hpath
    cases hpath
    rfl

theorem mkBoundaryLabels_at_eq_iff_path_eq
    {p₁ p₂ : BoundaryPath c} :
    ((mkBoundaryLabels scope pol c n).1).at p₁ =
        ((mkBoundaryLabels scope pol c n).1).at p₂ ↔
      p₁ = p₂ := by
  constructor
  · intro hlabel
    apply (mkBoundaryLabels_at_site_eq_iff_path_eq (scope := scope) (pol := pol) (n := n)).1
    exact congrArg Label.site hlabel
  · intro hpath
    cases hpath
    rfl

theorem mkBoundaryLabels_intervals_disjoint
    {c₁ c₂ : BoundaryContract}
    {p₁ : BoundaryPath c₁} {p₂ : BoundaryPath c₂}
    (hdisjoint : (mkBoundaryLabels scope₁ pol₁ c₁ n₁).2 ≤ n₂) :
    (((mkBoundaryLabels scope₁ pol₁ c₁ n₁).1).at p₁).site ≠
      (((mkBoundaryLabels scope₂ pol₂ c₂ n₂).1).at p₂).site := by
  intro hsite
  have hleft := (mkBoundaryLabels_interval (scope := scope₁) (pol := pol₁) (c := c₁) (n := n₁)
    (p := p₁)).2
  have hright := (mkBoundaryLabels_interval (scope := scope₂) (pol := pol₂) (c := c₂) (n := n₂)
    (p := p₂)).1
  rw [hsite] at hleft
  omega

/-! ## Callable coercions -/

/-- A callable coercion mediates between two callable boundary contracts,
    storing only the tree of target-side labels. Domain and codomain
    subtrees are recovered from this tree. -/
structure CallableCoercion where
  source : CallableBoundaryContract
  target : CallableBoundaryContract
  targetLabels : BoundaryLabels (.callable target.domain target.codomain)
  deriving DecidableEq, Repr

/-- Parameter labels are the domain subtree of the target callable labels. -/
def CallableCoercion.parameterLabels (coercion : CallableCoercion) :
    BoundaryLabels coercion.target.domain :=
  coercion.targetLabels.subtree (.callableDomain .here)

/-- Return labels are the codomain subtree of the target callable labels. -/
def CallableCoercion.returnLabels (coercion : CallableCoercion) :
    BoundaryLabels coercion.target.codomain :=
  coercion.targetLabels.subtree (.callableCodomain .here)

/-- Two callable coercions are compatible for composition when the inner
    coercion's target matches the outer coercion's source. -/
def CallableCoercion.Compatible (outer inner : CallableCoercion) : Prop :=
  outer.source = inner.target

/-- Compose two callable coercions, producing the overall source-to-target
    mediation of a two-layer wrapper chain. Label ownership stays with the
    outer target boundary. -/
def composeCallableCoercion (outer inner : CallableCoercion) : CallableCoercion where
  source := inner.source
  target := outer.target
  targetLabels := outer.targetLabels

theorem CallableCoercion.Compatible.compose_inner
    {a b c : CallableCoercion}
    (hab : a.Compatible b) (_hbc : b.Compatible c) :
    a.Compatible (composeCallableCoercion b c) :=
  hab

theorem CallableCoercion.Compatible.compose_outer
    {a b c : CallableCoercion}
    (_hab : a.Compatible b) (hbc : b.Compatible c) :
    (composeCallableCoercion a b).Compatible c :=
  hbc

/-- Callable coercion composition is associative. -/
theorem composeCallableCoercion_assoc (a b c : CallableCoercion) :
    composeCallableCoercion a (composeCallableCoercion b c) =
      composeCallableCoercion (composeCallableCoercion a b) c := rfl
