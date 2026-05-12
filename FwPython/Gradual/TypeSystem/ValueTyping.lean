import FwPython.Gradual.TypeSystem.Checked.Typing
import FwPython.Gradual.Checked.Core

/-! ## Exact positive operational views -/

/-- Exact positive evidence that a value is shallowly callable. -/
inductive CheckedCallableView :
    GClassTable → CheckedClassTable → CheckedHeap → CheckedValue → Prop where
  | objRefBoundMethod :
      heap.lookup oid = some ⟨boundMethodClass, .boundMethod recvOid cm⟩ →
      heap.lookup recvOid = some recvObj →
      CheckedMethodInReceiverMro gct cct recvObj.className cm →
      CheckedCallableView gct cct heap (.objRef oid)

/-- Minimal positive runtime-shape evidence. -/
inductive CheckedAnyShape :
    GClassTable → CheckedClassTable → CheckedHeap → CheckedValue → Prop where
  | objRef :
      heap.lookup oid = some obj →
      CheckedAnyShape gct cct heap (.objRef oid)

/-- Exact positive evidence that a value presents class `cname`. -/
inductive CheckedClassView :
    GClassTable → CheckedClassTable → CheckedHeap → CheckedValue → Identifier → Prop where
  | objRef :
      heap.lookup oid = some obj →
      findGClass gct obj.className = some cls →
      GComputeMro gct cls mro →
      cname ∈ mro →
      CheckedClassView gct cct heap (.objRef oid) cname

/-! ## Checked value witness -/

mutual
  /-- A checked value witness at type `G` bundles well-formedness of `G`
      with a structural decomposition into atomic witnesses. -/
  inductive CheckedValueWitness :
      GClassTable → CheckedClassTable → CheckedHeap →
      CheckedValue → GTy → Prop where
    | mk :
        WellFormedGTy gct G →
        CheckedValueWitnessData gct cct heap v G →
        CheckedValueWitness gct cct heap v G

  /-- The data payload of a checked value witness. Atomic payloads store
      exact positive view evidence. -/
  inductive CheckedValueWitnessData :
      GClassTable → CheckedClassTable → CheckedHeap →
      CheckedValue → GTy → Prop where
    | any :
        CheckedAnyShape gct cct heap v →
        CheckedValueWitnessData gct cct heap v .any
    | class_ :
        CheckedClassView gct cct heap v cname →
        CheckedValueWitnessData gct cct heap v (.class_ cname)
    | callable :
        CheckedCallableView gct cct heap v →
        CheckedValueWitnessData gct cct heap v (.callable P R)
    | unionLeft :
        CheckedValueWitness gct cct heap v G →
        CheckedValueWitnessData gct cct heap v (.union G H)
    | unionRight :
        CheckedValueWitness gct cct heap v H →
        CheckedValueWitnessData gct cct heap v (.union G H)
    | intersection :
        CheckedValueWitness gct cct heap v G →
        CheckedValueWitness gct cct heap v H →
        CheckedValueWitnessData gct cct heap v (.intersection G H)
    | negClass :
        CheckedAnyShape gct cct heap v →
        (∀ ℓ, EnforceValue gct heap v (compileBoundaryRaw (.negClass cname)) ℓ (.ok v)) →
        CheckedValueWitnessData gct cct heap v (.negClass cname)
end

def CheckedValueWitness.wf : CheckedValueWitness gct cct heap v G → WellFormedGTy gct G
  | .mk h _ => h

def CheckedValueWitness.data :
    CheckedValueWitness gct cct heap v G → CheckedValueWitnessData gct cct heap v G
  | .mk _ d => d

/-! ## View-to-shape projections -/

/-- A class view projects to minimal runtime shape. -/
theorem checkedClassView_toShape :
    CheckedClassView gct cct heap v cname → CheckedAnyShape gct cct heap v
  | .objRef hlook .. => .objRef hlook

/-- A callable view projects to minimal runtime shape. -/
theorem checkedCallableView_toShape :
    CheckedCallableView gct cct heap v → CheckedAnyShape gct cct heap v
  | .objRefBoundMethod hlook .. => .objRef hlook

/-! ## Witness-to-shape projection -/

/-- Total projection from any witness to runtime shape. -/
theorem checkedValueWitness_toShape :
    CheckedValueWitness gct cct heap v G → CheckedAnyShape gct cct heap v
  | .mk _ (.any hshape) => hshape
  | .mk _ (.class_ hview) => checkedClassView_toShape hview
  | .mk _ (.callable hview) => checkedCallableView_toShape hview
  | .mk _ (.negClass hshape _) => hshape
  | .mk _ (.unionLeft wG) => checkedValueWitness_toShape wG
  | .mk _ (.unionRight wH) => checkedValueWitness_toShape wH
  | .mk _ (.intersection wG _) => checkedValueWitness_toShape wG

/-! ## Shape-based runtime extraction -/

/-- An objRef shape guarantees heap lookup. -/
theorem checkedAnyShape_objRef_lookup
    (hshape : CheckedAnyShape gct cct heap v) (hv : v = .objRef oid) :
    ∃ obj, heap.lookup oid = some obj := by
  subst hv; let .objRef hlook := hshape; exact ⟨_, hlook⟩

/-- Witness-specialized: an objRef with a witness has heap lookup. -/
theorem checkedValueWitness_objRef_lookup
    (w : CheckedValueWitness gct cct heap v G) (hv : v = .objRef oid) :
    ∃ obj, heap.lookup oid = some obj :=
  checkedAnyShape_objRef_lookup (checkedValueWitness_toShape w) hv

/-! ## Atomic positive witness projections -/

/-- A witness at `.class_ cname` carries a class view. -/
theorem checkedValueWitness_class_view :
    CheckedValueWitness gct cct heap v (.class_ cname) → CheckedClassView gct cct heap v cname
  | .mk _ (.class_ hview) => hview

/-- A witness at `.callable P R` carries a callable view. -/
theorem checkedValueWitness_callable_view :
    CheckedValueWitness gct cct heap v (.callable P R) → CheckedCallableView gct cct heap v
  | .mk _ (.callable hview) => hview

/-! ## Environment typing -/

/-- The checked runtime environment is well-typed w.r.t. a type environment. -/
def CheckedEnvHasType (gct : GClassTable) (cct : CheckedClassTable) (heap : CheckedHeap)
    (env : CheckedEnv) (Γ : CheckedTyEnv) : Prop := ∀ x G, Γ.lookup x = some G →
  ∃ v, env.lookup x = some v ∧ CheckedValueWitness gct cct heap v G
