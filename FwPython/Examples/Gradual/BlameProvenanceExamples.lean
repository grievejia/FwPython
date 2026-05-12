import FwPython.Gradual.TypeSystem.Blame.Correctness

/-! # Blame Provenance Regression Examples

Exercises the blame provenance, blame correctness, and uniqueness APIs
introduced for compiled labels, together with the supporting lookup,
compilation, and registration lemmas. -/

open Checked

/-! ## Lookup uniqueness on an override chain -/

def overrideSpeakMammal : GMethod where
  name := "speak"
  receiverParam := "self"
  param := "arg"
  paramTy := .any
  returnTy := .any
  body := .constTrue

def overrideSpeakDog : GMethod where
  name := "speak"
  receiverParam := "self"
  param := "arg"
  paramTy := .any
  returnTy := .any
  body := .constFalse

def overrideObjectClass : GClass where
  name := objectClass
  baseClasses := []
  methods := []

def overrideMammalClass : GClass where
  name := "Mammal"
  baseClasses := [objectClass]
  methods := [overrideSpeakMammal]

def overrideDogClass : GClass where
  name := "Dog"
  baseClasses := ["Mammal"]
  methods := [overrideSpeakDog]

def overrideCt : GClassTable :=
  [overrideDogClass, overrideMammalClass, overrideObjectClass]

def overrideMro : List Identifier :=
  ["Dog", "Mammal", objectClass]

example
    {pre suf : List Identifier}
    {definer : Identifier}
    {d : GClass}
    {m : GMethod}
    (hotherEq : overrideMro = pre ++ definer :: suf)
    (hotherPrefix : ∀ cname ∈ pre, ∀ gc, findGClass overrideCt cname = some gc →
      findGMethodInList gc.methods "speak" = none)
    (hotherFind : findGClass overrideCt definer = some d)
    (hotherMethod : findGMethodInList d.methods "speak" = some m) :
    definer = "Dog" := by
  have hDogEq : overrideMro = [] ++ "Dog" :: ["Mammal", objectClass] := rfl
  have hDogPrefix :
      ∀ cname ∈ ([] : List Identifier), ∀ gc, findGClass overrideCt cname = some gc →
        findGMethodInList gc.methods "speak" = none := nofun
  have hDogFind : findGClass overrideCt "Dog" = some overrideDogClass := by native_decide
  have hDogMethod : findGMethodInList overrideDogClass.methods "speak" = some overrideSpeakDog := by
    native_decide
  have hdef := findGMethodInMro_first_definer_unique
    (ct := overrideCt)
    hDogEq
    hDogPrefix
    hDogFind
    hDogMethod
    hotherEq
    hotherPrefix
    hotherFind
    hotherMethod
  simpa using hdef.symm

/-! ## Site injectivity and label erasure -/

def nestedContract : BoundaryContract :=
  .callable
    (.intersection .unknown (.class_ "Dog"))
    (.intersection (.callable .unknown .bottom) (.class_ "Cat"))

example
    {p₁ p₂ : BoundaryPath nestedContract}
    (hsite :
      (((mkBoundaryLabels .main .positive nestedContract 7).1).at p₁).site =
        (((mkBoundaryLabels .main .positive nestedContract 7).1).at p₂).site) :
    p₁ = p₂ :=
  (mkBoundaryLabels_at_site_eq_iff_path_eq
    (scope := .main)
    (pol := .positive)
    (c := nestedContract)
    (n := 7)).1 hsite

example
    (hwfct : WellFormedGClassTableCore gct)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    eraseLabelsExpr (compileCheck .main hsrc Δ1 P n1).1 =
      eraseLabelsExpr (compileCheck (.methodBody "Dog" "speak") hsrc Δ2 P n2).1 :=
  compileCheck_eraseLabels_congr .main (.methodBody "Dog" "speak") hsrc

example :
    (((.callableDomain (.intersectionRight .here)) : BoundaryPath nestedContract).ownerFrom
      .positive) = .context := by
  native_decide

example :
    (((mkBoundaryLabels .main .positive nestedContract 7).1).at
      ((.callableDomain (.intersectionRight .here)) : BoundaryPath nestedContract)).owner =
        (((.callableDomain (.intersectionRight .here)) : BoundaryPath nestedContract).ownerFrom
          .positive) := by
  native_decide

example
    (hwfct : WellFormedGClassTableCore gct)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy)
    (hnode :
      (compileCheck .main hsrc Δ P n).1.nodeAt exprPath = some (.dynAttrAccess e' attr ℓ)) :
    ∃ k, ℓ = (freshLabel .main .context k).1 :=
  compileCheck_dynAttr_label_form .main hsrc hnode

/-! ## Registration helpers -/

def subtreeContract : BoundaryContract :=
  .intersection
    (.class_ "Dog")
    (.callable .unknown (.intersection .unknown .bottom))

example
    (hcompiled : ElaboratesProgramAt gp P cp)
    (labels : BoundaryLabels subtreeContract)
    (hlabels : BoundaryLabelsRegistered hcompiled labels) :
    BoundaryLabelsRegistered hcompiled
      (labels.subtree (.intersectionRight (.callableCodomain (.intersectionLeft .here)))) :=
  boundaryLabels_subtree_registered hlabels

example
    (hcompiled : ElaboratesProgramAt gp P cp)
    {U : BoundaryContract}
    {labels : BoundaryLabels (.intersection .unknown U)}
    (hlabels : BoundaryLabelsRegistered hcompiled labels)
    (hheap : HeapLabelsRegistered hcompiled heap)
    (hv : CheckedValueLabelsRegistered hcompiled v)
    (hU : EnforceValue gp.classes heap v U
      (labels.subtree (.intersectionRight .here)) (.ok v')) :
    CheckedValueLabelsRegistered hcompiled v' :=
  enforceValue_ok_registered hcompiled hlabels hheap hv
    (.intersectionOk .unknown hU) _ rfl

/-! ## Step preservation through attribute access -/

example
    (hcompiled : ElaboratesProgramAt gp P cp)
    (hreg : StateLabelsRegistered hcompiled
      { heap, env, control := .val (.objRef objOid),
        continuation := .attrAccess attrName :: k })
    (hlook : heap.lookup objOid = some obj)
    (hfind : findGClass gp.classes obj.className = some c)
    (hmro : GComputeMro gp.classes c mro)
    (hmethod : findCheckedMethodInMro cp.classes mro attrName = some cm)
    (halloc : heap.alloc ⟨boundMethodClass, .boundMethod objOid cm⟩ = (bmOid, heap')) :
    StateLabelsRegistered hcompiled
      { heap := heap', env, control := .val (.objRef bmOid), continuation := k } :=
  step_preserves_registered hcompiled hreg
    (.returnAttrAccess hlook hfind hmro hmethod halloc)

/-! ## End-to-end final blame provenance -/

example
    (hcompiled : ElaboratesProgramAt gp P cp)
    (hsteps : Steps gp.classes cp.classes (initialState cp) finalState)
    (hfinal : finalResult? finalState = some (heap', .blame ℓ)) :
    ∃ origin, CompiledBoundaryOrigin hcompiled origin ℓ :=
  gradual_blame_provenance_at hcompiled hsteps hfinal

example
    (hcompiled : ElaboratesProgramAt gp P cp)
    (horig : CompiledBoundaryOrigin hcompiled origin ℓ) :
    BoundaryOrigin.expectedOwner origin = ℓ.owner :=
  compiled_boundary_origin_expectedOwner hcompiled horig

example
    (hcompiled : ElaboratesProgramAt gp P cp)
    (hsteps : Steps gp.classes cp.classes (initialState cp) finalState)
    (hfinal : finalResult? finalState = some (heap', .blame ℓ)) :
    ∃ origin, CompiledBoundaryOrigin hcompiled origin ℓ ∧
      BoundaryOrigin.expectedOwner origin = ℓ.owner :=
  gradual_blame_correctness_at hcompiled hsteps hfinal
