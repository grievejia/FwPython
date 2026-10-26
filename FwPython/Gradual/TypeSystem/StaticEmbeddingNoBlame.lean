import FwPython.Gradual.TypeSystem.StaticEmbeddingBridge
import FwPython.Gradual.TypeSystem.CheckedTargetPrecision
import FwPython.Gradual.TypeSystem.Soundness
import FwPython.Gradual.TypeSystem.BlameAdequacy
import FwPython.Gradual.TypeSystem.IsInstanceRefinement
import FwPython.Gradual.TypeSystem.Preservation
import FwPython.Gradual.Checked.HeapPreservation

/-! # Static embedding no-blame

This module contains the runtime invariants proving that checked-machine blame
reached from an embedded static program satisfies the reported source
obligation. Blame adequacy then rules out such a final blame state.
-/

/-- Source provenance and compiler equalities for one checked method allocated
by embedded static method lookup. -/
private structure StaticMethodOrigin
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (cm : CheckedMethod) : Type where
  /-- Class name in the runtime receiver MRO that supplied the checked method. -/
  definingClassName : Identifier
  /-- Static method declaration compiled into the checked method. -/
  sourceMethod : Method
  /-- The source method parameter annotation is well formed in the static class table. -/
  parameter_wellFormed : WellFormedTy p.classes sourceMethod.paramTy
  /-- Checked receiver parameter name is the source receiver parameter name. -/
  receiverParam_eq : cm.receiverParam = sourceMethod.receiverParam
  /-- Checked argument parameter name is the source argument parameter name. -/
  param_eq : cm.param = sourceMethod.param
  /-- Checked argument target is the embedded source parameter annotation. -/
  paramTy_eq : cm.paramTy = checkedTargetOfGTy (embedTy sourceMethod.paramTy)
  /-- Checked return target is the embedded source return annotation. -/
  returnTy_eq : cm.returnTy = checkedTargetOfGTy (embedTy sourceMethod.returnTy)
  /-- Checked parameter obligation reports the source method-parameter site. -/
  parameterObligation_eq :
    cm.parameterObligation =
      .hasType (.methodParameter definingClassName sourceMethod.name)
        (embedTy sourceMethod.paramTy)
  /-- Checked return obligation reports the source method-return site. -/
  returnObligation_eq :
    cm.returnObligation =
      .hasType (.methodReturn definingClassName sourceMethod.name)
        (embedTy sourceMethod.returnTy)
  /-- Embedded source bridge that compiles into the checked method body. -/
  body_bridge :
    EmbeddedExprBridge p.classes helab.core
      [(sourceMethod.param, sourceMethod.paramTy),
       (sourceMethod.receiverParam, .class_ definingClassName)]
      sourceMethod.body
      sourceMethod.returnTy
  /-- Checked body is exactly the compiler output for `body_bridge`. -/
  body_eq :
    cm.body =
      compileCheck
        body_bridge.hsrc
        [(sourceMethod.param, embedTy sourceMethod.paramTy),
         (sourceMethod.receiverParam, .class_ definingClassName)]
        .any
        (.methodBody definingClassName sourceMethod.name [])

private def StaticMethodOrigin.ofExact
    (helab : EmbeddedStaticElaboration p)
    {recvMro : List Identifier}
    {attrName : Identifier}
    {sourceMethod : Method}
    {cm : CheckedMethod}
    (exact :
      ExactEmbeddedMethodLookup p helab.core helab.methodBodiesBridge
    helab.cp.classes helab.classesCompiled recvMro attrName
        sourceMethod cm) :
    StaticMethodOrigin p helab cm := by
  let sourceData := exact.source_data
  let definingClassName := exact.lookup.definingClassName
  let bodyBridge :=
    helab.methodBodiesBridge
      definingClassName
      sourceData.sourceClass
      sourceMethod
      sourceData.findClass_source
      sourceData.method_mem_source
  have hmethodWf :=
    helab.staticClassTable.hwf.allMethodSignaturesWellFormed
      definingClassName
      sourceData.sourceClass
      sourceMethod
      sourceData.findClass_source
      sourceData.method_mem_source
  refine
    { definingClassName := definingClassName
      sourceMethod := sourceMethod
      parameter_wellFormed := hmethodWf.1
      receiverParam_eq := ?_
      param_eq := ?_
      paramTy_eq := ?_
      returnTy_eq := ?_
      parameterObligation_eq := ?_
      returnObligation_eq := ?_
      body_bridge := bodyBridge
      body_eq := ?_ }
  all_goals (rw [exact.compiled_method_eq]; rfl)

/-- Static type embedding is injective. -/
private theorem embedTy_injective {T U : Ty}
    (h : embedTy T = embedTy U) :
    T = U := by
  calc
    T = lowerBound (embedTy T) := (embedTy_lowerBound T).symm
    _ = lowerBound (embedTy U) := congrArg lowerBound h
    _ = U := embedTy_lowerBound U

/-- Checked targets remain injective on embedded static types. -/
private theorem checkedTargetOfGTy_embedTy_injective {T U : Ty}
    (h : checkedTargetOfGTy (embedTy T) = checkedTargetOfGTy (embedTy U)) :
    T = U :=
  embedTy_injective (by simpa using congrArg interpTarget h)

private theorem gty_union_left_injective {left right left' right' : GTy}
    (h : GTy.union left right = GTy.union left' right') :
    left = left' := by
  injection h

private theorem gty_union_right_injective {left right left' right' : GTy}
    (h : GTy.union left right = GTy.union left' right') :
    right = right' := by
  injection h

private theorem staticMethodOrigin_same_checked_signature
    (left right : StaticMethodOrigin p helab cm) :
    left.sourceMethod.paramTy = right.sourceMethod.paramTy ∧
      left.sourceMethod.returnTy = right.sourceMethod.returnTy := by
  constructor
  · exact checkedTargetOfGTy_embedTy_injective
      (left.paramTy_eq.symm.trans right.paramTy_eq)
  · exact checkedTargetOfGTy_embedTy_injective
      (left.returnTy_eq.symm.trans right.returnTy_eq)

private theorem compiled_checkedMethodLookup_source_exists
    (helab : EmbeddedStaticElaboration p)
    (checked_lookup :
      findCheckedMethodInMro helab.cp.classes receiverMro methodName =
        some checkedMethod) :
    ∃ sourceMethod,
      findMethodInMro p.classes receiverMro methodName = some sourceMethod := by
  cases hsource :
      findGMethodInMro (embedClassTable p.classes) receiverMro methodName with
  | some _ =>
      obtain ⟨sourceMethod, source_lookup, _⟩ :=
        findMethodInMro_embed_reverse hsource
      exact ⟨sourceMethod, source_lookup⟩
  | none =>
      have checked_none :
          findCheckedMethodInMro helab.cp.classes receiverMro methodName = none := by
        exact
          findMemberInHierarchy_none_transport
            (findClass₁ := findGClass)
            (findClass₂ := findCheckedClass)
            (getMembers₁ := ClassDecl.methods)
            (getMembers₂ := CheckedClass.methods)
            (getName₁ := MethodDecl.name)
            (getName₂ := CheckedMethod.name)
            (ct₁ := embedClassTable p.classes)
            (ct₂ := helab.cp.classes)
            (hierarchy := receiverMro)
            (memberName := methodName)
            (RClass := fun sourceClass checkedClass =>
              Nonempty (Checked.IsCompiledClass
                (embedClassTable p.classes) helab.core sourceClass checkedClass))
            (classNone :=
              Checked.isCompiledClassTable_findClass_none helab.classesCompiled)
            (classSome := fun hfind =>
              let lookup :=
                Checked.isCompiledClassTable_findClass helab.classesCompiled hfind
              ⟨lookup.value, lookup.found, ⟨lookup.related⟩⟩)
            (memberNone := fun related hnone =>
              related.elim fun related =>
                Checked.isCompiledMethods_findMethod_none
                  related.methods_compiled hnone)
            hsource
      rw [checked_lookup] at checked_none
      cases checked_none

open FwPython.Static.Subtyping

/-- In a well-formed checked heap, the shallow predicate `CheckedValueSatisfies`
for a valid embedded annotation agrees with subtyping from the exact object's
lower bound under the hierarchy. The predicate's exclusion and callable
clauses can hold for annotations with unknown class names, while subtyping
requires known class names throughout. -/
private theorem checkedValueSatisfies_lowerBound (structural : WellFormedClassHierarchy ct)
    (hheap : CheckedHeapWellFormed (embedClassTable ct) cct heap)
    (lookup : heap.lookup oid = some obj)
    {type : Ty} (valid : WellFormedTy ct type) :
    let classKnown : obj.className ∈ ct.map ClassDecl.name := by
      obtain ⟨_, _, found, _⟩ := hheap.classesExist _ _ lookup
      obtain ⟨_, original, _⟩ := findClass_embedClassTable_reverse found
      exact findClass_name_known original
    CheckedValueSatisfies (embedClassTable ct) cct heap (.objRef oid)
      (checkedTargetOfGTy (embedTy type)) ↔
      IsSubtype structural
        (objectTypeLowerBound structural obj.className classKnown).raw type := by
  intro classKnown
  -- Each successful embedded lookup computes the object's static-context MRO.
  have mroEquation {declaration : GClass} {linearization : List Identifier}
      (found : findGClass (embedClassTable ct) obj.className = some declaration)
      (computed : GComputeMro (embedClassTable ct) declaration linearization) :
      structural.typeContext.ancestors obj.className = linearization := by
    obtain ⟨_, original, equal⟩ := findClass_embedClassTable_reverse found
    cases equal
    exact structural.typeContext_mro original
      (computeMro_embedClassTable_reverse original computed)
  -- Validity evidence supplies the known class names of every child annotation.
  induction valid with
  | bottom =>
      constructor
      · intro satisfied
        cases satisfied
      · intro included
        exact objectTypeLowerBound_nonempty structural obj.className classKnown included
  | union leftKnown rightKnown leftInduction rightInduction =>
      rw [objectTypeLowerBound_union_iff structural obj.className classKnown
        (.union leftKnown rightKnown)]
      exact or_congr leftInduction rightInduction
  | intersection _ _ leftInduction rightInduction =>
      rw [subtype_inter_iff]
      exact and_congr leftInduction rightInduction
  | class_ =>
      constructor
      · intro satisfied
        cases satisfied with
        | objRef actual found computed inherited =>
            cases Option.some.inj (actual.symm.trans lookup)
            apply (objectTypeLowerBound_class_iff structural _ _ classKnown).mpr
            rw [mroEquation found computed]
            exact inherited
      · intro included
        have inherited := (objectTypeLowerBound_class_iff structural _ _ classKnown).mp included
        obtain ⟨_, _, found, computed⟩ := hheap.classesExist _ _ lookup
        rw [mroEquation found computed] at inherited
        exact CheckedClassView.objRef lookup found computed inherited
  | callable parameterKnown resultKnown _ _ =>
      constructor
      · intro satisfied
        cases satisfied with
        | objRefBoundMethod actual =>
            cases Option.some.inj (actual.symm.trans lookup)
            exact (objectTypeLowerBound_callable_iff structural boundMethodClass classKnown
              (.callable parameterKnown resultKnown)).mpr rfl
      · intro included
        have classMethod := (objectTypeLowerBound_callable_iff structural
          obj.className classKnown (.callable parameterKnown resultKnown)).mp included
        obtain ⟨receiver, method, payload⟩ := (hheap.boundMethodShape _ _ lookup).mp classMethod
        have objectEqual : obj = ⟨boundMethodClass, .boundMethod receiver method⟩ := by
          cases obj
          simp_all
        subst obj
        exact CheckedCallableAtom.objRefBoundMethod lookup
  | negClass targetKnown =>
      constructor
      · intro satisfied
        rcases satisfied with ⟨_, successful⟩
        cases successful with
        | negClassObjRefOk actual found computed excluded =>
            cases Option.some.inj (actual.symm.trans lookup)
            apply (objectTypeLowerBound_negClass_iff structural _ _ classKnown targetKnown).mpr
            rw [mroEquation found computed]
            exact excluded
      · intro included
        have excluded := (objectTypeLowerBound_negClass_iff structural _ _ classKnown targetKnown).mp included
        obtain ⟨_, _, found, computed⟩ := hheap.classesExist _ _ lookup
        rw [mroEquation found computed] at excluded
        exact ⟨CheckedAnyShape.objRef lookup, EnforceValue.negClassObjRefOk lookup found computed excluded⟩

/-- In a well-formed checked heap, static subtyping preserves the shallow predicate
`CheckedValueSatisfies` by transitivity from the exact object's lower bound. -/
private theorem checkedValueSatisfies_staticSubtype {structural : WellFormedClassHierarchy ct}
    {source target : Ty} {value : CheckedValue}
    (hheap : CheckedHeapWellFormed (embedClassTable ct) cct heap)
    (included : IsSubtype structural source target)
    (satisfied : CheckedValueSatisfies (embedClassTable ct) cct heap value
      (checkedTargetOfGTy (embedTy source))) :
    CheckedValueSatisfies (embedClassTable ct) cct heap value
      (checkedTargetOfGTy (embedTy target)) := by
  cases checkedValueSatisfies_toAnyShape satisfied with
  | objRef lookup =>
      exact (checkedValueSatisfies_lowerBound structural hheap lookup included.targetWellFormed).mpr
        (.trans ((checkedValueSatisfies_lowerBound structural hheap lookup included.sourceWellFormed).mp satisfied)
          included)

/-- A source view preserves checked satisfaction from the embedded static
producer target to the viewed gradual source target. -/
theorem coreViewOnSrc_satisfies
    (view : CoreViewOnSrc ct staticTy sourceTy)
    (hsat :
      CheckedValueSatisfies (embedClassTable ct) cct heap value
        (checkedTargetOfGTy (embedTy staticTy))) :
    CheckedValueSatisfies (embedClassTable ct) cct heap value
      (checkedTargetOfGTy sourceTy) := by
  induction view generalizing value with
  | any =>
      exact checkedValueSatisfies_toAnyShape hsat
  | embed =>
      exact hsat
  | union _ _ ihLeft ihRight =>
      rcases hsat with hleft | hright
      · exact Or.inl (ihLeft hleft)
      · exact Or.inr (ihRight hright)
  | interIntro _ _ ihLeft _ =>
      exact ihLeft hsat.1

private theorem annotationPrecision_to_approxFormula
    (sourceTy : GTy) :
    AnnotationTargetPrecision sourceTy (approxFormula sourceTy) := by
  induction sourceTy with
  | any =>
      exact .refl
  | class_ =>
      exact .refl
  | bottom =>
      exact .refl
  | negClass =>
      exact .refl
  | callable =>
      exact .toAny
  | union _ _ ihLeft ihRight =>
      exact .union ihLeft ihRight
  | intersection _ _ ihLeft ihRight =>
      exact .intersection ihLeft ihRight

private theorem annotationPrecision_to_approxTarget
    (sourceTy : GTy) :
    AnnotationTargetPrecision sourceTy (approxTarget sourceTy) := by
  induction sourceTy with
  | any =>
      exact .refl
  | class_ =>
      exact .refl
  | bottom =>
      exact .refl
  | negClass =>
      exact .refl
  | callable _ _ ihParam ihReturn =>
      exact .callable ihParam ihReturn
  | union _ _ ihLeft ihRight =>
      exact .union ihLeft ihRight
  | intersection left right =>
      exact annotationPrecision_to_approxFormula (.intersection left right)

private inductive StaticValueOk
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (heap : CheckedHeap) :
    CheckedValue → Ty → Prop where
  /-- Ordinary object reference whose runtime class is a subtype of the target class. -/
  | class_
      (lookup : heap.lookup oid = some obj)
      (class_subtype :
        IsSubtype helab.core.toOriginalWellFormedClassHierarchy (.class_ obj.className) (.class_ className)) :
      StaticValueOk p helab heap (.objRef oid) (.class_ className)
  /-- Bound-method reference with exact embedded source origin for its checked method. -/
  | callable
      (lookup :
        heap.lookup oid =
          some ⟨boundMethodClass, .boundMethod receiverOid checkedMethod⟩)
      (receiver_lookup : heap.lookup receiverOid = some receiverObject)
      (definingClassName : Identifier)
      (origin :
        Nonempty { origin : StaticMethodOrigin p helab checkedMethod //
          origin.definingClassName = definingClassName ∧
          origin.sourceMethod.paramTy = paramTy ∧
          origin.sourceMethod.returnTy = returnTy })
      (receiver_ok :
        StaticValueOk p helab heap (.objRef receiverOid) (.class_ definingClassName)) :
      StaticValueOk p helab heap (.objRef oid) (.callable paramTy returnTy)
  /-- Left injection for a static union value. -/
  | unionLeft
      (value_ok : StaticValueOk p helab heap value leftTy) :
      StaticValueOk p helab heap value (.union leftTy rightTy)
  /-- Right injection for a static union value. -/
  | unionRight
      (value_ok : StaticValueOk p helab heap value rightTy) :
      StaticValueOk p helab heap value (.union leftTy rightTy)
  /-- Runtime intersection introduction for a value satisfying both static types. -/
  | interIntro
      (left_ok : StaticValueOk p helab heap value leftTy)
      (right_ok : StaticValueOk p helab heap value rightTy) :
      StaticValueOk p helab heap value (.intersection leftTy rightTy)
  /-- Negated-class value whose runtime MRO excludes the negated class. -/
  | negClass
      (lookup : heap.lookup oid = some obj)
      (class_lookup : findClass p.classes obj.className = some cls)
      (class_mro : ComputeMro p.classes cls mro)
      (class_not_in_mro : className ∉ mro) :
      StaticValueOk p helab heap (.objRef oid) (.negClass className)
  /-- Static subsumption for runtime values. -/
  | sub
      (value_ok : StaticValueOk p helab heap value producerTy)
      (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy producerTy advertisedTy) :
      StaticValueOk p helab heap value advertisedTy

private theorem staticValueOk_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (hvalue : StaticValueOk p helab heap value staticTy) :
    StaticValueOk p helab heap' value staticTy := by
  induction hvalue with
  | class_ lookup class_subtype =>
      exact .class_ (hmono _ _ lookup) class_subtype
  | callable lookup receiver_lookup definingClassName origin _ ihReceiver =>
      exact .callable (hmono _ _ lookup) (hmono _ _ receiver_lookup)
        definingClassName origin ihReceiver
  | unionLeft _ ih =>
      exact .unionLeft ih
  | unionRight _ ih =>
      exact .unionRight ih
  | interIntro _ _ ihLeft ihRight =>
      exact .interIntro ihLeft ihRight
  | negClass lookup class_lookup class_mro class_not_in_mro =>
      exact .negClass (hmono _ _ lookup) class_lookup class_mro class_not_in_mro
  | sub _ output_subtype ih =>
      exact .sub ih output_subtype

private theorem staticMethodOrigin_of_boundMethod_lookup
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap)
    (bound_lookup :
      heap.lookup calleeOid =
        some ⟨boundMethodClass, .boundMethod receiverOid checkedMethod⟩) :
    ∃ receiverObject,
      heap.lookup receiverOid = some receiverObject ∧
      ∃ origin : StaticMethodOrigin p helab checkedMethod,
        StaticValueOk p helab heap (.objRef receiverOid)
          (.class_ origin.definingClassName) := by
  obtain ⟨receiverObject, receiver_lookup, receiver_method⟩ :=
    hheap.payloadReceiverValid calleeOid boundMethodClass receiverOid
      checkedMethod bound_lookup
  rcases receiver_method with
    ⟨receiverClass, receiverMro, receiver_class_lookup, receiver_mro,
      checked_lookup⟩
  obtain ⟨sourceMethod, source_lookup⟩ :=
    compiled_checkedMethodLookup_source_exists helab checked_lookup
  let exactLookup := helab.methodLookupCompiled source_lookup checked_lookup
  let origin := StaticMethodOrigin.ofExact helab exactLookup
  obtain ⟨staticReceiverClass, static_class_lookup, receiver_class_eq⟩ :=
    findClass_embedClassTable_reverse receiver_class_lookup
  cases receiver_class_eq
  have static_receiver_mro :
      ComputeMro p.classes staticReceiverClass receiverMro :=
    computeMro_embedClassTable_reverse static_class_lookup receiver_mro
  have receiver_ok :
      StaticValueOk p helab heap (.objRef receiverOid)
        (.class_ origin.definingClassName) :=
    .class_ receiver_lookup
      (.class_ static_class_lookup static_receiver_mro
        exactLookup.source_data.definingClass_mem)
  exact ⟨receiverObject, receiver_lookup, origin, receiver_ok⟩

/-- The source method's declared function type lies below every type assigned to the fixed checked method. -/
private theorem staticValueOk_declaredFunction_provenance
    (origin : StaticMethodOrigin p helab checkedMethod)
    (bound_lookup : heap.lookup oid = some ⟨boundMethodClass, .boundMethod receiverOid checkedMethod⟩)
    (hvalue : StaticValueOk p helab heap value staticTy) (value_eq : value = .objRef oid)
    (targetValid : WellFormedTy p.classes staticTy) :
    IsSubtype helab.core.toOriginalWellFormedClassHierarchy (.callable origin.sourceMethod.paramTy origin.sourceMethod.returnTy) staticTy := by
  induction hvalue generalizing oid receiverOid checkedMethod origin with
  | class_ lookup included =>
      cases value_eq
      cases Option.some.inj (lookup.symm.trans bound_lookup)
      exact .trans (.callableBoundMethod origin.parameter_wellFormed origin.body_bridge.output_wellFormed) included
  | callable lookup _ _ originBox _ _ =>
      cases value_eq
      cases Option.some.inj (lookup.symm.trans bound_lookup)
      rcases originBox with ⟨⟨valueOrigin, _, parameter_eq, return_eq⟩⟩
      have signatures := staticMethodOrigin_same_checked_signature valueOrigin origin
      have parameter := parameter_eq.symm.trans signatures.1
      have result := signatures.2.symm.trans return_eq
      rw [parameter, ← result]
      exact .refl (.callable origin.parameter_wellFormed origin.body_bridge.output_wellFormed)
  | unionLeft _ ih => exact .unionLeft (ih origin bound_lookup value_eq targetValid.union_left) targetValid.union_right
  | unionRight _ ih => exact .unionRight (ih origin bound_lookup value_eq targetValid.union_right) targetValid.union_left
  | interIntro _ _ ihLeft ihRight =>
      exact .interIntro (ihLeft origin bound_lookup value_eq targetValid.intersection_left)
        (ihRight origin bound_lookup value_eq targetValid.intersection_right)
  | negClass lookup class_lookup class_mro excluded =>
      cases value_eq
      cases Option.some.inj (lookup.symm.trans bound_lookup)
      exact .trans (.callableBoundMethod origin.parameter_wellFormed origin.body_bridge.output_wellFormed)
        (.sealedClassNegClass (by simp [sealedClasses]) class_lookup class_mro excluded targetValid.class_of_neg)
  | sub _ included ih => exact .trans (ih origin bound_lookup value_eq included.sourceWellFormed) included

private theorem staticValueOk_satisfies
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap)
    (hvalue : StaticValueOk p helab heap value staticTy) :
    CheckedValueSatisfies (embedClassTable p.classes) helab.cp.classes heap value
      (checkedTargetOfGTy (embedTy staticTy)) := by
  induction hvalue with
  | class_ lookup class_subtype =>
      rename_i oid obj _
      obtain ⟨_, runtimeMro, hfindRuntime, hmroRuntime⟩ :=
        hheap.classesExist _ _ lookup
      have hself : obj.className ∈ runtimeMro := by
        simpa only [findGClass_name hfindRuntime] using mro_self_mem hmroRuntime
      have hclass :
          CheckedValueSatisfies (embedClassTable p.classes) helab.cp.classes heap
            (.objRef oid)
            (checkedTargetOfGTy (embedTy (.class_ obj.className))) :=
        CheckedClassView.objRef lookup hfindRuntime hmroRuntime hself
      exact checkedValueSatisfies_staticSubtype hheap class_subtype hclass
  | callable lookup _ _ _ _ =>
      exact CheckedCallableAtom.objRefBoundMethod lookup
  | unionLeft _ ih =>
      exact Or.inl ih
  | unionRight _ ih =>
      exact Or.inr ih
  | interIntro _ _ ihLeft ihRight =>
      exact ⟨ihLeft, ihRight⟩
  | negClass lookup class_lookup class_mro class_not_in_mro =>
      have hfindG := findGClass_embedClassTable class_lookup
      have hmroG := computeGMro_embedClassTable class_mro
      exact
        ⟨CheckedAnyShape.objRef lookup,
          EnforceValue.negClassObjRefOk lookup hfindG hmroG class_not_in_mro⟩
  | sub _ output_subtype ih =>
      exact checkedValueSatisfies_staticSubtype hheap output_subtype ih

private theorem staticValueOk_satisfies_view
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap)
    (view : CoreViewOnSrc p.classes staticTy sourceTy)
    (hvalue : StaticValueOk p helab heap value staticTy) :
    CheckedValueSatisfies (embedClassTable p.classes) helab.cp.classes heap value
      (checkedTargetOfGTy sourceTy) :=
  coreViewOnSrc_satisfies view (staticValueOk_satisfies hheap hvalue)

private theorem staticValueOk_callableAtom_of_callableSubtype
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap)
    (callee_to_callable :
      IsSubtype helab.core.toOriginalWellFormedClassHierarchy calleeTy (.callable parameterTy returnTy))
    (hvalue : StaticValueOk p helab heap value calleeTy) :
    CheckedCallableAtom heap value := by
  simpa using
    checkedValueSatisfies_staticSubtype hheap callee_to_callable
      (staticValueOk_satisfies hheap hvalue)

/-- Dispatch retains the subtype proof from the declared function type before argument evaluation. -/
private theorem staticCallDispatchEvidence_of_boundMethod
    (hheap : CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap)
    (callee_to_callable : IsSubtype helab.core.toOriginalWellFormedClassHierarchy calleeTy (.callable parameterTy returnTy))
    (callee_ok : StaticValueOk p helab heap (.objRef calleeOid) calleeTy)
    (bound_lookup : heap.lookup calleeOid = some ⟨boundMethodClass, .boundMethod receiverOid checkedMethod⟩) :
    ∃ receiverObject, heap.lookup receiverOid = some receiverObject ∧
      ∃ origin : StaticMethodOrigin p helab checkedMethod,
        StaticValueOk p helab heap (.objRef receiverOid) (.class_ origin.definingClassName) ∧
        IsSubtype helab.core.toOriginalWellFormedClassHierarchy (.callable origin.sourceMethod.paramTy origin.sourceMethod.returnTy)
          (.callable parameterTy returnTy) := by
  obtain ⟨receiverObject, receiver_lookup, origin, receiver_ok⟩ :=
    staticMethodOrigin_of_boundMethod_lookup hheap bound_lookup
  exact ⟨receiverObject, receiver_lookup, origin, receiver_ok,
    .trans (staticValueOk_declaredFunction_provenance origin bound_lookup callee_ok rfl
      callee_to_callable.sourceWellFormed) callee_to_callable⟩

private theorem staticValueOk_callSelection_not_ordinary
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap)
    (callee_to_callable :
      IsSubtype helab.core.toOriginalWellFormedClassHierarchy calleeTy (.callable parameterTy returnTy))
    (callee_ok :
      StaticValueOk p helab heap (.objRef calleeOid) calleeTy)
    (ordinary_lookup :
      heap.lookup calleeOid = some ⟨className, .ordinary⟩) :
    False := by
  have callable_atom :=
    staticValueOk_callableAtom_of_callableSubtype hheap
      callee_to_callable callee_ok
  cases callable_atom with
  | objRefBoundMethod bound_lookup =>
      rw [ordinary_lookup] at bound_lookup
      cases bound_lookup

/-- Checked environments realize static environments when every statically
typed binding maps to a runtime value satisfying the same static type. -/
private def StaticEnvOk
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (heap : CheckedHeap)
    (env : CheckedEnv)
    (Γ : TyEnv) : Prop :=
  ∀ x T, Γ.lookup x = some T →
    ∃ value, env.lookup x = some value ∧ StaticValueOk p helab heap value T

private theorem staticEnvOk_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (henv : StaticEnvOk p helab heap env Γ) :
    StaticEnvOk p helab heap' env Γ := by
  intro x T hlookup
  obtain ⟨value, henvLookup, hvalue⟩ := henv x T hlookup
  exact ⟨value, henvLookup, staticValueOk_heapMono hmono hvalue⟩

private theorem staticEnvOk_update
    {x : Identifier} {oldTy newTy : Ty} {value : CheckedValue}
    (henv : StaticEnvOk p helab heap env Γ)
    (hlookup : Γ.lookup x = some oldTy)
    (hvalue : StaticValueOk p helab heap value newTy) :
    StaticEnvOk p helab heap (env.update x value) (Γ.update x newTy) := by
  intro y T hlookupUpdated
  by_cases hyx : y = x
  · subst y
    have hlookupNew : (Γ.update x newTy).lookup x = some newTy :=
      namedEnv_update_lookup_eq newTy ⟨oldTy, hlookup⟩
    rw [hlookupNew] at hlookupUpdated
    obtain rfl := Option.some.inj hlookupUpdated
    exact ⟨value, namedEnv_update_lookup_eq value (by
      obtain ⟨oldValue, henvLookup, _⟩ := henv x oldTy hlookup
      exact ⟨oldValue, henvLookup⟩), hvalue⟩
  · rw [namedEnv_update_lookup_ne newTy hyx] at hlookupUpdated
    obtain ⟨oldValue, henvLookup, holdValue⟩ := henv y T hlookupUpdated
    exact ⟨oldValue, by
      rw [namedEnv_update_lookup_ne value hyx]
      exact henvLookup, holdValue⟩

private theorem staticEnvOk_refine_isInstance_true
    (henv : StaticEnvOk p helab heap env Γ)
    (hlookupΓ : Γ.lookup x = some T)
    (hlookupEnv : env.lookup x = some (.objRef oid))
    (hlookupHeap : heap.lookup oid = some obj)
    (hfindG : findGClass (embedClassTable p.classes) obj.className = some gcls)
    (hmroG : GComputeMro (embedClassTable p.classes) gcls mro)
    (hmem : C ∈ mro) :
    StaticEnvOk p helab heap env
      (Γ.update x (.intersection T (.class_ C))) := by
  obtain ⟨value, henvValue, hvalueOk⟩ := henv x T hlookupΓ
  cases henvValue.symm.trans hlookupEnv
  obtain ⟨cls, hfind, hclsEq⟩ := findClass_embedClassTable_reverse hfindG
  subst hclsEq
  have hmro : ComputeMro p.classes cls mro :=
    computeMro_embedClassTable_reverse hfind hmroG
  have hupdated := staticEnvOk_update henv hlookupΓ
    (.interIntro hvalueOk (.class_ hlookupHeap (.class_ hfind hmro hmem)))
  simpa [namedEnv_update_eq_self hlookupEnv] using hupdated

private theorem staticEnvOk_refine_isInstance_false
    (henv : StaticEnvOk p helab heap env Γ)
    (hlookupΓ : Γ.lookup x = some T)
    (hlookupEnv : env.lookup x = some (.objRef oid))
    (hlookupHeap : heap.lookup oid = some obj)
    (hfindG : findGClass (embedClassTable p.classes) obj.className = some gcls)
    (hmroG : GComputeMro (embedClassTable p.classes) gcls mro)
    (hnotMem : C ∉ mro) :
    StaticEnvOk p helab heap env
      (Γ.update x (.intersection T (.negClass C))) := by
  obtain ⟨value, henvValue, hvalueOk⟩ := henv x T hlookupΓ
  cases henvValue.symm.trans hlookupEnv
  obtain ⟨cls, hfind, hclsEq⟩ := findClass_embedClassTable_reverse hfindG
  subst hclsEq
  have hmro : ComputeMro p.classes cls mro :=
    computeMro_embedClassTable_reverse hfind hmroG
  have hupdated := staticEnvOk_update henv hlookupΓ
    (.interIntro hvalueOk (.negClass hlookupHeap hfind hmro hnotMem))
  simpa [namedEnv_update_eq_self hlookupEnv] using hupdated

/-- Heap-parametric evidence that static values at `producerTy` satisfy a
source target. This is the reusable payload carried by checked boundary
frames whose runtime source obligation is a type obligation. -/
private structure StaticOutputFact
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (producerTy : Ty)
    (sourceTy : GTy) : Type where
  /-- Every value with `StaticValueOk` at `producerTy` satisfies the shallow class,
  exclusion and function-shape requirements of `sourceTy` in a well-formed checked heap. -/
  holds : ∀ {heap value},
    CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap →
    StaticValueOk p helab heap value producerTy →
    CheckedValueSatisfies (embedClassTable p.classes) helab.cp.classes heap value
      (checkedTargetOfGTy sourceTy)

private def staticOutputFact_ofView
    (view : CoreViewOnSrc p.classes producerTy sourceTy) :
    StaticOutputFact p helab producerTy sourceTy where
  holds := fun hheap hvalue =>
    staticValueOk_satisfies_view hheap view hvalue

private def staticOutputFact_precision
    (fact : StaticOutputFact p helab producerTy sourceTy)
    (hprecision : AnnotationTargetPrecision sourceTy widerSourceTy) :
    StaticOutputFact p helab producerTy widerSourceTy where
  holds := fun hheap hvalue =>
    checkedValueSatisfies_precision hprecision (fact.holds hheap hvalue)

private theorem checkedValueSatisfies_compileTargetPrecision
    (hprecision : CompileTargetPrecision sourceTarget widerTarget)
    (hsat : CheckedValueSatisfies gct cct heap value sourceTarget) :
    CheckedValueSatisfies gct cct heap value widerTarget := by
  induction hprecision generalizing value with
  | refl =>
      exact hsat
  | toAny =>
      exact checkedValueSatisfies_toAnyShape hsat
  | callable _ _ _ _ =>
      exact hsat
  | union _ _ ihLeft ihRight =>
      rcases hsat with hleft | hright
      · exact Or.inl (ihLeft hleft)
      · exact Or.inr (ihRight hright)
  | intersection _ _ ihLeft ihRight =>
      exact ⟨ihLeft hsat.1, ihRight hsat.2⟩
  | fromBottom =>
      cases hsat
  | intersection_left_toAny _ _ _ ihRight =>
      exact ihRight hsat.2
  | intersection_right_toAny _ _ ihLeft _ =>
      exact ihLeft hsat.1
  | meet _ _ ihLeft ihRight =>
      exact ⟨ihLeft hsat, ihRight hsat⟩

private theorem normalizeCallParamAnnotationIntersection_compilePrecision
    (toLeft : CompileTargetPrecision sourceTarget leftTarget)
    (toRight : CompileTargetPrecision sourceTarget rightTarget) :
    CompileTargetPrecision sourceTarget
      (Checked.normalizeCallParamAnnotationIntersection leftTarget rightTarget) := by
  unfold Checked.normalizeCallParamAnnotationIntersection
  by_cases hEq : leftTarget = rightTarget
  · subst hEq
    simp
    exact toLeft
  · simp [hEq]
    by_cases hOrd : Checked.checkedTargetCmp leftTarget rightTarget = Ordering.gt
    · simp [hOrd]
      exact .meet toRight toLeft
    · simp [hOrd]
      exact .meet toLeft toRight

private theorem callParamCheckedTarget_compilePrecision
    (sourceTy : GTy) :
    CompileTargetPrecision
      (checkedTargetOfGTy sourceTy)
      (callParamCheckedTarget sourceTy) := by
  induction sourceTy with
  | any =>
      exact .refl
  | class_ =>
      exact .refl
  | bottom =>
      exact .refl
  | negClass =>
      exact .refl
  | callable =>
      exact .toAny
  | union left right ihLeft ihRight =>
      rw [callParamCheckedTarget_union]
      cases hleft : callParamCheckedTarget left <;>
        cases hright : callParamCheckedTarget right
      all_goals
        first
        | exact .toAny
        | exact .union
            (by simpa [hleft] using ihLeft)
            (by simpa [hright] using ihRight)
  | intersection left right ihLeft ihRight =>
      rw [callParamCheckedTarget_intersection]
      let sourceTarget := checkedTargetOfGTy (.intersection left right)
      have toLeft :
          CompileTargetPrecision sourceTarget
            (callParamCheckedTarget left) :=
        .intersection_right_toAny ihLeft .toAny
      have toRight :
          CompileTargetPrecision sourceTarget
            (callParamCheckedTarget right) :=
        .intersection_left_toAny .toAny ihRight
      cases hleft : callParamCheckedTarget left <;>
        cases hright : callParamCheckedTarget right
      all_goals
        first
        | exact (by simpa [sourceTarget, hleft] using toLeft)
        | exact (by simpa [sourceTarget, hright] using toRight)
        | exact
            (by
              simpa [sourceTarget, hleft, hright] using
                normalizeCallParamAnnotationIntersection_compilePrecision
                  (by simpa [sourceTarget, hleft] using toLeft)
                  (by simpa [sourceTarget, hright] using toRight))

private def staticOutputFact_callParamTarget
    (fact : StaticOutputFact p helab producerTy sourceTy) :
    StaticOutputFact p helab producerTy (callParamTarget sourceTy) where
  holds := fun hheap hvalue =>
    checkedValueSatisfies_compileTargetPrecision
      (by
        simpa [callParamCheckedTarget] using
          callParamCheckedTarget_compilePrecision sourceTy)
      (fact.holds hheap hvalue)

private def staticOutputFact_callableSubtype
    (callee_to_callable :
      IsSubtype helab.core.toOriginalWellFormedClassHierarchy calleeTy (.callable paramTy returnTy))
    (targetParam targetReturn : GTy) :
    StaticOutputFact p helab calleeTy (.callable targetParam targetReturn) where
  holds := fun hheap hvalue =>
    staticValueOk_callableAtom_of_callableSubtype hheap
      callee_to_callable hvalue

private def staticOutputFact_any :
    StaticOutputFact p helab producerTy .any where
  holds := fun hheap hvalue =>
    checkedValueSatisfies_toAnyShape (staticValueOk_satisfies hheap hvalue)

private def staticOutputFact_staticSubtypeEmbed
    (subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy producerTy targetTy) :
    StaticOutputFact p helab producerTy (embedTy targetTy) where
  holds := fun hheap hvalue =>
    checkedValueSatisfies_staticSubtype hheap subtype
      (staticValueOk_satisfies hheap hvalue)

private def staticOutputFact_precompose
    (fact : StaticOutputFact p helab producerTy sourceTy)
    (toProducer : ∀ {heap value},
      StaticValueOk p helab heap value inputTy →
      StaticValueOk p helab heap value producerTy) :
    StaticOutputFact p helab inputTy sourceTy where
  holds := fun hheap hvalue =>
    fact.holds hheap (toProducer hvalue)

private theorem attrSelection_sourceObligation_of_satisfies
    (selection : AttrSelection ct receiverTy attributeName resultTy)
    (hsat :
      CheckedValueSatisfies (embedClassTable ct) cct heap value
        (checkedTargetOfGTy (embedTy receiverTy))) :
    Checked.SourceObligationHolds (embedClassTable ct) cct heap value
      (.hasAttribute site attributeName) := by
  let classCase :
      ∀ {className paramTy returnTy},
        FindMethodType ct className attributeName paramTy returnTy →
        CheckedValueSatisfies (embedClassTable ct) cct heap value
          (checkedTargetOfGTy (embedTy (.class_ className))) →
        Checked.SourceObligationHolds (embedClassTable ct) cct heap value
          (.hasAttribute site attributeName) := by
    intro className paramTy returnTy hfindMethod hclass
    cases hclass with
    | objRef hlookup hfindG hmroG hmem =>
        rename_i oid obj receiverGClass receiverMro
        obtain ⟨receiverClass, hfindReceiver, hclassEq⟩ :=
          findClass_embedClassTable_reverse hfindG
        cases hclassEq
        have hmroReceiver : ComputeMro ct receiverClass _ :=
          computeMro_embedClassTable_reverse hfindReceiver hmroG
        have hfindReceiverName :
            findClass ct receiverClass.name = some receiverClass := by
          have hname := findClass_name hfindReceiver
          simpa [hname] using hfindReceiver
        obtain ⟨ancestorClass, ancestorMro, declaredMethod, ancestorLookup,
          ancestorComputed, declaredLookup, _, _⟩ := hfindMethod
        obtain ⟨sourceMethod, hsourceLookup⟩ :=
          findMethodInMro_of_ancestor hmroReceiver hfindReceiverName hmem
            ancestorLookup ancestorComputed declaredLookup
        exact
          ⟨_, _, _, _, embedMethod sourceMethod, rfl, hlookup, hfindG, hmroG,
            findGMethodInMro_embed hsourceLookup⟩
  induction selection with
  | class_ hfindMethod =>
      exact classCase hfindMethod hsat
  | union leftMethod rightMethod =>
      rcases hsat with hleft | hright
      · exact classCase leftMethod hleft
      · exact classCase rightMethod hright
  | inter leftMethod _ =>
      exact classCase leftMethod hsat.1

/-- Boundary evidence produced from a bridge view and a source site. The
producer type is the static type of the value entering the checked boundary. -/
private structure StaticTypeBoundaryEvidence
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (producerTy : Ty)
    (target : CheckedTarget)
    (obligation : SourceObligation) : Type where
  /-- Source target enforced by the checked boundary. -/
  sourceTy : GTy
  /-- Source site reported by the checked boundary. -/
  site : SourceSite
  /-- Boundary causes report expression and method-return sites, never
  method-parameter sites. -/
  site_boundary :
    match site with
    | .expression _ => True
    | .methodReturn _ _ => True
    | .methodParameter _ _ => False
  /-- Static-to-source evidence for the boundary source target. -/
  output : StaticOutputFact p helab producerTy sourceTy
  /-- Checked target equality stored by the machine frame. -/
  target_eq : target = checkedTargetOfGTy sourceTy
  /-- Source obligation equality stored by the machine frame. -/
  obligation_eq : obligation = .hasType site sourceTy

private theorem staticTypeBoundaryEvidence_causeSatisfies
    (fact : StaticTypeBoundaryEvidence p helab producerTy target obligation)
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap)
    (hvalue : StaticValueOk p helab heap value producerTy) :
    Checked.CauseSatisfiesObligation
      (embedClassTable p.classes)
      helab.cp.classes
      heap
      (.boundary value target)
      obligation := by
  rcases fact with ⟨sourceTy, site, site_boundary, output, target_eq, obligation_eq⟩
  subst obligation
  subst target
  cases site with
  | expression site =>
      exact ⟨rfl, output.holds hheap hvalue⟩
  | methodParameter className methodName =>
      cases site_boundary
  | methodReturn className methodName =>
      exact ⟨rfl, output.holds hheap hvalue⟩

private def staticTypeBoundaryEvidence_precompose
    (evidence :
      StaticTypeBoundaryEvidence p helab producerTy target obligation)
    (toProducer : ∀ {heap value},
      StaticValueOk p helab heap value inputTy →
      StaticValueOk p helab heap value producerTy) :
    StaticTypeBoundaryEvidence p helab inputTy target obligation where
  sourceTy := evidence.sourceTy
  site := evidence.site
  site_boundary := evidence.site_boundary
  output := {
    holds := fun hheap hvalue =>
      evidence.output.holds hheap (toProducer hvalue) }
  target_eq := evidence.target_eq
  obligation_eq := evidence.obligation_eq

private def staticTypeBoundaryEvidence_ofOutput
    (output : StaticOutputFact p helab producerTy sourceTy)
    (site : SourceSite)
    (site_boundary :
      match site with
      | .expression _ => True
      | .methodReturn _ _ => True
      | .methodParameter _ _ => False) :
    StaticTypeBoundaryEvidence p helab producerTy
      (checkedTargetOfGTy sourceTy)
      (.hasType site sourceTy) where
  sourceTy := sourceTy
  site := site
  site_boundary := site_boundary
  output := output
  target_eq := rfl
  obligation_eq := rfl

private def staticTypeBoundaryEvidence_methodReturn
    (origin : StaticMethodOrigin p helab checkedMethod) :
    StaticTypeBoundaryEvidence p helab origin.sourceMethod.returnTy
      checkedMethod.returnTy checkedMethod.returnObligation where
  sourceTy := embedTy origin.sourceMethod.returnTy
  site := .methodReturn origin.definingClassName origin.sourceMethod.name
  site_boundary := True.intro
  output := staticOutputFact_staticSubtypeEmbed (.refl origin.body_bridge.output_wellFormed)
  target_eq := origin.returnTy_eq
  obligation_eq := origin.returnObligation_eq

/-- Source-attribute evidence for a dynamic attribute operation. It states
that any receiver value at the producer static type has the reported source
attribute in the embedded source class table. -/
private structure StaticAttributeEvidence
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (receiverTy : Ty)
    (attributeName : Identifier)
    (obligation : SourceObligation) : Type where
  /-- Source expression site reported if dynamic lookup fails. -/
  site : SourceExpressionSite
  /-- The checked frame reports the requested attribute at the source site. -/
  obligation_eq : obligation = .hasAttribute site attributeName
  /-- Static receivers at the producer type satisfy the source attribute
  obligation, so missing-attribute blame is impossible for such receivers. -/
  holds : ∀ {heap value},
    CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap →
    StaticValueOk p helab heap value receiverTy →
    Checked.SourceObligationHolds (embedClassTable p.classes) helab.cp.classes
      heap value obligation

private def staticAttributeEvidence_ofSelection
    (selection : AttrSelection p.classes receiverTy attributeName resultTy)
    (site : SourceExpressionSite) :
    StaticAttributeEvidence p helab receiverTy attributeName
      (.hasAttribute site attributeName) where
  site := site
  obligation_eq := rfl
  holds := fun hheap hvalue =>
    attrSelection_sourceObligation_of_satisfies selection
      (staticValueOk_satisfies hheap hvalue)

private def staticAttributeEvidence_precompose
    (evidence :
      StaticAttributeEvidence p helab receiverTy attributeName obligation)
    (toReceiver : ∀ {heap value},
      StaticValueOk p helab heap value inputTy →
      StaticValueOk p helab heap value receiverTy) :
    StaticAttributeEvidence p helab inputTy attributeName obligation where
  site := evidence.site
  obligation_eq := evidence.obligation_eq
  holds := fun hheap hvalue =>
    evidence.holds hheap (toReceiver hvalue)

private theorem staticValueOk_boundMethod_of_findMethodType
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap)
    (hfmt : FindMethodType p.classes className attributeName paramTy returnTy)
    (receiver_satisfies :
      CheckedValueSatisfies (embedClassTable p.classes) helab.cp.classes heap
        (.objRef receiverOid)
        (checkedTargetOfGTy (embedTy (.class_ className))))
    (receiver_lookup : heap.lookup receiverOid = some receiverObject)
    (class_lookup :
      findGClass (embedClassTable p.classes) receiverObject.className =
        some receiverClass)
    (receiver_mro :
      GComputeMro (embedClassTable p.classes) receiverClass receiverMro)
    (checked_lookup :
      findCheckedMethodInMro helab.cp.classes receiverMro attributeName =
        some checkedMethod)
    (allocation :
      heap.alloc ⟨boundMethodClass, .boundMethod receiverOid checkedMethod⟩ =
        (boundMethodOid, heap')) :
    StaticValueOk p helab heap' (.objRef boundMethodOid)
      (.callable paramTy returnTy) := by
  cases receiver_satisfies with
  | objRef receiver_lookup' class_lookup' receiver_mro' class_mem =>
      rw [receiver_lookup] at receiver_lookup'
      cases receiver_lookup'
      rw [class_lookup] at class_lookup'
      cases class_lookup'
      have hmroEq :=
        gComputeMro_determinism receiver_mro' receiver_mro
      have class_mem_receiver : className ∈ receiverMro := by
        simpa [hmroEq] using class_mem
      obtain ⟨staticReceiverClass, static_class_lookup, hclassEq⟩ :=
        findClass_embedClassTable_reverse class_lookup
      cases hclassEq
      have static_receiver_mro :
          ComputeMro p.classes staticReceiverClass receiverMro :=
        computeMro_embedClassTable_reverse static_class_lookup receiver_mro
      have receiver_subtype :
          IsSubtype helab.staticClassTable.hwf.toWellFormedClassHierarchy
            (.class_ receiverObject.className) (.class_ className) :=
        .class_ static_class_lookup static_receiver_mro class_mem_receiver
      obtain ⟨sourceMethod, source_lookup⟩ :=
        typed_method_exists_on_runtime_receiver helab.staticClassTable.hwf
          hfmt receiver_subtype static_class_lookup static_receiver_mro
      have variance :=
        typed_method_variance_on_runtime_receiver
          helab.staticClassTable.hwf
          hfmt receiver_subtype static_class_lookup static_receiver_mro
          source_lookup
      let exactLookup := helab.methodLookupCompiled source_lookup checked_lookup
      let origin := StaticMethodOrigin.ofExact helab exactLookup
      have receiver_lookup_heap' :
          heap'.lookup receiverOid = some receiverObject :=
        checkedHeap_alloc_preserves_old hheap.idsBounded allocation receiver_lookup
      have receiver_defining_ok :
          StaticValueOk p helab heap' (.objRef receiverOid)
            (.class_ origin.definingClassName) := by
        exact .class_ receiver_lookup_heap'
          (.class_ static_class_lookup static_receiver_mro
            exactLookup.source_data.definingClass_mem)
      have bound_method_ok :
          StaticValueOk p helab heap' (.objRef boundMethodOid)
            (.callable origin.sourceMethod.paramTy
              origin.sourceMethod.returnTy) := by
        exact .callable
          (checkedHeap_alloc_lookup_new allocation)
          receiver_lookup_heap'
          origin.definingClassName
          ⟨⟨origin, rfl, rfl, rfl⟩⟩
          receiver_defining_ok
      exact .sub bound_method_ok
        ((IsSubtype.transport rfl).mp (.callable variance.1 variance.2))

private theorem staticValueOk_boundMethod_of_attrSelection
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap)
    (selection : AttrSelection p.classes receiverTy attributeName resultTy)
    (receiver_ok :
      StaticValueOk p helab heap (.objRef receiverOid) receiverTy)
    (receiver_lookup : heap.lookup receiverOid = some receiverObject)
    (class_lookup :
      findGClass (embedClassTable p.classes) receiverObject.className =
        some receiverClass)
    (receiver_mro :
      GComputeMro (embedClassTable p.classes) receiverClass receiverMro)
    (checked_lookup :
      findCheckedMethodInMro helab.cp.classes receiverMro attributeName =
        some checkedMethod)
    (allocation :
      heap.alloc ⟨boundMethodClass, .boundMethod receiverOid checkedMethod⟩ =
        (boundMethodOid, heap')) :
    StaticValueOk p helab heap' (.objRef boundMethodOid) resultTy := by
  have receiver_satisfies :=
    staticValueOk_satisfies hheap receiver_ok
  cases selection with
  | class_ hfmt =>
      exact staticValueOk_boundMethod_of_findMethodType hheap hfmt
        receiver_satisfies receiver_lookup class_lookup receiver_mro
        checked_lookup allocation
  | union hleft hright =>
      rcases receiver_satisfies with receiver_left | receiver_right
      · exact .unionLeft
          (staticValueOk_boundMethod_of_findMethodType hheap hleft
            receiver_left receiver_lookup class_lookup receiver_mro
            checked_lookup allocation)
      · exact .unionRight
          (staticValueOk_boundMethod_of_findMethodType hheap hright
            receiver_right receiver_lookup class_lookup receiver_mro
            checked_lookup allocation)
  | inter hleft hright =>
      exact .interIntro
        (staticValueOk_boundMethod_of_findMethodType hheap hleft
          receiver_satisfies.1 receiver_lookup class_lookup receiver_mro
          checked_lookup allocation)
        (staticValueOk_boundMethod_of_findMethodType hheap hright
          receiver_satisfies.2 receiver_lookup class_lookup receiver_mro
          checked_lookup allocation)

/-- Dynamic-attribute frame evidence. It records both the missing-attribute
obligation proof and the successful-lookup result proof for receivers at the
frame input type. -/
private structure StaticDynAttributePayloadEvidence
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (receiverTy : Ty)
    (attributeName : Identifier)
    (obligation : SourceObligation)
    (resultTy : Ty) : Type where
  /-- Static receivers at the frame input type satisfy the reported
  missing-attribute obligation. -/
  attrEvidence :
    StaticAttributeEvidence p helab receiverTy attributeName obligation
  /-- Well-formedness of the receiver type consumed by this payload. -/
  receiver_wellFormed : WellFormedTy p.classes receiverTy
  /-- Successful checked lookup allocates a bound-method value satisfying the
  static result type recorded by this payload. -/
  boundMethodOk : ∀ {heap heap' receiverOid receiverObject receiverClass receiverMro
      checkedMethod boundMethodOid},
    CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap →
    StaticValueOk p helab heap (.objRef receiverOid) receiverTy →
    heap.lookup receiverOid = some receiverObject →
    findGClass (embedClassTable p.classes) receiverObject.className =
      some receiverClass →
    GComputeMro (embedClassTable p.classes) receiverClass receiverMro →
    findCheckedMethodInMro helab.cp.classes receiverMro attributeName =
      some checkedMethod →
    heap.alloc ⟨boundMethodClass, .boundMethod receiverOid checkedMethod⟩ =
      (boundMethodOid, heap') →
    StaticValueOk p helab heap' (.objRef boundMethodOid) resultTy

private def staticDynAttributePayloadEvidence_ofSelection
    (selection : AttrSelection p.classes receiverTy attributeName resultTy)
    (attrEvidence :
      StaticAttributeEvidence p helab receiverTy attributeName obligation)
    (receiver_wellFormed : WellFormedTy p.classes receiverTy) :
    StaticDynAttributePayloadEvidence p helab receiverTy attributeName
      obligation resultTy where
  attrEvidence := attrEvidence
  receiver_wellFormed := receiver_wellFormed
  boundMethodOk := fun hheap receiver_ok receiver_lookup class_lookup
      receiver_mro checked_lookup allocation =>
    staticValueOk_boundMethod_of_attrSelection hheap selection receiver_ok
      receiver_lookup class_lookup receiver_mro checked_lookup allocation

private def staticDynAttributePayloadEvidence_interIntro
    (left :
      StaticDynAttributePayloadEvidence p helab leftReceiverTy attributeName
        obligation leftResultTy)
    (right :
      StaticDynAttributePayloadEvidence p helab rightReceiverTy attributeName
        obligation rightResultTy) :
    StaticDynAttributePayloadEvidence p helab
      (.intersection leftReceiverTy rightReceiverTy)
      attributeName obligation
      (.intersection leftResultTy rightResultTy) where
  attrEvidence :=
    staticAttributeEvidence_precompose left.attrEvidence
      (fun hvalue =>
        .sub hvalue (.interLeft (.refl left.receiver_wellFormed) right.receiver_wellFormed))
  receiver_wellFormed :=
    .intersection left.receiver_wellFormed right.receiver_wellFormed
  boundMethodOk := fun hheap receiver_ok receiver_lookup class_lookup
      receiver_mro checked_lookup allocation =>
    .interIntro
      (left.boundMethodOk hheap
        (.sub receiver_ok (.interLeft (.refl left.receiver_wellFormed) right.receiver_wellFormed))
        receiver_lookup class_lookup receiver_mro checked_lookup allocation)
      (right.boundMethodOk hheap
        (.sub receiver_ok (.interRight (.refl right.receiver_wellFormed) left.receiver_wellFormed))
        receiver_lookup class_lookup receiver_mro checked_lookup allocation)

/-- A checked call carries its function requirement and its result check. -/
private structure StaticCallPayloadEvidence
    (p : Program) (helab : EmbeddedStaticElaboration p)
    (calleeTy argumentTy returnTy : Ty)
    (returnTarget : CheckedTarget) (returnObligation : SourceObligation) : Type where
  /-- The callee type lies below the function type required by this call. -/
  callee_to_callable : IsSubtype helab.core.toOriginalWellFormedClassHierarchy calleeTy (.callable argumentTy returnTy)
  /-- Values of the recorded result type satisfy the reported result check. -/
  returnBoundary :
    StaticTypeBoundaryEvidence p helab returnTy returnTarget returnObligation

/-- Pairing corresponding union alternatives gives a result below both target output types. -/
private theorem combinedUnionResult_subtype {A B C D X Y : Ty}
    (left : IsSubtype structural (.union A B) X)
    (right : IsSubtype structural (.union C D) Y) :
    IsSubtype structural (.union (.intersection A C) (.intersection B D)) (.intersection X Y) :=
  .unionElim
    (.interMono (subtype_union_iff.mp left).1 (subtype_union_iff.mp right).1)
    (.interMono (subtype_union_iff.mp left).2 (subtype_union_iff.mp right).2)

private def staticCallPayloadEvidence_interIntro
    (left :
      StaticCallPayloadEvidence p helab leftCalleeTy leftArgumentTy
        leftReturnTy returnTarget returnObligation)
    (right :
      StaticCallPayloadEvidence p helab rightCalleeTy rightArgumentTy
        rightReturnTy returnTarget returnObligation)
    (returnBoundary :
      StaticTypeBoundaryEvidence p helab (.intersection leftReturnTy rightReturnTy)
        returnTarget returnObligation) :
    StaticCallPayloadEvidence p helab
      (.intersection leftCalleeTy rightCalleeTy)
      (.intersection leftArgumentTy rightArgumentTy)
      (.intersection leftReturnTy rightReturnTy)
      returnTarget returnObligation where
  callee_to_callable := IsSubtype.callableMeet
    (.interLeft left.callee_to_callable right.callee_to_callable.sourceWellFormed)
    (.interRight right.callee_to_callable left.callee_to_callable.sourceWellFormed)
  returnBoundary := returnBoundary

mutual
  /-- Static evidence for checked syntax currently being evaluated. The type
  index is the static producer type assigned to the value if the checked
  expression returns. -/
  private inductive StaticCheckedExprOk
      (p : Program)
      (helab : EmbeddedStaticElaboration p) :
      TyEnv → CheckedExpr → Ty → Prop where
    /-- Compiler-produced expression for an embedded static bridge. This
    constructor is the entry point from source bridge artifacts into checked
    syntax evidence. -/
    | compiled
        (bridge : EmbeddedExprBridge p.classes helab.core Γ sourceExpr advertisedTy)
        (output : StaticOutputFact p helab bridge.producerTy target)
        (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy bridge.producerTy outputTy) :
        StaticCheckedExprOk p helab Γ
          (compileCheck bridge.hsrc checkedEnv target site)
          outputTy
    /-- Variable expression whose runtime value is supplied by the static
    environment invariant. -/
    | var
        (lookup : Γ.lookup x = some variableTy)
        (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy variableTy outputTy) :
        StaticCheckedExprOk p helab Γ (.var x) outputTy
    /-- `None` literal expression. -/
    | constNone
        (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy (.class_ noneClass) outputTy) :
        StaticCheckedExprOk p helab Γ .constNone outputTy
    /-- `True` literal expression. -/
    | constTrue
        (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy (.class_ boolClass) outputTy) :
        StaticCheckedExprOk p helab Γ .constTrue outputTy
    /-- `False` literal expression. -/
    | constFalse
        (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy (.class_ boolClass) outputTy) :
        StaticCheckedExprOk p helab Γ .constFalse outputTy
    /-- Object allocation expression for an ordinary class. -/
    | new
        (class_lookup : findClass p.classes className = some classDecl)
        (notBool : className ≠ boolClass)
        (notNone : className ≠ noneClass)
        (notBoundMethod : className ≠ boundMethodClass)
        (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy (.class_ className) outputTy) :
        StaticCheckedExprOk p helab Γ (.new className) outputTy
    /-- Standalone `isInstance` expression, whose result is a boolean object. -/
    | isInstance
        (lookup : Γ.lookup x = some variableTy)
        (class_lookup : findClass p.classes className = some classDecl)
        (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy (.class_ boolClass) outputTy) :
        StaticCheckedExprOk p helab Γ (.isInstance x className) outputTy
    /-- Checked enforcement expression with static evidence for the source
    obligation it reports on rejection. -/
    | enforce
        (body : StaticCheckedExprOk p helab Γ checkedBody producerTy)
        (boundary :
          StaticTypeBoundaryEvidence p helab producerTy target obligation)
        (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy producerTy outputTy) :
        StaticCheckedExprOk p helab Γ (.enforce checkedBody target obligation) outputTy
    /-- Dynamic attribute expression with static evidence that missing-attribute
    blame is inconsistent with the embedded source receiver type. -/
    | dynAttrAccess
        (base : StaticCheckedExprOk p helab Γ checkedBase receiverTy)
        (selection : AttrSelection p.classes receiverTy attributeName resultTy)
        (attrEvidence :
          StaticAttributeEvidence p helab receiverTy attributeName obligation) :
        StaticCheckedExprOk p helab Γ
          (.dynAttrAccess checkedBase attributeName obligation)
          resultTy
    /-- Checked call expression. The callee and argument are evaluated in order;
    the call payload records the argument and return obligations that later
    frames must preserve. -/
    | call
        (callee : StaticCheckedExprOk p helab Γ checkedCallee calleeTy)
        (argument : StaticCheckedExprOk p helab Γ checkedArgument argumentTy)
        (payload :
          StaticCallPayloadEvidence p helab calleeTy argumentTy callReturnTy
            returnTarget returnObligation)
        (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy callReturnTy outputTy) :
        StaticCheckedExprOk p helab Γ
          (.call checkedCallee checkedArgument parameterTarget returnTarget
            returnObligation)
          outputTy
    /-- Conditional expression whose two branches are checked under the same
    static environment and whose result is the static union of branch producers. -/
    | cond
        (test_not_isInstance : ∀ x C, checkedTest ≠ .isInstance x C)
        (test : StaticCheckedExprOk p helab Γ checkedTest (.class_ boolClass))
        (thenBranch : StaticCheckedExprOk p helab Γ checkedThen thenTy)
        (elseBranch : StaticCheckedExprOk p helab Γ checkedElse elseTy)
        (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy (.union thenTy elseTy) outputTy) :
        StaticCheckedExprOk p helab Γ
          (.cond checkedTest checkedThen checkedElse)
          outputTy
    /-- Conditional expression whose test is a runtime `isInstance` check.
    The checked machine steps directly into one statically-refined branch and
    pushes a `returnTo` frame for the caller environment. -/
    | condIsInstance
        (lookup : Γ.lookup x = some variableTy)
        (class_lookup : findClass p.classes className = some classDecl)
        (thenBranch :
          StaticCheckedExprOk p helab
            (Γ.update x (.intersection variableTy (.class_ className)))
            checkedThen thenTy)
        (elseBranch :
          StaticCheckedExprOk p helab
            (Γ.update x (.intersection variableTy (.negClass className)))
            checkedElse elseTy)
        (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy (.union thenTy elseTy) outputTy) :
        StaticCheckedExprOk p helab Γ
          (.cond (.isInstance x className) checkedThen checkedElse)
          outputTy
    /-- Intersection introduction for two static derivations of the same
    checked expression. -/
    | interIntro
        (left : StaticCheckedExprOk p helab Γ checkedExpr leftTy)
        (right : StaticCheckedExprOk p helab Γ checkedExpr rightTy)
        (output_subtype :
          IsSubtype helab.core.toOriginalWellFormedClassHierarchy (.intersection leftTy rightTy) outputTy) :
        StaticCheckedExprOk p helab Γ checkedExpr outputTy
    /-- Static subsumption for checked-expression evidence. This does not
    change checked syntax; it changes only the static producer type exposed to
    the surrounding continuation. -/
    | sub
        (expr : StaticCheckedExprOk p helab Γ checkedExpr producerTy)
        (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy producerTy outputTy) :
        StaticCheckedExprOk p helab Γ checkedExpr outputTy

end

section CompileCheckNe

variable
  {p : Program}
  {helab : EmbeddedStaticElaboration p}
  (hsrc :
    GSrcInfer (embedClassTable p.classes) helab.core Γ sourceExpr sourceTy)
  (checkedEnv : GTyEnv) (target : GTy) (site : SourceExpressionSite)

private theorem compileCheck_ne_var (x : Identifier) :
    compileCheck hsrc checkedEnv target site ≠ .var x := by
  cases hsrc <;> simp [compileCheck, compileEnforce]

private theorem compileCheck_ne_constNone :
    compileCheck hsrc checkedEnv target site ≠ .constNone := by
  cases hsrc <;> simp [compileCheck, compileEnforce]

private theorem compileCheck_ne_constTrue :
    compileCheck hsrc checkedEnv target site ≠ .constTrue := by
  cases hsrc <;> simp [compileCheck, compileEnforce]

private theorem compileCheck_ne_constFalse :
    compileCheck hsrc checkedEnv target site ≠ .constFalse := by
  cases hsrc <;> simp [compileCheck, compileEnforce]

private theorem compileCheck_ne_new (className : Identifier) :
    compileCheck hsrc checkedEnv target site ≠ .new className := by
  cases hsrc <;> simp [compileCheck, compileEnforce]

private theorem compileCheck_ne_isInstance (variableName className : Identifier) :
    compileCheck hsrc checkedEnv target site ≠ .isInstance variableName className := by
  cases hsrc <;> simp [compileCheck, compileEnforce]

private theorem compileCheck_ne_dynAttrAccess
    (base : CheckedExpr) (attributeName : Identifier) (obligation : SourceObligation) :
    compileCheck hsrc checkedEnv target site ≠
      .dynAttrAccess base attributeName obligation := by
  cases hsrc <;> simp [compileCheck, compileEnforce]

private theorem compileCheck_ne_attrAccess
    (base : CheckedExpr) (attributeName : Identifier) :
    compileCheck hsrc checkedEnv target site ≠
      .attrAccess base attributeName := by
  cases hsrc <;> simp [compileCheck, compileEnforce]

end CompileCheckNe

private theorem compileCheck_cast_env
    {gct : GClassTable}
    {hwfct : WellFormedGClassTableCore gct}
    {Γ Γ' : SBindingEnv}
    {sourceExpr : GExpr}
    {sourceTy : GTy}
    (hΓ : Γ = Γ')
    (hsrc : GSrcInfer gct hwfct Γ sourceExpr sourceTy)
    (checkedEnv : GTyEnv)
    (target : GTy)
    (site : SourceExpressionSite) :
    compileCheck (cast (by rw [hΓ]) hsrc) checkedEnv target site =
      compileCheck hsrc checkedEnv target site := by
  cases hΓ
  rfl

private def staticCheckedExprOk_unionLeftOutput
    (expr : StaticCheckedExprOk p helab Γ checkedExpr leftTy)
    (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy (.union leftTy rightTy) outputTy) :
    StaticCheckedExprOk p helab Γ checkedExpr outputTy :=
  .sub expr (subtype_union_iff.mp output_subtype).1

private def staticCheckedExprOk_unionRightOutput
    (expr : StaticCheckedExprOk p helab Γ checkedExpr rightTy)
    (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy (.union leftTy rightTy) outputTy) :
    StaticCheckedExprOk p helab Γ checkedExpr outputTy :=
  .sub expr (subtype_union_iff.mp output_subtype).2

private def staticCheckedExprOk_wellFormed
    (expr : StaticCheckedExprOk p helab Γ checkedExpr outputTy) :
    WellFormedTy p.classes outputTy :=
  match expr with
  | .compiled _ _ included => included.targetWellFormed
  | .var _ included => included.targetWellFormed
  | .constNone included => included.targetWellFormed
  | .constTrue included => included.targetWellFormed
  | .constFalse included => included.targetWellFormed
  | .new _ _ _ _ included => included.targetWellFormed
  | .isInstance _ _ included => included.targetWellFormed
  | .enforce _ _ included => included.targetWellFormed
  | .dynAttrAccess _ selection _ =>
      attrSelection_result_wellFormed helab.staticClassTable.hwf selection
  | .call _ _ _ included => included.targetWellFormed
  | .cond _ _ _ _ included => included.targetWellFormed
  | .condIsInstance _ _ _ _ included => included.targetWellFormed
  | .interIntro _ _ included => included.targetWellFormed
  | .sub _ included => included.targetWellFormed

/-- The same checked expression satisfies both types when it has each component type. -/
private def StaticCheckedExprOk.intersection
    (left : StaticCheckedExprOk p helab Γ checkedExpr leftTy)
    (right : StaticCheckedExprOk p helab Γ checkedExpr rightTy) :
    StaticCheckedExprOk p helab Γ checkedExpr (.intersection leftTy rightTy) :=
  .interIntro left right (.refl (.intersection
    (staticCheckedExprOk_wellFormed left) (staticCheckedExprOk_wellFormed right)))

private theorem compileCheck_enforce_target_obligation
    {p : Program}
    {helab : EmbeddedStaticElaboration p}
    (hsrc :
      GSrcInfer (embedClassTable p.classes) helab.core Γ sourceExpr sourceTy)
    (checkedEnv : GTyEnv)
    (sourceTarget : GTy)
    (site : SourceExpressionSite)
    (checkedBody : CheckedExpr)
    (checkedTarget : CheckedTarget)
    (obligation : SourceObligation)
    (checked_eq :
      compileCheck hsrc checkedEnv sourceTarget site =
        .enforce checkedBody checkedTarget obligation) :
    checkedTargetOfGTy sourceTarget = checkedTarget ∧
      .hasType (.expression site) sourceTarget = obligation := by
  cases hsrc <;> simp [compileCheck, compileEnforce] at checked_eq
  all_goals
    first
    | exact ⟨checked_eq.2.1, checked_eq.2.2⟩
    | cases checked_eq

private def StaticEnforceDecomposition
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (Γ : TyEnv)
    (checkedBody : CheckedExpr)
    (target : CheckedTarget)
    (obligation : SourceObligation)
    (outputTy : Ty) : Prop :=
  ∃ producerTy,
    ∃ _boundary :
      StaticTypeBoundaryEvidence p helab producerTy target obligation,
    StaticCheckedExprOk p helab Γ checkedBody producerTy ∧
    IsSubtype helab.core.toOriginalWellFormedClassHierarchy producerTy outputTy

private def staticCompiledEnforceBody_ofCore
    {sourceTy : GTy}
    {hsrc :
      GSrcInfer (embedClassTable p.classes) helab.core
        (embedTyEnv Γ) (embedExpr sourceExpr) sourceTy}
    (core :
      EmbeddedExprBridgeCore p.classes helab.core Γ sourceExpr producerTy
        sourceTy hsrc advertisedTy)
    (checked_eq :
      compileCheck hsrc checkedEnv target site =
        .enforce checkedBody checkedTarget obligation) :
    StaticCheckedExprOk p helab Γ checkedBody producerTy :=
  match core with
  | .var lookup output_subtype =>
      by
        simp [compileCheck, compileEnforce] at checked_eq
        rcases checked_eq with ⟨body_eq, _target_eq, _obligation_eq⟩
        cases body_eq
        exact .var lookup (.refl output_subtype.sourceWellFormed)
  | .constNone output_subtype =>
      by
        simp [compileCheck, compileEnforce] at checked_eq
        rcases checked_eq with ⟨body_eq, _target_eq, _obligation_eq⟩
        cases body_eq
        exact .constNone (.refl output_subtype.sourceWellFormed)
  | .constTrue output_subtype =>
      by
        simp [compileCheck, compileEnforce] at checked_eq
        rcases checked_eq with ⟨body_eq, _target_eq, _obligation_eq⟩
        cases body_eq
        exact .constTrue (.refl output_subtype.sourceWellFormed)
  | .constFalse output_subtype =>
      by
        simp [compileCheck, compileEnforce] at checked_eq
        rcases checked_eq with ⟨body_eq, _target_eq, _obligation_eq⟩
        cases body_eq
        exact .constFalse (.refl output_subtype.sourceWellFormed)
  | .new class_lookup _ notBool notNone notBoundMethod output_subtype =>
      by
        simp [compileCheck, compileEnforce] at checked_eq
        rcases checked_eq with ⟨body_eq, _target_eq, _obligation_eq⟩
        cases body_eq
        exact .new class_lookup notBool notNone notBoundMethod (.refl output_subtype.sourceWellFormed)
  | .attrAccess receiverHsrc receiver producerSelection _ _
      _ .. =>
      by
        simp [compileCheck, compileEnforce] at checked_eq
        rcases checked_eq with ⟨body_eq, _target_eq, _obligation_eq⟩
        cases body_eq
        let receiverBridge :
            EmbeddedExprBridge p.classes helab.core Γ _ _ :=
          { producerTy := _
            srcTy := _
            hsrc := receiverHsrc
            core := receiver }
        exact .dynAttrAccess
          (.compiled
            (bridge := receiverBridge)
            (checkedEnv := checkedEnv)
            (target := .any)
            (site := site.child .attributeReceiver)
            staticOutputFact_any
            (.refl (EmbeddedExprBridgeCore.producer_wellFormed receiver)))
          producerSelection
          (staticAttributeEvidence_ofSelection producerSelection site)
  | .call .. =>
      by
        cases checked_eq
  | .cond .. =>
      by
        cases checked_eq
  | .isInstance lookup class_lookup _ output_subtype =>
      by
        simp [compileCheck, compileEnforce] at checked_eq
        rcases checked_eq with ⟨body_eq, _target_eq, _obligation_eq⟩
        cases body_eq
        exact .isInstance lookup class_lookup (.refl output_subtype.sourceWellFormed)
  | .condIsInstance .. =>
      by
        cases checked_eq
  | .interIntro leftHsrc left rightHsrc right _ .. =>
      by
        let leftBody :=
          staticCompiledEnforceBody_ofCore
            (p := p)
            (helab := helab)
            (Γ := Γ)
            (sourceExpr := sourceExpr)
            (producerTy := _)
            (sourceTy := _)
            (hsrc := leftHsrc)
            (advertisedTy := _)
            (checkedEnv := checkedEnv)
            (target := target)
            (site := site)
            (checkedBody := checkedBody)
            (checkedTarget := checkedTarget)
            (obligation := obligation)
            left
            checked_eq
        have right_eq :
            compileCheck rightHsrc checkedEnv target site =
              .enforce checkedBody checkedTarget obligation := by
          rw [compileCheck_sourceCoherent rightHsrc leftHsrc checkedEnv target site]
          exact checked_eq
        let rightBody :=
          staticCompiledEnforceBody_ofCore
            (p := p)
            (helab := helab)
            (Γ := Γ)
            (sourceExpr := sourceExpr)
            (producerTy := _)
            (sourceTy := _)
            (hsrc := rightHsrc)
            (advertisedTy := _)
            (checkedEnv := checkedEnv)
            (target := target)
            (site := site)
            (checkedBody := checkedBody)
            (checkedTarget := checkedTarget)
            (obligation := obligation)
            right
            right_eq
        exact .intersection leftBody rightBody
  | .sub _ inner .. =>
      staticCompiledEnforceBody_ofCore
        (p := p)
        (helab := helab)
        (Γ := Γ)
        (sourceExpr := sourceExpr)
        (producerTy := producerTy)
        (sourceTy := sourceTy)
        (hsrc := hsrc)
        (advertisedTy := _)
        (checkedEnv := checkedEnv)
        (target := target)
        (site := site)
        (checkedBody := checkedBody)
        (checkedTarget := checkedTarget)
        (obligation := obligation)
        inner
        checked_eq

private def staticCheckedExprOk_enforce_of_eq
    (expr : StaticCheckedExprOk p helab Γ checkedExpr outputTy)
    (checked_eq :
      checkedExpr = .enforce checkedBody target obligation) :
    StaticEnforceDecomposition p helab Γ checkedBody target obligation outputTy :=
  match expr with
  | .compiled bridge output output_subtype =>
      by
        obtain ⟨target_eq, obligation_eq⟩ :=
          compileCheck_enforce_target_obligation bridge.hsrc _ _ _
            checkedBody target obligation checked_eq
        cases target_eq
        cases obligation_eq
        exact ⟨
          bridge.producerTy,
            staticTypeBoundaryEvidence_ofOutput output (.expression _) True.intro,
            staticCompiledEnforceBody_ofCore
              (p := p)
              (helab := helab)
              (Γ := Γ)
              (sourceExpr := _)
              (producerTy := _)
              (sourceTy := _)
              (hsrc := bridge.hsrc)
              (advertisedTy := _)
              (checkedEnv := _)
              (target := _)
              (site := _)
              (checkedBody := checkedBody)
              (checkedTarget := _)
              (obligation := _)
              bridge.core
              checked_eq,
          output_subtype⟩
  | .enforce body boundary output_subtype =>
      by
        cases checked_eq
        exact ⟨_, boundary, body, output_subtype⟩
  | .interIntro left right output_subtype =>
      by
        rcases staticCheckedExprOk_enforce_of_eq left checked_eq with
          ⟨leftProducer, leftBoundary, leftBody, leftSubtype⟩
        rcases staticCheckedExprOk_enforce_of_eq right checked_eq with
          ⟨rightProducer, _, rightBody, rightSubtype⟩
        let combinedBody :
            StaticCheckedExprOk p helab Γ checkedBody
              (.intersection leftProducer rightProducer) :=
          .intersection leftBody rightBody
        let combinedBoundary :
            StaticTypeBoundaryEvidence p helab
              (.intersection leftProducer rightProducer)
              target obligation :=
          staticTypeBoundaryEvidence_precompose leftBoundary
            (fun hvalue =>
              .sub hvalue (.interLeft (.refl (staticCheckedExprOk_wellFormed leftBody))
                (staticCheckedExprOk_wellFormed rightBody)))
        exact ⟨
          .intersection leftProducer rightProducer,
          combinedBoundary,
          combinedBody,
            .trans
              (.interMono leftSubtype rightSubtype)
              output_subtype⟩
  | .sub inner output_subtype =>
      by
        rcases staticCheckedExprOk_enforce_of_eq inner checked_eq with
          ⟨producerTy, boundary, body, innerSubtype⟩
        exact ⟨producerTy, boundary, body,
          .trans innerSubtype output_subtype⟩
  | .var .. =>
      by cases checked_eq
  | .constNone .. =>
      by cases checked_eq
  | .constTrue .. =>
      by cases checked_eq
  | .constFalse .. =>
      by cases checked_eq
  | .new .. =>
      by cases checked_eq
  | .isInstance .. =>
      by cases checked_eq
  | .dynAttrAccess .. =>
      by cases checked_eq
  | .call .. =>
      by cases checked_eq
  | .cond .. =>
      by cases checked_eq
  | .condIsInstance .. =>
      by cases checked_eq

private def staticCheckedExprOk_enforce
    (expr :
      StaticCheckedExprOk p helab Γ
        (.enforce checkedBody target obligation) outputTy) :
    StaticEnforceDecomposition p helab Γ checkedBody target obligation outputTy :=
  staticCheckedExprOk_enforce_of_eq expr rfl

private def StaticCallDecomposition
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (Γ : TyEnv)
    (checkedCallee checkedArgument : CheckedExpr)
    (returnTarget : CheckedTarget)
    (returnObligation : SourceObligation)
    (outputTy : Ty) : Prop :=
  ∃ calleeTy argumentTy returnTy,
    ∃ _payload :
      StaticCallPayloadEvidence p helab calleeTy argumentTy returnTy
        returnTarget returnObligation,
    StaticCheckedExprOk p helab Γ checkedCallee calleeTy ∧
    StaticCheckedExprOk p helab Γ checkedArgument argumentTy ∧
    IsSubtype helab.core.toOriginalWellFormedClassHierarchy returnTy outputTy

private theorem compileCheck_call_return_obligation
    {p : Program}
    {helab : EmbeddedStaticElaboration p}
    (hsrc :
      GSrcInfer (embedClassTable p.classes) helab.core Γ sourceExpr sourceTy)
    (checkedEnv : GTyEnv)
    (sourceTarget : GTy)
    (site : SourceExpressionSite)
    (checkedCallee checkedArgument : CheckedExpr)
    (parameterTarget returnTarget : CheckedTarget)
    (returnObligation : SourceObligation)
    (checked_eq :
      compileCheck hsrc checkedEnv sourceTarget site =
        .call checkedCallee checkedArgument parameterTarget
          returnTarget returnObligation) :
    checkedTargetOfGTy sourceTarget = returnTarget ∧
      .hasType (.expression site) sourceTarget = returnObligation := by
  cases hsrc <;> simp [compileCheck, compileEnforce] at checked_eq
  · exact ⟨checked_eq.2.2.2.1, checked_eq.2.2.2.2⟩
  all_goals cases checked_eq

private structure StaticCallHead
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (Γ : TyEnv)
    (checkedCallee checkedArgument : CheckedExpr)
    (producerTy : Ty) : Type where
  /-- Static type of the callee expression. -/
  calleeTy : Ty
  /-- Static type of the argument expression. -/
  argumentTy : Ty
  /-- Static return type selected by the call expression. -/
  returnTy : Ty
  /-- The function requirement used by both call decomposition and dispatch. -/
  callee_to_callable : IsSubtype helab.core.toOriginalWellFormedClassHierarchy calleeTy (.callable argumentTy returnTy)
  /-- Static evidence for the callee checked expression. -/
  callee_ok : StaticCheckedExprOk p helab Γ checkedCallee calleeTy
  /-- Static evidence for the argument checked expression. -/
  argument_ok : StaticCheckedExprOk p helab Γ checkedArgument argumentTy
  /-- Static transfer from the selected return type to the bridge producer. -/
  return_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy returnTy producerTy

private def staticCompiledCallHead_ofCore
    {sourceTy : GTy}
    {hsrc :
      GSrcInfer (embedClassTable p.classes) helab.core
        (embedTyEnv Γ) (embedExpr sourceExpr) sourceTy}
    (core :
      EmbeddedExprBridgeCore p.classes helab.core Γ sourceExpr producerTy
        sourceTy hsrc advertisedTy)
    (checked_eq :
      compileCheck hsrc checkedEnv sourceTarget site =
        .call checkedCallee checkedArgument parameterTarget
          returnTarget returnObligation) :
    StaticCallHead p helab Γ checkedCallee checkedArgument producerTy :=
  match core with
  | .call calleeHsrc calleeBridge argumentHsrc argumentBridge
      producerSelection argument_subtype
      _ _
      output_subtype =>
      by
        simp [compileCheck] at checked_eq
        rcases checked_eq with
          ⟨callee_eq, argument_eq, _parameter_eq, return_eq, obligation_eq⟩
        cases callee_eq
        cases argument_eq
        cases return_eq
        cases obligation_eq
        have selectedCallable := callSelection_subtype_callable producerSelection
          calleeBridge.producer_wellFormed argument_subtype.targetWellFormed
        have returnRefl := IsSubtype.refl (structural := helab.core.toOriginalWellFormedClassHierarchy)
          output_subtype.sourceWellFormed
        let calleeBridgeWrapped :
            EmbeddedExprBridge p.classes helab.core Γ _ _ :=
          { producerTy := _
            srcTy := _
            hsrc := calleeHsrc
            core := calleeBridge }
        let argumentBridgeWrapped :
            EmbeddedExprBridge p.classes helab.core Γ _ _ :=
          { producerTy := _
            srcTy := _
            hsrc := argumentHsrc
            core := argumentBridge }
        let callArgumentTarget : GTy :=
          callParamTarget argumentBridgeWrapped.srcTy
        let callee_ok :
            StaticCheckedExprOk p helab Γ
              (compileCheck calleeHsrc checkedEnv
                (.callable callArgumentTarget sourceTarget)
                (site.child .callCallee))
              _ :=
          .compiled
            (bridge := calleeBridgeWrapped)
            (checkedEnv := checkedEnv)
            (target := .callable callArgumentTarget sourceTarget)
            (site := site.child .callCallee)
            (staticOutputFact_callableSubtype
              selectedCallable
              callArgumentTarget sourceTarget)
            (.refl (EmbeddedExprBridgeCore.producer_wellFormed calleeBridge))
        let argument_ok :
            StaticCheckedExprOk p helab Γ
              (compileCheck argumentHsrc checkedEnv callArgumentTarget
                (site.child .callArgument))
              _ :=
          .compiled
            (bridge := argumentBridgeWrapped)
            (checkedEnv := checkedEnv)
            (target := callArgumentTarget)
            (site := site.child .callArgument)
            (staticOutputFact_callParamTarget
              (staticOutputFact_ofView
                (EmbeddedExprBridgeCore.view argumentBridge)))
            (.refl (EmbeddedExprBridgeCore.producer_wellFormed argumentBridge))
        exact {
          calleeTy := _
          argumentTy := _
          returnTy := _
          callee_to_callable := .trans selectedCallable
            (.callable argument_subtype returnRefl)
          callee_ok := callee_ok
          argument_ok := argument_ok
          return_subtype := returnRefl }
  | .interIntro leftHsrc left rightHsrc right _ .. =>
      by
        let leftHead :=
          staticCompiledCallHead_ofCore
            (p := p)
            (helab := helab)
            (Γ := Γ)
            (sourceExpr := sourceExpr)
            (producerTy := _)
            (sourceTy := _)
            (hsrc := leftHsrc)
            (advertisedTy := _)
            (checkedEnv := checkedEnv)
            (sourceTarget := sourceTarget)
            (site := site)
            (checkedCallee := checkedCallee)
            (checkedArgument := checkedArgument)
            (parameterTarget := parameterTarget)
            (returnTarget := returnTarget)
            (returnObligation := returnObligation)
            left
            checked_eq
        have right_eq :
            compileCheck rightHsrc checkedEnv sourceTarget site =
              .call checkedCallee checkedArgument parameterTarget
                returnTarget returnObligation := by
          rw [compileCheck_sourceCoherent rightHsrc leftHsrc checkedEnv
            sourceTarget site]
          exact checked_eq
        let rightHead :=
          staticCompiledCallHead_ofCore
            (p := p)
            (helab := helab)
            (Γ := Γ)
            (sourceExpr := sourceExpr)
            (producerTy := _)
            (sourceTy := _)
            (hsrc := rightHsrc)
            (advertisedTy := _)
            (checkedEnv := checkedEnv)
            (sourceTarget := sourceTarget)
            (site := site)
            (checkedCallee := checkedCallee)
            (checkedArgument := checkedArgument)
            (parameterTarget := parameterTarget)
            (returnTarget := returnTarget)
            (returnObligation := returnObligation)
            right
            right_eq
        let callee_ok :
            StaticCheckedExprOk p helab Γ checkedCallee
              (.intersection leftHead.calleeTy rightHead.calleeTy) :=
          .intersection leftHead.callee_ok rightHead.callee_ok
        let argument_ok :
            StaticCheckedExprOk p helab Γ checkedArgument
              (.intersection leftHead.argumentTy rightHead.argumentTy) :=
          .intersection leftHead.argument_ok rightHead.argument_ok
        exact {
          calleeTy := .intersection leftHead.calleeTy rightHead.calleeTy
          argumentTy := .intersection leftHead.argumentTy rightHead.argumentTy
          returnTy := .intersection leftHead.returnTy rightHead.returnTy
          callee_to_callable := IsSubtype.callableMeet
            (.interLeft leftHead.callee_to_callable rightHead.callee_to_callable.sourceWellFormed)
            (.interRight rightHead.callee_to_callable leftHead.callee_to_callable.sourceWellFormed)
          callee_ok := callee_ok
          argument_ok := argument_ok
          return_subtype :=
            .interMono leftHead.return_subtype rightHead.return_subtype }
  | .sub _ inner .. =>
      staticCompiledCallHead_ofCore
        (p := p)
        (helab := helab)
        (Γ := Γ)
        (sourceExpr := sourceExpr)
        (producerTy := producerTy)
        (sourceTy := sourceTy)
        (hsrc := hsrc)
        (advertisedTy := _)
        (checkedEnv := checkedEnv)
        (sourceTarget := sourceTarget)
        (site := site)
        (checkedCallee := checkedCallee)
        (checkedArgument := checkedArgument)
        (parameterTarget := parameterTarget)
        (returnTarget := returnTarget)
        (returnObligation := returnObligation)
        inner
        checked_eq
  | .var .. =>
      by cases checked_eq
  | .constNone .. =>
      by cases checked_eq
  | .constTrue .. =>
      by cases checked_eq
  | .constFalse .. =>
      by cases checked_eq
  | .new .. =>
      by cases checked_eq
  | .attrAccess .. =>
      by cases checked_eq
  | .cond .. =>
      by cases checked_eq
  | .isInstance .. =>
      by cases checked_eq
  | .condIsInstance .. =>
      by cases checked_eq

private def staticCompiledCall_ofCore
    {sourceTy : GTy}
    {hsrc :
      GSrcInfer (embedClassTable p.classes) helab.core
        (embedTyEnv Γ) (embedExpr sourceExpr) sourceTy}
    (core :
      EmbeddedExprBridgeCore p.classes helab.core Γ sourceExpr producerTy
        sourceTy hsrc advertisedTy)
    (output : StaticOutputFact p helab producerTy sourceTarget)
    (checked_eq :
      compileCheck hsrc checkedEnv sourceTarget site =
        .call checkedCallee checkedArgument parameterTarget
          returnTarget returnObligation) :
    StaticCallDecomposition p helab Γ checkedCallee checkedArgument
      returnTarget returnObligation producerTy := by
  obtain ⟨return_eq, obligation_eq⟩ :=
    compileCheck_call_return_obligation hsrc checkedEnv sourceTarget site
      checkedCallee checkedArgument parameterTarget returnTarget
      returnObligation checked_eq
  cases return_eq
  cases obligation_eq
  let head :=
    staticCompiledCallHead_ofCore
      (p := p)
      (helab := helab)
      (Γ := Γ)
      (sourceExpr := sourceExpr)
      (producerTy := producerTy)
      (sourceTy := sourceTy)
      (hsrc := hsrc)
      (advertisedTy := advertisedTy)
      (checkedEnv := checkedEnv)
      (sourceTarget := sourceTarget)
      (site := site)
      (checkedCallee := checkedCallee)
      (checkedArgument := checkedArgument)
      (parameterTarget := parameterTarget)
      (returnTarget := checkedTargetOfGTy sourceTarget)
      (returnObligation := .hasType (.expression site) sourceTarget)
      core
      checked_eq
  let returnBoundary :
      StaticTypeBoundaryEvidence p helab head.returnTy
        (checkedTargetOfGTy sourceTarget)
        (.hasType (.expression site) sourceTarget) :=
    staticTypeBoundaryEvidence_precompose
      (staticTypeBoundaryEvidence_ofOutput output (.expression site) True.intro)
      (fun hvalue =>
        .sub hvalue head.return_subtype)
  exact ⟨
    head.calleeTy,
    head.argumentTy,
    head.returnTy,
    { callee_to_callable := head.callee_to_callable
      returnBoundary := returnBoundary },
    head.callee_ok,
    head.argument_ok,
    head.return_subtype⟩

private def staticCheckedExprOk_call_of_eq
    (expr : StaticCheckedExprOk p helab Γ checkedExpr outputTy)
    (checked_eq :
      checkedExpr =
        .call checkedCallee checkedArgument parameterTarget
          returnTarget returnObligation) :
    StaticCallDecomposition p helab Γ checkedCallee checkedArgument
      returnTarget returnObligation outputTy :=
  match expr with
  | .compiled bridge output output_subtype =>
      by
        rcases staticCompiledCall_ofCore
            (p := p)
            (helab := helab)
            (Γ := Γ)
            (sourceExpr := _)
            (producerTy := _)
            (sourceTy := _)
            (hsrc := bridge.hsrc)
            (advertisedTy := _)
            (checkedEnv := _)
            (sourceTarget := _)
            (site := _)
            (checkedCallee := checkedCallee)
            (checkedArgument := checkedArgument)
            (parameterTarget := parameterTarget)
            (returnTarget := returnTarget)
            (returnObligation := returnObligation)
            bridge.core
            output
            (by simpa using checked_eq) with
          ⟨calleeTy, argumentTy, returnTy, payload, callee_ok,
            argument_ok, return_subtype⟩
        exact ⟨calleeTy, argumentTy, returnTy, payload, callee_ok,
          argument_ok, .trans return_subtype output_subtype⟩
  | .call callee argument payload output_subtype =>
      by
        cases checked_eq
        exact ⟨_, _, _, payload, callee, argument, output_subtype⟩
  | .interIntro left right output_subtype =>
      by
        rcases staticCheckedExprOk_call_of_eq left checked_eq with
          ⟨leftCalleeTy, leftArgumentTy, leftReturnTy, leftPayload,
            leftCallee, leftArgument, leftSubtype⟩
        rcases staticCheckedExprOk_call_of_eq right checked_eq with
          ⟨rightCalleeTy, rightArgumentTy, rightReturnTy, rightPayload,
            rightCallee, rightArgument, rightSubtype⟩
        let callee_ok :
            StaticCheckedExprOk p helab Γ checkedCallee
              (.intersection leftCalleeTy rightCalleeTy) :=
          .intersection leftCallee rightCallee
        let argument_ok :
            StaticCheckedExprOk p helab Γ checkedArgument
              (.intersection leftArgumentTy rightArgumentTy) :=
          .intersection leftArgument rightArgument
        let returnBoundary :
            StaticTypeBoundaryEvidence p helab
              (.intersection leftReturnTy rightReturnTy)
              returnTarget returnObligation :=
          staticTypeBoundaryEvidence_precompose leftPayload.returnBoundary
            (fun hvalue =>
              .sub hvalue (.interLeft (.refl leftPayload.callee_to_callable.targetWellFormed.callable_return)
                rightPayload.callee_to_callable.targetWellFormed.callable_return))
        exact ⟨
          .intersection leftCalleeTy rightCalleeTy,
          .intersection leftArgumentTy rightArgumentTy,
          .intersection leftReturnTy rightReturnTy,
          staticCallPayloadEvidence_interIntro
            leftPayload rightPayload returnBoundary,
          callee_ok,
          argument_ok,
          .trans
            (.interMono leftSubtype rightSubtype)
            output_subtype⟩
  | .sub inner output_subtype =>
      by
        rcases staticCheckedExprOk_call_of_eq inner checked_eq with
          ⟨calleeTy, argumentTy, returnTy, payload, callee_ok,
            argument_ok, return_subtype⟩
        exact ⟨calleeTy, argumentTy, returnTy, payload, callee_ok,
          argument_ok, .trans return_subtype output_subtype⟩
  | .var .. =>
      by cases checked_eq
  | .constNone .. =>
      by cases checked_eq
  | .constTrue .. =>
      by cases checked_eq
  | .constFalse .. =>
      by cases checked_eq
  | .new .. =>
      by cases checked_eq
  | .isInstance .. =>
      by cases checked_eq
  | .enforce .. =>
      by cases checked_eq
  | .dynAttrAccess .. =>
      by cases checked_eq
  | .cond .. =>
      by cases checked_eq
  | .condIsInstance .. =>
      by cases checked_eq

private def staticCheckedExprOk_call
    (expr :
      StaticCheckedExprOk p helab Γ
        (.call checkedCallee checkedArgument parameterTarget
          returnTarget returnObligation) outputTy) :
    StaticCallDecomposition p helab Γ checkedCallee checkedArgument
      returnTarget returnObligation outputTy :=
  staticCheckedExprOk_call_of_eq expr rfl

private def StaticCondDecomposition
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (Γ : TyEnv)
    (checkedTest checkedThen checkedElse : CheckedExpr)
    (outputTy : Ty) : Prop :=
  ∃ thenTy elseTy,
    StaticCheckedExprOk p helab Γ checkedTest (.class_ boolClass) ∧
    StaticCheckedExprOk p helab Γ checkedThen thenTy ∧
    StaticCheckedExprOk p helab Γ checkedElse elseTy ∧
    IsSubtype helab.core.toOriginalWellFormedClassHierarchy (.union thenTy elseTy) outputTy

/-- Structural head for a compiled ordinary conditional. It stores the source
bridges for the test and branches, but delays construction of branch checked
evidence until the caller supplies the output fact for the combined producer. -/
private inductive StaticCompiledCondHead
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (Γ : TyEnv)
    (checkedEnv : GTyEnv)
    (sourceTarget : GTy)
    (site : SourceExpressionSite)
    (sourceTy : GTy)
    (checkedTest checkedThen checkedElse : CheckedExpr) :
    Expr → Ty → Type where
  | cond
      -- Caller-facing type for packaging the condition bridge.
      (conditionAdvertised : Ty)
      -- Embedded bridge for the condition source expression.
      (conditionBridge :
        EmbeddedExprBridge p.classes helab.core Γ conditionExpr
          conditionAdvertised)
      -- Static evidence that the condition producer is a boolean.
      (condition_bool_subtype :
        IsSubtype helab.core.toOriginalWellFormedClassHierarchy conditionBridge.producerTy (.class_ boolClass))
      -- Caller-facing type for packaging the positive branch bridge.
      (thenAdvertised : Ty)
      -- Embedded bridge for the positive branch.
      (thenBridge :
        EmbeddedExprBridge p.classes helab.core Γ thenExpr thenAdvertised)
      -- Caller-facing type for packaging the negative branch bridge.
      (elseAdvertised : Ty)
      -- Embedded bridge for the negative branch.
      (elseBridge :
        EmbeddedExprBridge p.classes helab.core Γ elseExpr elseAdvertised)
      -- Checked condition syntax produced by compiling the condition bridge
      -- at the boolean target.
      (checkedTest_eq :
        checkedTest =
          compileCheck conditionBridge.hsrc checkedEnv (.class_ boolClass)
            (site.child .conditionTest))
      -- Checked positive branch syntax produced by compiling the positive
      -- branch at the conditional's requested target.
      (checkedThen_eq :
        checkedThen =
          compileCheck thenBridge.hsrc checkedEnv sourceTarget
            (site.child .conditionThen))
      -- Checked negative branch syntax produced by compiling the negative
      -- branch at the conditional's requested target.
      (checkedElse_eq :
        checkedElse =
          compileCheck elseBridge.hsrc checkedEnv sourceTarget
            (site.child .conditionElse))
      -- Source result of the conditional is the source union of branch results.
      (source_eq :
        sourceTy = .union thenBridge.srcTy elseBridge.srcTy)
      -- The branch producer union flows to the conditional producer.
      (result_subtype :
        IsSubtype helab.core.toOriginalWellFormedClassHierarchy
          (.union thenBridge.producerTy elseBridge.producerTy)
          producerTy) :
      StaticCompiledCondHead p helab Γ checkedEnv sourceTarget site
        sourceTy checkedTest checkedThen checkedElse
        (.cond conditionExpr thenExpr elseExpr)
        producerTy

private def staticCompiledCondHead_decomposition
    (head :
      StaticCompiledCondHead p helab Γ checkedEnv sourceTarget site
        sourceTy checkedTest checkedThen checkedElse sourceExpr producerTy)
    (output : StaticOutputFact p helab producerTy sourceTarget) :
    StaticCondDecomposition p helab Γ checkedTest checkedThen checkedElse
      producerTy := by
  cases head with
  | cond _ conditionBridge condition_bool_subtype
      _ thenBridge _ elseBridge checkedTest_eq
      checkedThen_eq checkedElse_eq _source_eq result_subtype =>
      let thenFact :
          StaticOutputFact p helab thenBridge.producerTy sourceTarget :=
        staticOutputFact_precompose output
          (fun hvalue =>
            .sub (.unionLeft hvalue)
              result_subtype)
      let elseFact :
          StaticOutputFact p helab elseBridge.producerTy sourceTarget :=
        staticOutputFact_precompose output
          (fun hvalue =>
            .sub (.unionRight hvalue)
              result_subtype)
      have conditionOk :
          StaticCheckedExprOk p helab Γ checkedTest (.class_ boolClass) := by
        rw [checkedTest_eq]
        exact .compiled
          (bridge := conditionBridge)
          (checkedEnv := checkedEnv)
          (target := .class_ boolClass)
          (site := site.child .conditionTest)
          (staticOutputFact_staticSubtypeEmbed condition_bool_subtype)
          condition_bool_subtype
      have thenOk :
          StaticCheckedExprOk p helab Γ checkedThen
            thenBridge.producerTy := by
        rw [checkedThen_eq]
        exact .compiled
          (bridge := thenBridge)
          (checkedEnv := checkedEnv)
          (target := sourceTarget)
          (site := site.child .conditionThen)
          thenFact
          (.refl thenBridge.producer_wellFormed)
      have elseOk :
          StaticCheckedExprOk p helab Γ checkedElse
            elseBridge.producerTy := by
        rw [checkedElse_eq]
        exact .compiled
          (bridge := elseBridge)
          (checkedEnv := checkedEnv)
          (target := sourceTarget)
          (site := site.child .conditionElse)
          elseFact
          (.refl elseBridge.producer_wellFormed)
      exact ⟨thenBridge.producerTy, elseBridge.producerTy,
        conditionOk, thenOk, elseOk, result_subtype⟩

private def staticCompiledCondHead_ofCore
    {sourceTy : GTy}
    {hsrc :
      GSrcInfer (embedClassTable p.classes) helab.core
        (embedTyEnv Γ) (embedExpr sourceExpr) sourceTy}
    (core :
      EmbeddedExprBridgeCore p.classes helab.core Γ sourceExpr producerTy
        sourceTy hsrc advertisedTy)
    (checked_eq :
      compileCheck hsrc checkedEnv sourceTarget site =
        .cond checkedTest checkedThen checkedElse)
    (test_not_isInstance : ∀ x C, checkedTest ≠ .isInstance x C) :
    StaticCompiledCondHead p helab Γ checkedEnv sourceTarget site
      sourceTy checkedTest checkedThen checkedElse sourceExpr producerTy :=
  match core with
  | .cond _ conditionHsrc conditionBridge condition_bool_subtype _
      thenHsrc thenBridge elseHsrc elseBridge output_subtype .. =>
      by
        simp [compileCheck] at checked_eq
        rcases checked_eq with ⟨condition_eq, then_eq, else_eq⟩
        cases condition_eq
        cases then_eq
        cases else_eq
        let conditionBridgeWrapped :
            EmbeddedExprBridge p.classes helab.core Γ _ _ :=
          { producerTy := _
            srcTy := _
            hsrc := conditionHsrc
            core := conditionBridge }
        let thenBridgeWrapped :
            EmbeddedExprBridge p.classes helab.core Γ _ _ :=
          { producerTy := _
            srcTy := _
            hsrc := thenHsrc
            core := thenBridge }
        let elseBridgeWrapped :
            EmbeddedExprBridge p.classes helab.core Γ _ _ :=
          { producerTy := _
            srcTy := _
            hsrc := elseHsrc
            core := elseBridge }
        exact .cond
          _
          conditionBridgeWrapped
          condition_bool_subtype
          _
          thenBridgeWrapped
          _
          elseBridgeWrapped
          rfl
          rfl
          rfl
          rfl
          (.refl (output_subtype.sourceWellFormed))
  | .interIntro leftHsrc left rightHsrc right _ .. =>
      by
        let leftHead :=
          staticCompiledCondHead_ofCore
            (p := p)
            (helab := helab)
            (Γ := Γ)
            (sourceExpr := sourceExpr)
            (producerTy := _)
            (sourceTy := _)
            (hsrc := leftHsrc)
            (advertisedTy := _)
            (checkedEnv := checkedEnv)
            (sourceTarget := sourceTarget)
            (site := site)
            (checkedTest := checkedTest)
            (checkedThen := checkedThen)
            (checkedElse := checkedElse)
            left
            checked_eq
            test_not_isInstance
        have right_eq :
            compileCheck rightHsrc checkedEnv sourceTarget site =
              .cond checkedTest checkedThen checkedElse := by
          rw [compileCheck_sourceCoherent rightHsrc leftHsrc checkedEnv
            sourceTarget site]
          exact checked_eq
        let rightHead :=
          staticCompiledCondHead_ofCore
            (p := p)
            (helab := helab)
            (Γ := Γ)
            (sourceExpr := sourceExpr)
            (producerTy := _)
            (sourceTy := _)
            (hsrc := rightHsrc)
            (advertisedTy := _)
            (checkedEnv := checkedEnv)
            (sourceTarget := sourceTarget)
            (site := site)
            (checkedTest := checkedTest)
            (checkedThen := checkedThen)
            (checkedElse := checkedElse)
            right
            right_eq
            test_not_isInstance
        cases leftHead with
        | cond conditionAdvertised conditionBridge condition_bool_subtype
            _ thenBridge _ elseBridge
            checkedTest_eq checkedThen_eq checkedElse_eq source_eq
            result_subtype =>
            cases rightHead with
            | cond _ _
                _ thenAdvertisedRight thenBridgeRight
                elseAdvertisedRight elseBridgeRight _
                _ _ source_eqRight
                result_subtypeRight =>
                have branch_source_eq :
                    GTy.union thenBridge.srcTy elseBridge.srcTy =
                      GTy.union thenBridgeRight.srcTy elseBridgeRight.srcTy := by
                  rw [← source_eq, source_eqRight]
                have then_source_eq :
                    thenBridge.srcTy = thenBridgeRight.srcTy :=
                  gty_union_left_injective branch_source_eq
                have else_source_eq :
                    elseBridge.srcTy = elseBridgeRight.srcTy :=
                  gty_union_right_injective branch_source_eq
                cases thenBridgeRight with
                | mk rightThenProducer _ rightThenHsrc
                    rightThenCore =>
                cases elseBridgeRight with
                | mk rightElseProducer _ rightElseHsrc
                    rightElseCore =>
                cases then_source_eq
                cases else_source_eq
                let thenBridgeRightAtLeft :
                    EmbeddedExprBridge p.classes helab.core Γ _
                      thenAdvertisedRight :=
                  { producerTy := rightThenProducer
                    srcTy := thenBridge.srcTy
                    hsrc := rightThenHsrc
                    core := rightThenCore }
                let thenProducer :=
                  Ty.intersection thenBridge.producerTy
                    thenBridgeRightAtLeft.producerTy
                let thenProducerWellFormed :
                    WellFormedTy p.classes thenProducer :=
                  .intersection thenBridge.producer_wellFormed
                    thenBridgeRightAtLeft.producer_wellFormed
                let thenCore :
                    EmbeddedExprBridgeCore p.classes helab.core Γ _ thenProducer
                      thenBridge.srcTy thenBridge.hsrc thenProducer :=
                  .interIntro
                    thenBridge.hsrc
                    thenBridge.core
                    thenBridgeRightAtLeft.hsrc
                    thenBridgeRightAtLeft.core
                    (.refl thenProducerWellFormed)
                let thenBridgeCombined :
                    EmbeddedExprBridge p.classes helab.core Γ _ thenProducer :=
                  { producerTy := thenProducer
                    srcTy := thenBridge.srcTy
                    hsrc := thenBridge.hsrc
                    core := thenCore }
                let elseBridgeRightAtLeft :
                    EmbeddedExprBridge p.classes helab.core Γ _
                      elseAdvertisedRight :=
                  { producerTy := rightElseProducer
                    srcTy := elseBridge.srcTy
                    hsrc := rightElseHsrc
                    core := rightElseCore }
                let elseProducer :=
                  Ty.intersection elseBridge.producerTy
                    elseBridgeRightAtLeft.producerTy
                let elseProducerWellFormed :
                    WellFormedTy p.classes elseProducer :=
                  .intersection elseBridge.producer_wellFormed
                    elseBridgeRightAtLeft.producer_wellFormed
                let elseCore :
                    EmbeddedExprBridgeCore p.classes helab.core Γ _ elseProducer
                      elseBridge.srcTy elseBridge.hsrc elseProducer :=
                  .interIntro
                    elseBridge.hsrc
                    elseBridge.core
                    elseBridgeRightAtLeft.hsrc
                    elseBridgeRightAtLeft.core
                    (.refl elseProducerWellFormed)
                let elseBridgeCombined :
                    EmbeddedExprBridge p.classes helab.core Γ _ elseProducer :=
                  { producerTy := elseProducer
                    srcTy := elseBridge.srcTy
                    hsrc := elseBridge.hsrc
                    core := elseCore }
                let combined_result_subtype :
                    IsSubtype helab.core.toOriginalWellFormedClassHierarchy
                      (.union thenProducer elseProducer)
                      (.intersection _ _) :=
                  combinedUnionResult_subtype result_subtype result_subtypeRight
                exact .cond
                  conditionAdvertised
                  conditionBridge
                  condition_bool_subtype
                  thenProducer
                  thenBridgeCombined
                  elseProducer
                  elseBridgeCombined
                  checkedTest_eq
                  checkedThen_eq
                  checkedElse_eq
                  source_eq
                  combined_result_subtype
  | .sub _ inner .. =>
      staticCompiledCondHead_ofCore
        (p := p)
        (helab := helab)
        (Γ := Γ)
        (sourceExpr := sourceExpr)
        (producerTy := producerTy)
        (sourceTy := sourceTy)
        (hsrc := hsrc)
        (advertisedTy := _)
        (checkedEnv := checkedEnv)
        (sourceTarget := sourceTarget)
        (site := site)
        (checkedTest := checkedTest)
        (checkedThen := checkedThen)
        (checkedElse := checkedElse)
        inner
        checked_eq
        test_not_isInstance
  | .condIsInstance (x := x) (C := C) .. =>
      by
        simp [compileCheck] at checked_eq
        rcases checked_eq with ⟨test_eq, _then_eq, _else_eq⟩
        exact False.elim (test_not_isInstance x C test_eq.symm)
  | .var .. =>
      by cases checked_eq
  | .constNone .. =>
      by cases checked_eq
  | .constTrue .. =>
      by cases checked_eq
  | .constFalse .. =>
      by cases checked_eq
  | .new .. =>
      by cases checked_eq
  | .attrAccess .. =>
      by cases checked_eq
  | .call .. =>
      by cases checked_eq
  | .isInstance .. =>
      by cases checked_eq

private def staticCompiledCond_ofCore
    {sourceTy : GTy}
    {hsrc :
      GSrcInfer (embedClassTable p.classes) helab.core
        (embedTyEnv Γ) (embedExpr sourceExpr) sourceTy}
    (core :
      EmbeddedExprBridgeCore p.classes helab.core Γ sourceExpr producerTy
        sourceTy hsrc advertisedTy)
    (output : StaticOutputFact p helab producerTy sourceTarget)
    (checked_eq :
      compileCheck hsrc checkedEnv sourceTarget site =
        .cond checkedTest checkedThen checkedElse)
    (test_not_isInstance : ∀ x C, checkedTest ≠ .isInstance x C) :
    StaticCondDecomposition p helab Γ checkedTest checkedThen checkedElse
      producerTy :=
  staticCompiledCondHead_decomposition
    (staticCompiledCondHead_ofCore core checked_eq test_not_isInstance)
    output

private def staticCheckedExprOk_cond_of_eq
    (expr : StaticCheckedExprOk p helab Γ checkedExpr outputTy)
    (checked_eq :
      checkedExpr = .cond checkedTest checkedThen checkedElse)
    (test_not_isInstance : ∀ x C, checkedTest ≠ .isInstance x C) :
    StaticCondDecomposition p helab Γ checkedTest checkedThen checkedElse
      outputTy :=
  match expr with
  | .compiled bridge output output_subtype =>
      by
        rcases staticCompiledCond_ofCore
            (p := p)
            (helab := helab)
            (Γ := Γ)
            (sourceExpr := _)
            (producerTy := _)
            (sourceTy := _)
            (hsrc := bridge.hsrc)
            (advertisedTy := _)
            (checkedEnv := _)
            (sourceTarget := _)
            (site := _)
            (checkedTest := checkedTest)
            (checkedThen := checkedThen)
            (checkedElse := checkedElse)
            bridge.core
            output
            (by simpa using checked_eq)
            test_not_isInstance with
          ⟨thenTy, elseTy, test_ok, then_ok, else_ok,
            result_subtype⟩
        exact ⟨thenTy, elseTy, test_ok, then_ok, else_ok,
          .trans result_subtype output_subtype⟩
  | .cond _ test thenBranch elseBranch output_subtype =>
      by
        cases checked_eq
        exact ⟨_, _, test, thenBranch, elseBranch, output_subtype⟩
  | .condIsInstance (x := x) (className := className) .. =>
      by
        cases checked_eq
        exact False.elim (test_not_isInstance x className rfl)
  | .interIntro left right output_subtype =>
      by
        rcases staticCheckedExprOk_cond_of_eq left checked_eq
            test_not_isInstance with
          ⟨leftThenTy, leftElseTy, leftTest, leftThen, leftElse,
            leftSubtype⟩
        rcases staticCheckedExprOk_cond_of_eq right checked_eq
            test_not_isInstance with
          ⟨rightThenTy, rightElseTy, _, rightThen, rightElse,
            rightSubtype⟩
        let thenOk :
            StaticCheckedExprOk p helab Γ checkedThen
              (.intersection leftThenTy rightThenTy) :=
          .intersection leftThen rightThen
        let elseOk :
            StaticCheckedExprOk p helab Γ checkedElse
              (.intersection leftElseTy rightElseTy) :=
          .intersection leftElse rightElse
        let result_subtype :
            IsSubtype helab.core.toOriginalWellFormedClassHierarchy
              (.union (.intersection leftThenTy rightThenTy)
                (.intersection leftElseTy rightElseTy))
              (.intersection _ _) :=
          combinedUnionResult_subtype leftSubtype rightSubtype
        exact ⟨
          .intersection leftThenTy rightThenTy,
          .intersection leftElseTy rightElseTy,
          leftTest,
          thenOk,
          elseOk,
          .trans result_subtype output_subtype⟩
  | .sub inner output_subtype =>
      by
        rcases staticCheckedExprOk_cond_of_eq inner checked_eq
            test_not_isInstance with
          ⟨thenTy, elseTy, test_ok, then_ok, else_ok, result_subtype⟩
        exact ⟨thenTy, elseTy, test_ok, then_ok, else_ok,
          .trans result_subtype output_subtype⟩
  | .var .. =>
      by cases checked_eq
  | .constNone .. =>
      by cases checked_eq
  | .constTrue .. =>
      by cases checked_eq
  | .constFalse .. =>
      by cases checked_eq
  | .new .. =>
      by cases checked_eq
  | .isInstance .. =>
      by cases checked_eq
  | .enforce .. =>
      by cases checked_eq
  | .dynAttrAccess .. =>
      by cases checked_eq
  | .call .. =>
      by cases checked_eq

private def staticCheckedExprOk_cond
    (expr :
      StaticCheckedExprOk p helab Γ
        (.cond checkedTest checkedThen checkedElse) outputTy)
    (test_not_isInstance : ∀ x C, checkedTest ≠ .isInstance x C) :
    StaticCondDecomposition p helab Γ checkedTest checkedThen checkedElse
      outputTy :=
  staticCheckedExprOk_cond_of_eq expr rfl test_not_isInstance

private def StaticCondIsInstanceDecomposition
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (Γ : TyEnv)
    (x className : Identifier)
    (checkedThen checkedElse : CheckedExpr)
    (outputTy : Ty) : Prop :=
  ∃ variableTy,
    Γ.lookup x = some variableTy ∧
    StaticCheckedExprOk p helab
      (Γ.update x (.intersection variableTy (.class_ className)))
      checkedThen outputTy ∧
    StaticCheckedExprOk p helab
      (Γ.update x (.intersection variableTy (.negClass className)))
      checkedElse outputTy

/-- Structural head for a compiled `isInstance` conditional. The checked
machine evaluates one branch under a refined static environment, so the head
keeps the branch bridges in those refined environments and delays boundary
evidence until the combined producer is known. -/
private inductive StaticCompiledCondIsInstanceHead
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (Γ : TyEnv)
    (checkedEnv : GTyEnv)
    (sourceTarget : GTy)
    (site : SourceExpressionSite)
    (sourceTy : GTy)
    (x className : Identifier)
    (checkedThen checkedElse : CheckedExpr) :
    Expr → Ty → Type where
  | cond
      -- Static type of the binding refined by the runtime test.
      (variableTy : Ty)
      -- Static binding refined by the runtime test.
      (lookup : Γ.lookup x = some variableTy)
      -- Caller-facing type for packaging the positive branch bridge.
      (thenAdvertised : Ty)
      -- Embedded bridge for the positive branch under the class refinement.
      (thenBridge :
        EmbeddedExprBridge p.classes helab.core
          (Γ.update x (.intersection variableTy (.class_ className)))
          thenExpr thenAdvertised)
      -- Caller-facing type for packaging the negative branch bridge.
      (elseAdvertised : Ty)
      -- Embedded bridge for the negative branch under the negated refinement.
      (elseBridge :
        EmbeddedExprBridge p.classes helab.core
          (Γ.update x (.intersection variableTy (.negClass className)))
          elseExpr elseAdvertised)
      -- Checked positive branch syntax produced at the conditional target.
      (checkedThen_eq :
        checkedThen =
          compileCheck thenBridge.hsrc
            (condIsInstanceBranchEnvironments
              (embedClassTable p.classes) checkedEnv x className).1
            sourceTarget
            (site.child .conditionThen))
      -- Checked negative branch syntax produced at the conditional target.
      (checkedElse_eq :
        checkedElse =
          compileCheck elseBridge.hsrc
            (condIsInstanceBranchEnvironments
              (embedClassTable p.classes) checkedEnv x className).2
            sourceTarget
            (site.child .conditionElse))
      -- Source result of the conditional is the source union of branch results.
      (source_eq :
        sourceTy = .union thenBridge.srcTy elseBridge.srcTy)
      -- The branch producer union flows to the conditional producer.
      (result_subtype :
        IsSubtype helab.core.toOriginalWellFormedClassHierarchy
          (.union thenBridge.producerTy elseBridge.producerTy)
          producerTy) :
      StaticCompiledCondIsInstanceHead p helab Γ checkedEnv sourceTarget site
        sourceTy x className checkedThen checkedElse
        (.cond (.isInstance x className) thenExpr elseExpr)
        producerTy

private def staticCompiledCondIsInstanceHead_decomposition
    (head :
      StaticCompiledCondIsInstanceHead p helab Γ checkedEnv sourceTarget site
        sourceTy x className checkedThen checkedElse sourceExpr producerTy)
    (output : StaticOutputFact p helab producerTy sourceTarget) :
    StaticCondIsInstanceDecomposition p helab Γ x className checkedThen
      checkedElse producerTy := by
  cases head with
  | cond variableTy lookup _ thenBridge _ elseBridge
      checkedThen_eq checkedElse_eq _source_eq result_subtype =>
      let thenFact :
          StaticOutputFact p helab thenBridge.producerTy sourceTarget :=
        staticOutputFact_precompose output
          (fun hvalue =>
            .sub (.unionLeft hvalue)
              result_subtype)
      let elseFact :
          StaticOutputFact p helab elseBridge.producerTy sourceTarget :=
        staticOutputFact_precompose output
          (fun hvalue =>
            .sub (.unionRight hvalue)
              result_subtype)
      have thenProducerOk :
          StaticCheckedExprOk p helab
            (Γ.update x (.intersection variableTy (.class_ className)))
            checkedThen thenBridge.producerTy := by
        rw [checkedThen_eq]
        exact .compiled
          (bridge := thenBridge)
          (checkedEnv :=
            (condIsInstanceBranchEnvironments
              (embedClassTable p.classes) checkedEnv x className).1)
          (target := sourceTarget)
          (site := site.child .conditionThen)
          thenFact
          (.refl thenBridge.producer_wellFormed)
      have elseProducerOk :
          StaticCheckedExprOk p helab
            (Γ.update x (.intersection variableTy (.negClass className)))
            checkedElse elseBridge.producerTy := by
        rw [checkedElse_eq]
        exact .compiled
          (bridge := elseBridge)
          (checkedEnv :=
            (condIsInstanceBranchEnvironments
              (embedClassTable p.classes) checkedEnv x className).2)
          (target := sourceTarget)
          (site := site.child .conditionElse)
          elseFact
          (.refl elseBridge.producer_wellFormed)
      exact ⟨variableTy, lookup,
        staticCheckedExprOk_unionLeftOutput thenProducerOk result_subtype,
        staticCheckedExprOk_unionRightOutput elseProducerOk result_subtype⟩

private def staticCompiledCondIsInstanceHead_ofCore
    {sourceTy : GTy}
    {hsrc :
      GSrcInfer (embedClassTable p.classes) helab.core
        (embedTyEnv Γ) (embedExpr sourceExpr) sourceTy}
    (core :
      EmbeddedExprBridgeCore p.classes helab.core Γ sourceExpr producerTy
        sourceTy hsrc advertisedTy)
    (checked_eq :
      compileCheck hsrc checkedEnv sourceTarget site =
        .cond (.isInstance x className) checkedThen checkedElse) :
    StaticCompiledCondIsInstanceHead p helab Γ checkedEnv sourceTarget site
      sourceTy x className checkedThen checkedElse sourceExpr producerTy :=
  match core with
  | .cond _ conditionHsrc _ _ _ .. =>
      by
        simp [compileCheck] at checked_eq
        rcases checked_eq with ⟨test_eq, _then_eq, _else_eq⟩
        exact False.elim
          (compileCheck_ne_isInstance conditionHsrc checkedEnv
            (.class_ boolClass) (site.child .conditionTest)
            x className test_eq)
  | .condIsInstance (x := coreX) (C := coreClass)
      (variableTy := variableTy)
      lookup _ _ thenHsrc thenBridge elseHsrc elseBridge
      output_subtype .. =>
      by
        simp [compileCheck] at checked_eq
        rcases checked_eq with ⟨test_eq, then_eq, else_eq⟩
        rcases test_eq with ⟨hx, hclass⟩
        cases hx
        cases hclass
        let thenBridgeWrapped :
            EmbeddedExprBridge p.classes helab.core
              (Γ.update x (.intersection variableTy (.class_ className)))
              _ _ :=
          { producerTy := _
            srcTy := _
            hsrc := thenHsrc
            core := thenBridge }
        let elseBridgeWrapped :
            EmbeddedExprBridge p.classes helab.core
              (Γ.update x (.intersection variableTy (.negClass className)))
              _ _ :=
          { producerTy := _
            srcTy := _
            hsrc := elseHsrc
            core := elseBridge }
        have checkedThen_eq :
            checkedThen =
              compileCheck thenBridgeWrapped.hsrc
                (condIsInstanceBranchEnvironments
                  (embedClassTable p.classes) checkedEnv x className).1
                sourceTarget
                (site.child .conditionThen) := by
          rw [← then_eq]
          simpa [thenBridgeWrapped] using
            compileCheck_cast_env
              (embedTyEnv_update_isInstanceThen Γ x variableTy className)
              thenHsrc
              (condIsInstanceBranchEnvironments
                (embedClassTable p.classes) checkedEnv x className).1
              sourceTarget
              (site.child .conditionThen)
        have checkedElse_eq :
            checkedElse =
              compileCheck elseBridgeWrapped.hsrc
                (condIsInstanceBranchEnvironments
                  (embedClassTable p.classes) checkedEnv x className).2
                sourceTarget
                (site.child .conditionElse) := by
          rw [← else_eq]
          simpa [elseBridgeWrapped] using
            compileCheck_cast_env
              (embedTyEnv_update_isInstanceElse Γ x variableTy className)
              elseHsrc
              (condIsInstanceBranchEnvironments
                (embedClassTable p.classes) checkedEnv x className).2
              sourceTarget
              (site.child .conditionElse)
        exact .cond
          variableTy
          lookup
          _
          thenBridgeWrapped
          _
          elseBridgeWrapped
          checkedThen_eq
          checkedElse_eq
          rfl
          (.refl output_subtype.sourceWellFormed)
  | .interIntro leftHsrc left rightHsrc right _ .. =>
      by
        let leftHead :=
          staticCompiledCondIsInstanceHead_ofCore
            (p := p)
            (helab := helab)
            (Γ := Γ)
            (sourceExpr := sourceExpr)
            (producerTy := _)
            (sourceTy := _)
            (hsrc := leftHsrc)
            (advertisedTy := _)
            (checkedEnv := checkedEnv)
            (sourceTarget := sourceTarget)
            (site := site)
            (x := x)
            (className := className)
            (checkedThen := checkedThen)
            (checkedElse := checkedElse)
            left
            checked_eq
        have right_eq :
            compileCheck rightHsrc checkedEnv sourceTarget site =
              .cond (.isInstance x className) checkedThen checkedElse := by
          rw [compileCheck_sourceCoherent rightHsrc leftHsrc checkedEnv
            sourceTarget site]
          exact checked_eq
        let rightHead :=
          staticCompiledCondIsInstanceHead_ofCore
            (p := p)
            (helab := helab)
            (Γ := Γ)
            (sourceExpr := sourceExpr)
            (producerTy := _)
            (sourceTy := _)
            (hsrc := rightHsrc)
            (advertisedTy := _)
            (checkedEnv := checkedEnv)
            (sourceTarget := sourceTarget)
            (site := site)
            (x := x)
            (className := className)
            (checkedThen := checkedThen)
            (checkedElse := checkedElse)
            right
            right_eq
        cases leftHead with
        | cond variableTy lookup _ thenBridge _
            elseBridge checkedThen_eq checkedElse_eq source_eq result_subtype =>
            cases rightHead with
            | cond variableTyRight lookupRight thenAdvertisedRight
                thenBridgeRight elseAdvertisedRight elseBridgeRight
                _ _ source_eqRight
                result_subtypeRight =>
                have variable_eq : variableTy = variableTyRight := by
                  rw [lookup] at lookupRight
                  cases lookupRight
                  rfl
                cases variable_eq
                have branch_source_eq :
                    GTy.union thenBridge.srcTy elseBridge.srcTy =
                      GTy.union thenBridgeRight.srcTy elseBridgeRight.srcTy := by
                  rw [← source_eq, source_eqRight]
                have then_source_eq :
                    thenBridge.srcTy = thenBridgeRight.srcTy :=
                  gty_union_left_injective branch_source_eq
                have else_source_eq :
                    elseBridge.srcTy = elseBridgeRight.srcTy :=
                  gty_union_right_injective branch_source_eq
                cases thenBridgeRight with
                | mk rightThenProducer _ rightThenHsrc
                    rightThenCore =>
                cases elseBridgeRight with
                | mk rightElseProducer _ rightElseHsrc
                    rightElseCore =>
                cases then_source_eq
                cases else_source_eq
                let thenBridgeRightAtLeft :
                    EmbeddedExprBridge p.classes helab.core
                      (Γ.update x (.intersection variableTy (.class_ className)))
                      _ thenAdvertisedRight :=
                  { producerTy := rightThenProducer
                    srcTy := thenBridge.srcTy
                    hsrc := rightThenHsrc
                    core := rightThenCore }
                let thenProducer :=
                  Ty.intersection thenBridge.producerTy
                    thenBridgeRightAtLeft.producerTy
                let thenProducerWellFormed :
                    WellFormedTy p.classes thenProducer :=
                  .intersection thenBridge.producer_wellFormed
                    thenBridgeRightAtLeft.producer_wellFormed
                let thenCore :
                    EmbeddedExprBridgeCore p.classes helab.core
                      (Γ.update x (.intersection variableTy (.class_ className)))
                      _ thenProducer thenBridge.srcTy thenBridge.hsrc
                      thenProducer :=
                  .interIntro
                    thenBridge.hsrc
                    thenBridge.core
                    thenBridgeRightAtLeft.hsrc
                    thenBridgeRightAtLeft.core
                    (.refl thenProducerWellFormed)
                let thenBridgeCombined :
                    EmbeddedExprBridge p.classes helab.core
                      (Γ.update x (.intersection variableTy (.class_ className)))
                      _ thenProducer :=
                  { producerTy := thenProducer
                    srcTy := thenBridge.srcTy
                    hsrc := thenBridge.hsrc
                    core := thenCore }
                let elseBridgeRightAtLeft :
                    EmbeddedExprBridge p.classes helab.core
                      (Γ.update x (.intersection variableTy (.negClass className)))
                      _ elseAdvertisedRight :=
                  { producerTy := rightElseProducer
                    srcTy := elseBridge.srcTy
                    hsrc := rightElseHsrc
                    core := rightElseCore }
                let elseProducer :=
                  Ty.intersection elseBridge.producerTy
                    elseBridgeRightAtLeft.producerTy
                let elseProducerWellFormed :
                    WellFormedTy p.classes elseProducer :=
                  .intersection elseBridge.producer_wellFormed
                    elseBridgeRightAtLeft.producer_wellFormed
                let elseCore :
                    EmbeddedExprBridgeCore p.classes helab.core
                      (Γ.update x (.intersection variableTy (.negClass className)))
                      _ elseProducer elseBridge.srcTy elseBridge.hsrc
                      elseProducer :=
                  .interIntro
                    elseBridge.hsrc
                    elseBridge.core
                    elseBridgeRightAtLeft.hsrc
                    elseBridgeRightAtLeft.core
                    (.refl elseProducerWellFormed)
                let elseBridgeCombined :
                    EmbeddedExprBridge p.classes helab.core
                      (Γ.update x (.intersection variableTy (.negClass className)))
                      _ elseProducer :=
                  { producerTy := elseProducer
                    srcTy := elseBridge.srcTy
                    hsrc := elseBridge.hsrc
                    core := elseCore }
                let combined_result_subtype :
                    IsSubtype helab.core.toOriginalWellFormedClassHierarchy
                      (.union thenProducer elseProducer)
                      (.intersection _ _) :=
                  combinedUnionResult_subtype result_subtype result_subtypeRight
                exact .cond
                  variableTy
                  lookup
                  thenProducer
                  thenBridgeCombined
                  elseProducer
                  elseBridgeCombined
                  checkedThen_eq
                  checkedElse_eq
                  source_eq
                  combined_result_subtype
  | .sub _ inner .. =>
      staticCompiledCondIsInstanceHead_ofCore
        (p := p)
        (helab := helab)
        (Γ := Γ)
        (sourceExpr := sourceExpr)
        (producerTy := producerTy)
        (sourceTy := sourceTy)
        (hsrc := hsrc)
        (advertisedTy := _)
        (checkedEnv := checkedEnv)
        (sourceTarget := sourceTarget)
        (site := site)
        (x := x)
        (className := className)
        (checkedThen := checkedThen)
        (checkedElse := checkedElse)
        inner
        checked_eq
  | .var .. =>
      by cases checked_eq
  | .constNone .. =>
      by cases checked_eq
  | .constTrue .. =>
      by cases checked_eq
  | .constFalse .. =>
      by cases checked_eq
  | .new .. =>
      by cases checked_eq
  | .attrAccess .. =>
      by cases checked_eq
  | .call .. =>
      by cases checked_eq
  | .isInstance .. =>
      by cases checked_eq

private def staticCompiledCondIsInstance_ofCore
    {sourceTy : GTy}
    {hsrc :
      GSrcInfer (embedClassTable p.classes) helab.core
        (embedTyEnv Γ) (embedExpr sourceExpr) sourceTy}
    (core :
      EmbeddedExprBridgeCore p.classes helab.core Γ sourceExpr producerTy
        sourceTy hsrc advertisedTy)
    (output : StaticOutputFact p helab producerTy sourceTarget)
    (checked_eq :
      compileCheck hsrc checkedEnv sourceTarget site =
        .cond (.isInstance x className) checkedThen checkedElse) :
    StaticCondIsInstanceDecomposition p helab Γ x className checkedThen
      checkedElse producerTy :=
  staticCompiledCondIsInstanceHead_decomposition
    (staticCompiledCondIsInstanceHead_ofCore core checked_eq)
    output

private def staticCheckedExprOk_condIsInstance_of_eq
    (expr : StaticCheckedExprOk p helab Γ checkedExpr outputTy)
    (checked_eq :
      checkedExpr = .cond (.isInstance x className) checkedThen checkedElse) :
    StaticCondIsInstanceDecomposition p helab Γ x className checkedThen
      checkedElse outputTy :=
  match expr with
  | .compiled bridge output output_subtype =>
      by
        rcases staticCompiledCondIsInstance_ofCore
            (p := p)
            (helab := helab)
            (Γ := Γ)
            (sourceExpr := _)
            (producerTy := _)
            (sourceTy := _)
            (hsrc := bridge.hsrc)
            (advertisedTy := _)
            (checkedEnv := _)
            (sourceTarget := _)
            (site := _)
            (x := x)
            (className := className)
            (checkedThen := checkedThen)
            (checkedElse := checkedElse)
            bridge.core
            output
            (by simpa using checked_eq) with
          ⟨variableTy, lookup, then_ok, else_ok⟩
        exact ⟨variableTy, lookup,
          .sub then_ok output_subtype,
          .sub else_ok output_subtype⟩
  | .cond test_not_isInstance .. =>
      by
        cases checked_eq
        exact False.elim (test_not_isInstance x className rfl)
  | .condIsInstance lookup _ thenBranch elseBranch output_subtype =>
      by
        cases checked_eq
        exact ⟨_, lookup,
          staticCheckedExprOk_unionLeftOutput thenBranch output_subtype,
          staticCheckedExprOk_unionRightOutput elseBranch output_subtype⟩
  | .interIntro left right output_subtype =>
      by
        rcases staticCheckedExprOk_condIsInstance_of_eq left checked_eq with
          ⟨leftVariableTy, leftLookup, leftThen, leftElse⟩
        rcases staticCheckedExprOk_condIsInstance_of_eq right checked_eq with
          ⟨rightVariableTy, rightLookup, rightThen, rightElse⟩
        have hvariable : leftVariableTy = rightVariableTy := by
          rw [leftLookup] at rightLookup
          cases rightLookup
          rfl
        cases hvariable
        let thenOk :
            StaticCheckedExprOk p helab
              (Γ.update x (.intersection leftVariableTy (.class_ className)))
              checkedThen
              (.intersection _ _) :=
          .intersection leftThen rightThen
        let elseOk :
            StaticCheckedExprOk p helab
              (Γ.update x (.intersection leftVariableTy (.negClass className)))
              checkedElse
              (.intersection _ _) :=
          .intersection leftElse rightElse
        exact ⟨leftVariableTy, leftLookup,
          .sub thenOk output_subtype,
          .sub elseOk output_subtype⟩
  | .sub inner output_subtype =>
      by
        rcases staticCheckedExprOk_condIsInstance_of_eq inner checked_eq with
          ⟨variableTy, lookup, then_ok, else_ok⟩
        exact ⟨variableTy, lookup,
          .sub then_ok output_subtype,
          .sub else_ok output_subtype⟩
  | .var .. =>
      by cases checked_eq
  | .constNone .. =>
      by cases checked_eq
  | .constTrue .. =>
      by cases checked_eq
  | .constFalse .. =>
      by cases checked_eq
  | .new .. =>
      by cases checked_eq
  | .isInstance .. =>
      by cases checked_eq
  | .enforce .. =>
      by cases checked_eq
  | .dynAttrAccess .. =>
      by cases checked_eq
  | .call .. =>
      by cases checked_eq

private def staticCheckedExprOk_condIsInstance
    (expr :
      StaticCheckedExprOk p helab Γ
        (.cond (.isInstance x className) checkedThen checkedElse) outputTy) :
    StaticCondIsInstanceDecomposition p helab Γ x className checkedThen
      checkedElse outputTy :=
  staticCheckedExprOk_condIsInstance_of_eq expr rfl

private def StaticDynAttrAccessDecomposition
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (Γ : TyEnv)
    (checkedBase : CheckedExpr)
    (attributeName : Identifier)
    (obligation : SourceObligation)
    (outputTy : Ty) : Prop :=
  ∃ receiverTy resultTy,
    ∃ _payload :
      StaticDynAttributePayloadEvidence p helab receiverTy attributeName
        obligation resultTy,
    StaticCheckedExprOk p helab Γ checkedBase receiverTy ∧
    IsSubtype helab.core.toOriginalWellFormedClassHierarchy resultTy outputTy

private def staticCheckedExprOk_dynAttrAccess_of_eq
    (expr : StaticCheckedExprOk p helab Γ checkedExpr outputTy)
    (checked_eq :
      checkedExpr = .dynAttrAccess checkedBase attributeName obligation) :
    StaticDynAttrAccessDecomposition p helab Γ checkedBase attributeName
      obligation outputTy :=
  match expr with
  | .compiled bridge _ _ =>
      False.elim
        (compileCheck_ne_dynAttrAccess bridge.hsrc _ _ _ checkedBase
          attributeName obligation (by simpa using checked_eq))
  | .dynAttrAccess base selection attrEvidence =>
      by
        cases checked_eq
        let payload :=
          staticDynAttributePayloadEvidence_ofSelection selection attrEvidence
            (staticCheckedExprOk_wellFormed base)
        exact ⟨_, _, payload, base,
          .refl (attrSelection_result_wellFormed helab.staticClassTable.hwf selection)⟩
  | .interIntro left right output_subtype =>
      by
        rcases staticCheckedExprOk_dynAttrAccess_of_eq left checked_eq with
          ⟨leftReceiverTy, leftResultTy, leftPayload, leftBase,
            leftSubtype⟩
        rcases staticCheckedExprOk_dynAttrAccess_of_eq right checked_eq with
          ⟨rightReceiverTy, rightResultTy, rightPayload, rightBase,
            rightSubtype⟩
        let baseOk :
            StaticCheckedExprOk p helab Γ checkedBase
              (.intersection leftReceiverTy rightReceiverTy) :=
          .intersection leftBase rightBase
        let payload :=
          staticDynAttributePayloadEvidence_interIntro leftPayload rightPayload
        let result_subtype :
            IsSubtype helab.core.toOriginalWellFormedClassHierarchy
              (.intersection leftResultTy rightResultTy)
              (.intersection _ _) :=
          .interMono leftSubtype rightSubtype
        exact ⟨
          .intersection leftReceiverTy rightReceiverTy,
          .intersection leftResultTy rightResultTy,
          payload,
          baseOk,
          .trans result_subtype output_subtype⟩
  | .sub inner output_subtype =>
      by
        rcases staticCheckedExprOk_dynAttrAccess_of_eq inner checked_eq with
          ⟨receiverTy, resultTy, payload, base_ok, result_subtype⟩
        exact ⟨receiverTy, resultTy, payload, base_ok,
          .trans result_subtype output_subtype⟩
  | .var .. =>
      by cases checked_eq
  | .constNone .. =>
      by cases checked_eq
  | .constTrue .. =>
      by cases checked_eq
  | .constFalse .. =>
      by cases checked_eq
  | .new .. =>
      by cases checked_eq
  | .isInstance .. =>
      by cases checked_eq
  | .enforce .. =>
      by cases checked_eq
  | .call .. =>
      by cases checked_eq
  | .cond .. =>
      by cases checked_eq
  | .condIsInstance .. =>
      by cases checked_eq

private def staticCheckedExprOk_dynAttrAccess
    (expr :
      StaticCheckedExprOk p helab Γ
        (.dynAttrAccess checkedBase attributeName obligation) outputTy) :
    StaticDynAttrAccessDecomposition p helab Γ checkedBase attributeName
      obligation outputTy :=
  staticCheckedExprOk_dynAttrAccess_of_eq expr rfl

private theorem staticCheckedExprOk_attrAccess_false_of_eq
    (expr : StaticCheckedExprOk p helab Γ checkedExpr outputTy)
    (checked_eq : checkedExpr = .attrAccess checkedBase attributeName) :
    False :=
  match expr with
  | .compiled bridge _ _ =>
      compileCheck_ne_attrAccess bridge.hsrc _ _ _ checkedBase attributeName
        (by simpa using checked_eq)
  | .interIntro left _ _ =>
      staticCheckedExprOk_attrAccess_false_of_eq left checked_eq
  | .sub inner _ =>
      staticCheckedExprOk_attrAccess_false_of_eq inner checked_eq
  | .var .. =>
      by cases checked_eq
  | .constNone .. =>
      by cases checked_eq
  | .constTrue .. =>
      by cases checked_eq
  | .constFalse .. =>
      by cases checked_eq
  | .new .. =>
      by cases checked_eq
  | .isInstance .. =>
      by cases checked_eq
  | .enforce .. =>
      by cases checked_eq
  | .dynAttrAccess .. =>
      by cases checked_eq
  | .call .. =>
      by cases checked_eq
  | .cond .. =>
      by cases checked_eq
  | .condIsInstance .. =>
      by cases checked_eq

private def staticCheckedExprOk_var_value_of_eq
    (expr : StaticCheckedExprOk p helab Γ checkedExpr outputTy)
    (checked_eq : checkedExpr = .var x)
    (env_ok : StaticEnvOk p helab heap env Γ)
    (env_lookup : env.lookup x = some value) :
    StaticValueOk p helab heap value outputTy :=
  match expr with
  | .compiled bridge _ _ =>
      False.elim
        (compileCheck_ne_var bridge.hsrc _ _ _ x (by simpa using checked_eq))
  | .var lookup output_subtype =>
      by
        cases checked_eq
        obtain ⟨runtimeValue, runtime_lookup, value_ok⟩ :=
          env_ok _ _ lookup
        rw [env_lookup] at runtime_lookup
        cases runtime_lookup
        exact .sub value_ok output_subtype
  | .constNone .. =>
      by cases checked_eq
  | .constTrue .. =>
      by cases checked_eq
  | .constFalse .. =>
      by cases checked_eq
  | .new .. =>
      by cases checked_eq
  | .isInstance .. =>
      by cases checked_eq
  | .enforce .. =>
      by cases checked_eq
  | .dynAttrAccess .. =>
      by cases checked_eq
  | .call .. =>
      by cases checked_eq
  | .cond .. =>
      by cases checked_eq
  | .condIsInstance .. =>
      by cases checked_eq
  | .interIntro left right output_subtype =>
      .sub
        (.interIntro
          (staticCheckedExprOk_var_value_of_eq left checked_eq
            env_ok env_lookup)
          (staticCheckedExprOk_var_value_of_eq right checked_eq
            env_ok env_lookup))
        output_subtype
  | .sub inner output_subtype =>
      .sub
        (staticCheckedExprOk_var_value_of_eq inner checked_eq env_ok env_lookup)
        output_subtype

private def staticCheckedExprOk_var_value
    (expr : StaticCheckedExprOk p helab Γ (.var x) outputTy)
    (env_ok : StaticEnvOk p helab heap env Γ)
    (env_lookup : env.lookup x = some value) :
    StaticValueOk p helab heap value outputTy :=
  staticCheckedExprOk_var_value_of_eq expr rfl env_ok env_lookup

private def staticCheckedExprOk_constNone_value_of_eq
    (expr : StaticCheckedExprOk p helab Γ checkedExpr outputTy)
    (checked_eq : checkedExpr = .constNone)
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap) :
    StaticValueOk p helab heap (.objRef noneOid) outputTy :=
  match expr with
  | .compiled bridge _ _ =>
      False.elim
        (compileCheck_ne_constNone bridge.hsrc _ _ _ (by simpa using checked_eq))
  | .constNone output_subtype =>
      by
        cases checked_eq
        exact .sub
          (.class_ hheap.initialNone (.refl (WellFormedTy.none helab.staticClassTable.hwf.toWellFormedClassHierarchy)))
          output_subtype
  | .interIntro left right output_subtype =>
      .sub
        (.interIntro
          (staticCheckedExprOk_constNone_value_of_eq left checked_eq hheap)
          (staticCheckedExprOk_constNone_value_of_eq right checked_eq hheap))
        output_subtype
  | .sub inner output_subtype =>
      .sub
        (staticCheckedExprOk_constNone_value_of_eq inner checked_eq hheap)
        output_subtype
  | .var .. =>
      by cases checked_eq
  | .constTrue .. =>
      by cases checked_eq
  | .constFalse .. =>
      by cases checked_eq
  | .new .. =>
      by cases checked_eq
  | .isInstance .. =>
      by cases checked_eq
  | .enforce .. =>
      by cases checked_eq
  | .dynAttrAccess .. =>
      by cases checked_eq
  | .call .. =>
      by cases checked_eq
  | .cond .. =>
      by cases checked_eq
  | .condIsInstance .. =>
      by cases checked_eq

private def staticCheckedExprOk_constNone_value
    (expr : StaticCheckedExprOk p helab Γ .constNone outputTy)
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap) :
    StaticValueOk p helab heap (.objRef noneOid) outputTy :=
  staticCheckedExprOk_constNone_value_of_eq expr rfl hheap

private def staticCheckedExprOk_constTrue_value_of_eq
    (expr : StaticCheckedExprOk p helab Γ checkedExpr outputTy)
    (checked_eq : checkedExpr = .constTrue)
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap) :
    StaticValueOk p helab heap (.objRef trueOid) outputTy :=
  match expr with
  | .compiled bridge _ _ =>
      False.elim
        (compileCheck_ne_constTrue bridge.hsrc _ _ _ (by simpa using checked_eq))
  | .constTrue output_subtype =>
      by
        cases checked_eq
        exact .sub
          (.class_ hheap.initialTrue (.refl (WellFormedTy.bool helab.staticClassTable.hwf.toWellFormedClassHierarchy)))
          output_subtype
  | .interIntro left right output_subtype =>
      .sub
        (.interIntro
          (staticCheckedExprOk_constTrue_value_of_eq left checked_eq hheap)
          (staticCheckedExprOk_constTrue_value_of_eq right checked_eq hheap))
        output_subtype
  | .sub inner output_subtype =>
      .sub
        (staticCheckedExprOk_constTrue_value_of_eq inner checked_eq hheap)
        output_subtype
  | .var .. =>
      by cases checked_eq
  | .constNone .. =>
      by cases checked_eq
  | .constFalse .. =>
      by cases checked_eq
  | .new .. =>
      by cases checked_eq
  | .isInstance .. =>
      by cases checked_eq
  | .enforce .. =>
      by cases checked_eq
  | .dynAttrAccess .. =>
      by cases checked_eq
  | .call .. =>
      by cases checked_eq
  | .cond .. =>
      by cases checked_eq
  | .condIsInstance .. =>
      by cases checked_eq

private def staticCheckedExprOk_constTrue_value
    (expr : StaticCheckedExprOk p helab Γ .constTrue outputTy)
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap) :
    StaticValueOk p helab heap (.objRef trueOid) outputTy :=
  staticCheckedExprOk_constTrue_value_of_eq expr rfl hheap

private def staticCheckedExprOk_constFalse_value_of_eq
    (expr : StaticCheckedExprOk p helab Γ checkedExpr outputTy)
    (checked_eq : checkedExpr = .constFalse)
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap) :
    StaticValueOk p helab heap (.objRef falseOid) outputTy :=
  match expr with
  | .compiled bridge _ _ =>
      False.elim
        (compileCheck_ne_constFalse bridge.hsrc _ _ _ (by simpa using checked_eq))
  | .constFalse output_subtype =>
      by
        cases checked_eq
        exact .sub
          (.class_ hheap.initialFalse (.refl (WellFormedTy.bool helab.staticClassTable.hwf.toWellFormedClassHierarchy)))
          output_subtype
  | .interIntro left right output_subtype =>
      .sub
        (.interIntro
          (staticCheckedExprOk_constFalse_value_of_eq left checked_eq hheap)
          (staticCheckedExprOk_constFalse_value_of_eq right checked_eq hheap))
        output_subtype
  | .sub inner output_subtype =>
      .sub
        (staticCheckedExprOk_constFalse_value_of_eq inner checked_eq hheap)
        output_subtype
  | .var .. =>
      by cases checked_eq
  | .constNone .. =>
      by cases checked_eq
  | .constTrue .. =>
      by cases checked_eq
  | .new .. =>
      by cases checked_eq
  | .isInstance .. =>
      by cases checked_eq
  | .enforce .. =>
      by cases checked_eq
  | .dynAttrAccess .. =>
      by cases checked_eq
  | .call .. =>
      by cases checked_eq
  | .cond .. =>
      by cases checked_eq
  | .condIsInstance .. =>
      by cases checked_eq

private def staticCheckedExprOk_constFalse_value
    (expr : StaticCheckedExprOk p helab Γ .constFalse outputTy)
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap) :
    StaticValueOk p helab heap (.objRef falseOid) outputTy :=
  staticCheckedExprOk_constFalse_value_of_eq expr rfl hheap

private def staticCheckedExprOk_new_value_of_eq
    (expr : StaticCheckedExprOk p helab Γ checkedExpr outputTy)
    (checked_eq : checkedExpr = .new className)
    {heap heap' : CheckedHeap}
    {objectId : Nat}
    (allocation :
      heap.alloc ⟨className, .ordinary⟩ = (objectId, heap')) :
    StaticValueOk p helab heap' (.objRef objectId) outputTy :=
  match expr with
  | .compiled bridge _ _ =>
      False.elim
        (compileCheck_ne_new bridge.hsrc _ _ _ className
          (by simpa using checked_eq))
  | .new _ _ _ _ output_subtype =>
      by
        cases checked_eq
        exact .sub
          (.class_ (checkedHeap_alloc_lookup_new allocation) (.refl output_subtype.sourceWellFormed))
          output_subtype
  | .interIntro left right output_subtype =>
      .sub
        (.interIntro
          (staticCheckedExprOk_new_value_of_eq left checked_eq allocation)
          (staticCheckedExprOk_new_value_of_eq right checked_eq allocation))
        output_subtype
  | .sub inner output_subtype =>
      .sub
        (staticCheckedExprOk_new_value_of_eq inner checked_eq allocation)
        output_subtype
  | .var .. =>
      by cases checked_eq
  | .constNone .. =>
      by cases checked_eq
  | .constTrue .. =>
      by cases checked_eq
  | .constFalse .. =>
      by cases checked_eq
  | .isInstance .. =>
      by cases checked_eq
  | .enforce .. =>
      by cases checked_eq
  | .dynAttrAccess .. =>
      by cases checked_eq
  | .call .. =>
      by cases checked_eq
  | .cond .. =>
      by cases checked_eq
  | .condIsInstance .. =>
      by cases checked_eq

private def staticCheckedExprOk_new_value
    (expr : StaticCheckedExprOk p helab Γ (.new className) outputTy)
    {heap heap' : CheckedHeap}
    {objectId : Nat}
    (allocation :
      heap.alloc ⟨className, .ordinary⟩ = (objectId, heap')) :
    StaticValueOk p helab heap' (.objRef objectId) outputTy :=
  staticCheckedExprOk_new_value_of_eq expr rfl allocation

private def staticCheckedExprOk_isInstance_value_of_eq
    (expr : StaticCheckedExprOk p helab Γ checkedExpr outputTy)
    (checked_eq : checkedExpr = .isInstance variableName className)
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap)
    (resultOid : Nat)
    (result_lookup :
      heap.lookup resultOid = some ⟨boolClass, .ordinary⟩) :
    StaticValueOk p helab heap (.objRef resultOid) outputTy :=
  match expr with
  | .compiled bridge _ _ =>
      False.elim
        (compileCheck_ne_isInstance bridge.hsrc _ _ _ variableName className
          (by simpa using checked_eq))
  | .isInstance _ _ output_subtype =>
      by
        cases checked_eq
        exact .sub
          (.class_ result_lookup (.refl (WellFormedTy.bool helab.staticClassTable.hwf.toWellFormedClassHierarchy)))
          output_subtype
  | .interIntro left right output_subtype =>
      .sub
        (.interIntro
          (staticCheckedExprOk_isInstance_value_of_eq left checked_eq hheap
            resultOid result_lookup)
          (staticCheckedExprOk_isInstance_value_of_eq right checked_eq hheap
            resultOid result_lookup))
        output_subtype
  | .sub inner output_subtype =>
      .sub
        (staticCheckedExprOk_isInstance_value_of_eq inner checked_eq hheap
          resultOid result_lookup)
        output_subtype
  | .var .. =>
      by cases checked_eq
  | .constNone .. =>
      by cases checked_eq
  | .constTrue .. =>
      by cases checked_eq
  | .constFalse .. =>
      by cases checked_eq
  | .new .. =>
      by cases checked_eq
  | .enforce .. =>
      by cases checked_eq
  | .dynAttrAccess .. =>
      by cases checked_eq
  | .call .. =>
      by cases checked_eq
  | .cond .. =>
      by cases checked_eq
  | .condIsInstance .. =>
      by cases checked_eq

private def staticCheckedExprOk_isInstance_value
    (expr : StaticCheckedExprOk p helab Γ (.isInstance variableName className) outputTy)
    (hheap :
      CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap)
    (resultOid : Nat)
    (result_lookup :
      heap.lookup resultOid = some ⟨boolClass, .ordinary⟩) :
    StaticValueOk p helab heap (.objRef resultOid) outputTy :=
  staticCheckedExprOk_isInstance_value_of_eq expr rfl hheap resultOid
    result_lookup

/-- Static evidence for one checked continuation frame. The input and output
type indices describe how a returned value flows through this frame. -/
private inductive StaticFrameOk
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (heap : CheckedHeap) :
    TyEnv → Ty → TyEnv → Ty → Checked.Frame → Prop where
  /-- Attribute frame for source-level static attribute access. -/
  | attrAccess
      (selection : AttrSelection p.classes receiverTy attributeName resultTy)
      (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy resultTy outputTy) :
      StaticFrameOk p helab heap Γ receiverTy Γ outputTy
        (.attrAccess attributeName)
  /-- Dynamic-attribute frame with source obligation evidence. -/
  | dynAttrAccess
      (payload :
        StaticDynAttributePayloadEvidence p helab receiverTy attributeName
          obligation resultTy)
      (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy resultTy outputTy) :
      StaticFrameOk p helab heap Γ receiverTy Γ outputTy
        (.dynAttrAccess attributeName obligation)
  /-- Call-callee frame: after the callee returns, the argument expression is
  evaluated and the resolved method frame is pushed. -/
  | callCallee
      (argument : StaticCheckedExprOk p helab Γ checkedArgument argumentTy)
      (payload :
        StaticCallPayloadEvidence p helab calleeTy argumentTy returnTy
          returnTarget returnObligation)
      (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy returnTy outputTy) :
      StaticFrameOk p helab heap Γ calleeTy Γ outputTy
        (.callCallee checkedArgument parameterTarget returnTarget returnObligation)
  /-- A resolved method call waiting for its argument.
  `receiver_lookup` identifies the receiver object in the heap.
  `origin` identifies the source method and its exact compiled body and checks.
  `receiver_ok` gives the receiver the method's defining class type.
  `argumentTy` is the argument expression's static type.
  `callReturn` proves that a value of `callReturnTy` passes the call's result check.
  `declared_to_call` places the declared function type below the call's required function type.
  `output_subtype` permits the caller to use the result at its requested output type.
  The subtype proofs also certify validity of the argument, result, and output types. -/
  | awaitArgument
      (receiver_lookup : heap.lookup receiverOid = some receiverObject)
      (origin : StaticMethodOrigin p helab checkedMethod)
      (receiver_ok :
        StaticValueOk p helab heap (.objRef receiverOid)
          (.class_ origin.definingClassName))
      (argumentTy : Ty)
      (callReturn :
        StaticTypeBoundaryEvidence p helab callReturnTy
          returnTarget returnObligation)
      (declared_to_call :
        IsSubtype helab.core.toOriginalWellFormedClassHierarchy
          (.callable origin.sourceMethod.paramTy origin.sourceMethod.returnTy)
          (.callable argumentTy callReturnTy))
      (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy callReturnTy outputTy) :
      StaticFrameOk p helab heap Γ argumentTy Γ outputTy
        (.awaitArgument receiverOid checkedMethod returnTarget returnObligation)
  /-- Conditional frame for already-focused condition expressions. Branches are
  stored at the frame output type, so selecting either branch can pop the
  condition frame without changing the rest of the continuation. -/
  | cond
      (thenBranch : StaticCheckedExprOk p helab Γ checkedThen outputTy)
      (elseBranch : StaticCheckedExprOk p helab Γ checkedElse outputTy) :
      StaticFrameOk p helab heap Γ (.class_ boolClass) Γ outputTy
        (.cond checkedThen checkedElse)
  /-- Return-to frame restores the caller environment and preserves the static
  value type. -/
  | returnTo
      (callerEnvOk : StaticEnvOk p helab heap callerEnv callerΓ) :
      StaticFrameOk p helab heap bodyΓ valueTy callerΓ valueTy
        (.returnTo callerEnv)
  /-- Enforcement frame with source-obligation satisfaction evidence for the
  value entering the boundary. -/
  | enforce
      (boundary :
        StaticTypeBoundaryEvidence p helab producerTy target obligation)
      (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy producerTy outputTy) :
      StaticFrameOk p helab heap Γ producerTy Γ outputTy
        (.enforce target obligation)

/-- A checked continuation is statically valid when each frame threads static
producer types and environments to the outer result. -/
private inductive StaticContinuationOk
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (heap : CheckedHeap) :
    TyEnv → Ty → TyEnv → Ty → Checked.Continuation → Prop where
  /-- Empty continuation preserves the current type and environment. -/
  | nil :
      StaticContinuationOk p helab heap Γ valueTy Γ valueTy []
  /-- Non-empty continuation whose top frame feeds the remaining frames. -/
  | cons
      (frameEvidence : StaticFrameOk p helab heap inputΓ inputTy midΓ midTy checkedFrame)
      (continuation :
        StaticContinuationOk p helab heap midΓ midTy outputΓ outputTy rest) :
      StaticContinuationOk p helab heap inputΓ inputTy outputΓ outputTy
        (checkedFrame :: rest)

/-- Static evidence for the active checked control. Active blame directly
stores the source-obligation satisfaction fact needed by the final theorem. -/
private inductive StaticControlOk
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (heap : CheckedHeap)
    (env : CheckedEnv)
    (Γ : TyEnv) :
    Checked.Control → Ty → Prop where
  /-- Expression control with static checked-expression evidence. -/
  | expr
      (expr : StaticCheckedExprOk p helab Γ checkedExpr producerTy) :
      StaticControlOk p helab heap env Γ (.expr checkedExpr) producerTy
  /-- Value control with static runtime value evidence. -/
  | val
      (value : StaticValueOk p helab heap checkedValue valueTy) :
      StaticControlOk p helab heap env Γ (.val checkedValue) valueTy
  /-- Blame control whose runtime cause satisfies the reported source
  obligation in the current heap. -/
  | blame
      (satisfies :
        Checked.CauseSatisfiesObligation
          (embedClassTable p.classes) helab.cp.classes heap
          info.cause info.obligation) :
      StaticControlOk p helab heap env Γ (.blame info) valueTy

/-- Static half of a checked-machine state invariant. It names the active
static environment, control type, outer environment, and root result type. -/
private structure StaticStateWitness
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (state : Checked.State)
    (rootStaticTy : Ty) : Type where
  /-- Static environment corresponding to the checked runtime environment. -/
  Γ : TyEnv
  /-- Static type produced by the active checked control. -/
  controlTy : Ty
  /-- Static environment expected by the outermost continuation result. -/
  outputΓ : TyEnv
  /-- Runtime environment realizes `Γ`. -/
  env_ok : StaticEnvOk p helab state.heap state.env Γ
  /-- Active checked control realizes `controlTy`. -/
  control_ok :
    StaticControlOk p helab state.heap state.env Γ state.control controlTy
  /-- Continuation threads the active control to the root static result type. -/
  continuation_ok :
    StaticContinuationOk p helab state.heap Γ controlTy outputΓ rootStaticTy
      state.continuation

/-- Full static state invariant. The checked safety witness is stored alongside
the static witness so one-step preservation can update both artifacts for the
same checked state. -/
private def StaticStateOk
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (state : Checked.State)
    (rootStaticTy : Ty)
    (checkedExpected : GTy) : Prop :=
  ∃ _static : StaticStateWitness p helab state rootStaticTy,
    Checked.CheckedStateSafe
      (embedClassTable p.classes)
      helab.cp.classes
      state.heap
      state.env
      state.control
      state.continuation
      checkedExpected

private theorem static_state_initial
    (helab : EmbeddedStaticElaboration p) :
    StaticStateOk p helab (Checked.initialState helab.cp)
      helab.mainTy helab.mainTarget := by
  have outputApprox :
      StaticOutputFact p helab helab.mainBridge.producerTy
        (approxTarget helab.mainBridge.srcTy) :=
    staticOutputFact_precision
      (staticOutputFact_ofView helab.mainBridge.view)
      (annotationPrecision_to_approxTarget helab.mainBridge.srcTy)
  have outputMain :
      StaticOutputFact p helab helab.mainBridge.producerTy
        helab.mainTarget := by
    rw [helab.mainTarget_eq]
    exact outputApprox
  refine ⟨?_, Checked.compiled_initial_safe_from_elaboration_at helab.compiled⟩
  refine
    { Γ := []
      controlTy := helab.mainTy
      outputΓ := []
      env_ok := ?_
      control_ok := ?_
      continuation_ok := .nil }
  · intro x T hlookup
    simp [NamedEnv.lookup] at hlookup
  · simp [Checked.initialState, Checked.expressionState, helab.main_eq]
    exact .expr
      (.compiled
        (bridge := helab.mainBridge)
        (checkedEnv := [])
        (target := helab.mainTarget)
        (site := .main [])
        outputMain
        helab.mainBridge.output_subtype)

private theorem staticFrameOk_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (frame : StaticFrameOk p helab heap inputΓ inputTy outputΓ outputTy checkedFrame) :
    StaticFrameOk p helab heap' inputΓ inputTy outputΓ outputTy checkedFrame := by
  cases frame with
  | attrAccess selection output_subtype =>
      exact .attrAccess selection output_subtype
  | dynAttrAccess payload output_subtype =>
      exact .dynAttrAccess payload output_subtype
  | callCallee argument payload output_subtype =>
      exact .callCallee argument payload output_subtype
  | awaitArgument receiver_lookup origin receiver_ok _
      callReturn declared_to_call
      output_subtype =>
      exact .awaitArgument (hmono _ _ receiver_lookup) origin
        (staticValueOk_heapMono hmono receiver_ok)
        inputTy callReturn
        declared_to_call output_subtype
  | cond thenBranch elseBranch =>
      exact .cond thenBranch elseBranch
  | returnTo callerEnvOk =>
      exact .returnTo (staticEnvOk_heapMono hmono callerEnvOk)
  | enforce boundary output_subtype =>
      exact .enforce boundary output_subtype

private theorem staticContinuationOk_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (continuation :
      StaticContinuationOk p helab heap inputΓ inputTy outputΓ outputTy checkedContinuation) :
    StaticContinuationOk p helab heap' inputΓ inputTy outputΓ outputTy checkedContinuation := by
  induction continuation with
  | nil =>
      exact .nil
  | cons frame _ ih =>
      exact .cons (staticFrameOk_heapMono hmono frame) ih

private theorem staticControlOk_blame_satisfies
    (control : StaticControlOk p helab heap env Γ (.blame info) controlTy) :
    Checked.CauseSatisfiesObligation
      (embedClassTable p.classes)
      helab.cp.classes
      heap
      info.cause
      info.obligation := by
  cases control with
  | blame satisfies => exact satisfies

private theorem static_state_final_blame_satisfies
    (hstate : StaticStateOk p helab finalState rootStaticTy checkedExpected)
    (hfinal :
      Checked.finalResult? finalState =
        some (heap', CheckedResult.blame info)) :
    Checked.CauseSatisfiesObligation
      (embedClassTable p.classes)
      helab.cp.classes
      heap'
      info.cause
      info.obligation := by
  obtain ⟨witness, _checkedSafe⟩ := hstate
  obtain ⟨hheap, hcontrol, _hcontinuation⟩ :=
    Checked.finalResult_blame_control hfinal
  have hcontrolOk := witness.control_ok
  rw [hcontrol] at hcontrolOk
  rw [← hheap]
  exact staticControlOk_blame_satisfies hcontrolOk

private theorem static_state_step_blame
    (hstate : StaticStateOk p helab s rootStaticTy checkedExpected)
    (hcontrol : s.control = .blame info)
    (hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes s s') :
    StaticStateOk p helab s' rootStaticTy checkedExpected := by
  rcases s with ⟨heap, env, control, continuation⟩
  rcases s' with ⟨heap', env', control', continuation'⟩
  simp at hcontrol
  subst control
  obtain ⟨witness, hsafe⟩ := hstate
  have hsafe' := Checked.checked_preservation hsafe hstep
  rcases witness with
    ⟨Γ, controlTy, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases hstep with
  | blameUnwindAttrAccess =>
      cases continuation_ok with
      | cons frame rest =>
          cases frame with
          | attrAccess _ _ =>
              exact ⟨
                { Γ := Γ
                  controlTy := _
                  outputΓ := outputΓ
                  env_ok := env_ok
                  control_ok := .blame
                    (staticControlOk_blame_satisfies control_ok)
                  continuation_ok := rest },
                hsafe'⟩
  | blameUnwindCallCallee =>
      cases continuation_ok with
      | cons frame rest =>
          cases frame with
          | callCallee _ _ _ =>
              exact ⟨
                { Γ := Γ
                  controlTy := _
                  outputΓ := outputΓ
                  env_ok := env_ok
                  control_ok := .blame
                    (staticControlOk_blame_satisfies control_ok)
                  continuation_ok := rest },
                hsafe'⟩
  | blameUnwindAwaitArgument =>
      cases continuation_ok with
      | cons frame rest =>
          cases frame with
          | awaitArgument _ _ _ _ _ _ _ =>
              exact ⟨
                { Γ := Γ
                  controlTy := _
                  outputΓ := outputΓ
                  env_ok := env_ok
                  control_ok := .blame
                    (staticControlOk_blame_satisfies control_ok)
                  continuation_ok := rest },
                hsafe'⟩
  | blameUnwindCond =>
      cases continuation_ok with
      | cons frame rest =>
          cases frame with
          | cond _ _ =>
              exact ⟨
                { Γ := Γ
                  controlTy := _
                  outputΓ := outputΓ
                  env_ok := env_ok
                  control_ok := .blame
                    (staticControlOk_blame_satisfies control_ok)
                  continuation_ok := rest },
                hsafe'⟩
  | blameUnwindReturnTo =>
      cases continuation_ok with
      | cons frame rest =>
          cases frame with
          | returnTo callerEnvOk =>
              exact ⟨
                { Γ := _
                  controlTy := controlTy
                  outputΓ := outputΓ
                  env_ok := callerEnvOk
                  control_ok := .blame
                    (staticControlOk_blame_satisfies control_ok)
                  continuation_ok := rest },
                hsafe'⟩
  | blameUnwindEnforce =>
      cases continuation_ok with
      | cons frame rest =>
          cases frame with
          | enforce _ _ =>
              exact ⟨
                { Γ := Γ
                  controlTy := _
                  outputΓ := outputΓ
                  env_ok := env_ok
                  control_ok := .blame
                    (staticControlOk_blame_satisfies control_ok)
                  continuation_ok := rest },
                hsafe'⟩
  | blameUnwindDynAttrAccess =>
      cases continuation_ok with
      | cons frame rest =>
          cases frame with
          | dynAttrAccess _ _ =>
              exact ⟨
                { Γ := Γ
                  controlTy := _
                  outputΓ := outputΓ
                  env_ok := env_ok
                  control_ok := .blame
                    (staticControlOk_blame_satisfies control_ok)
                  continuation_ok := rest },
                hsafe'⟩
  | _ =>
      contradiction

private theorem static_state_runtimeError_false
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .runtimeError message,
          continuation := rest }
        rootStaticTy checkedExpected) :
    False := by
  obtain ⟨witness, _hsafe⟩ := hstate
  cases witness.control_ok

private theorem static_state_step_focusAttrAccess
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env,
          control := .expr (.attrAccess checkedBase attributeName),
          continuation := rest }
        rootStaticTy checkedExpected) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .expr checkedBase,
        continuation := .attrAccess attributeName :: rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, _hsafe⟩ := hstate
  rcases witness with
    ⟨_, _, _, _, control_ok, _⟩
  cases control_ok with
  | expr expr_ok =>
      exact False.elim
        (staticCheckedExprOk_attrAccess_false_of_eq expr_ok rfl)

private theorem static_state_step_focusCond_fromEvidence
    (hsafe :
      Checked.CheckedStateSafe
        (embedClassTable p.classes)
        helab.cp.classes
        heap
        env
        (.expr (.cond checkedTest checkedThen checkedElse))
        rest
        checkedExpected)
    (env_ok : StaticEnvOk p helab heap env Γ)
    (condition_ok :
      StaticCheckedExprOk p helab Γ checkedTest (.class_ boolClass))
    (then_ok : StaticCheckedExprOk p helab Γ checkedThen thenTy)
    (else_ok : StaticCheckedExprOk p helab Γ checkedElse elseTy)
    (output_subtype :
      IsSubtype helab.core.toOriginalWellFormedClassHierarchy (.union thenTy elseTy) outputTy)
    (continuation_ok :
      StaticContinuationOk p helab heap Γ outputTy outputΓ rootStaticTy rest)
    (test_not_isInstance : ∀ x C, checkedTest ≠ .isInstance x C) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .expr checkedTest,
        continuation := .cond checkedThen checkedElse :: rest }
      rootStaticTy checkedExpected := by
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env,
          control := .expr (.cond checkedTest checkedThen checkedElse),
          continuation := rest }
        { heap := heap, env := env, control := .expr checkedTest,
          continuation := .cond checkedThen checkedElse :: rest } :=
    .focusCond test_not_isInstance
  have hsafe' := Checked.checked_preservation hsafe hstep
  exact ⟨
    { Γ := Γ
      controlTy := .class_ boolClass
      outputΓ := outputΓ
      env_ok := env_ok
      control_ok := .expr condition_ok
      continuation_ok :=
        .cons
          (.cond
            (staticCheckedExprOk_unionLeftOutput then_ok
              output_subtype)
            (staticCheckedExprOk_unionRightOutput else_ok
              output_subtype))
          continuation_ok },
    hsafe'⟩

private theorem static_state_step_focusCond
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env,
          control := .expr (.cond checkedTest checkedThen checkedElse),
          continuation := rest }
        rootStaticTy checkedExpected)
    (test_not_isInstance : ∀ x C, checkedTest ≠ .isInstance x C) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .expr checkedTest,
        continuation := .cond checkedThen checkedElse :: rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  rcases witness with
    ⟨_, _, _, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | expr expr_ok =>
      rcases staticCheckedExprOk_cond expr_ok test_not_isInstance with
        ⟨thenTy, elseTy, test_ok, then_ok, else_ok, output_subtype⟩
      exact static_state_step_focusCond_fromEvidence hsafe env_ok test_ok
        then_ok else_ok output_subtype continuation_ok
        test_not_isInstance

private theorem static_state_step_condIsInstanceTrue
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env,
          control := .expr (.cond (.isInstance x className) checkedThen checkedElse),
          continuation := rest }
        rootStaticTy checkedExpected)
    (env_lookup : env.lookup x = some (.objRef objectId))
    (object_lookup : heap.lookup objectId = some object)
    (class_lookup :
      findGClass (embedClassTable p.classes) object.className =
        some checkedClass)
    (class_mro :
      GComputeMro (embedClassTable p.classes) checkedClass mro)
    (class_mem : className ∈ mro) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .expr checkedThen,
        continuation := .returnTo env :: rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env,
          control := .expr (.cond (.isInstance x className) checkedThen checkedElse),
          continuation := rest }
        { heap := heap, env := env, control := .expr checkedThen,
          continuation := .returnTo env :: rest } :=
    .condIsInstanceTrue env_lookup object_lookup class_lookup class_mro
      class_mem
  have hsafe' := Checked.checked_preservation hsafe hstep
  rcases witness with
    ⟨Γ, controlTy, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | expr expr_ok =>
      rcases staticCheckedExprOk_condIsInstance expr_ok with
        ⟨variableTy, lookup, then_ok, _⟩
      let refined_env_ok :=
        staticEnvOk_refine_isInstance_true env_ok lookup env_lookup
          object_lookup class_lookup class_mro class_mem
      exact ⟨
        { Γ := Γ.update x (.intersection variableTy (.class_ className))
          controlTy := controlTy
          outputΓ := outputΓ
          env_ok := refined_env_ok
          control_ok := .expr then_ok
          continuation_ok :=
            .cons (.returnTo env_ok) continuation_ok },
        hsafe'⟩

private theorem static_state_step_condIsInstanceFalse
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env,
          control := .expr (.cond (.isInstance x className) checkedThen checkedElse),
          continuation := rest }
        rootStaticTy checkedExpected)
    (env_lookup : env.lookup x = some (.objRef objectId))
    (object_lookup : heap.lookup objectId = some object)
    (class_lookup :
      findGClass (embedClassTable p.classes) object.className =
        some checkedClass)
    (class_mro :
      GComputeMro (embedClassTable p.classes) checkedClass mro)
    (class_not_mem : className ∉ mro) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .expr checkedElse,
        continuation := .returnTo env :: rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env,
          control := .expr (.cond (.isInstance x className) checkedThen checkedElse),
          continuation := rest }
        { heap := heap, env := env, control := .expr checkedElse,
          continuation := .returnTo env :: rest } :=
    .condIsInstanceFalse env_lookup object_lookup class_lookup class_mro
      class_not_mem
  have hsafe' := Checked.checked_preservation hsafe hstep
  rcases witness with
    ⟨Γ, controlTy, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | expr expr_ok =>
      rcases staticCheckedExprOk_condIsInstance expr_ok with
        ⟨variableTy, lookup, _, else_ok⟩
      let refined_env_ok :=
        staticEnvOk_refine_isInstance_false env_ok lookup env_lookup
          object_lookup class_lookup class_mro class_not_mem
      exact ⟨
        { Γ := Γ.update x (.intersection variableTy (.negClass className))
          controlTy := controlTy
          outputΓ := outputΓ
          env_ok := refined_env_ok
          control_ok := .expr else_ok
          continuation_ok :=
            .cons (.returnTo env_ok) continuation_ok },
        hsafe'⟩

private theorem static_state_step_condIsInstanceVarNotFound
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env,
          control := .expr (.cond (.isInstance x className) checkedThen checkedElse),
          continuation := rest }
        rootStaticTy checkedExpected)
    (env_lookup : env.lookup x = none) :
    StaticStateOk p helab
      { heap := heap, env := env,
        control := .runtimeError ("Variable not found: " ++ x),
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨_witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env,
          control := .expr (.cond (.isInstance x className) checkedThen checkedElse),
          continuation := rest }
        { heap := heap, env := env,
          control := .runtimeError ("Variable not found: " ++ x),
          continuation := rest } :=
    .condIsInstanceVarNotFound env_lookup
  have hsafe' := Checked.checked_preservation hsafe hstep
  exact False.elim (hsafe'.not_runtimeError _ rfl)

private theorem static_state_step_focusCall_fromEvidence
    (hsafe :
      Checked.CheckedStateSafe
        (embedClassTable p.classes)
        helab.cp.classes
        heap
        env
        (.expr
          (.call checkedCallee checkedArgument parameterTarget returnTarget
            returnObligation))
        rest
        checkedExpected)
    (env_ok : StaticEnvOk p helab heap env Γ)
    (callee_ok :
      StaticCheckedExprOk p helab Γ checkedCallee calleeTy)
    (argument_ok :
      StaticCheckedExprOk p helab Γ checkedArgument argumentTy)
    (payload :
      StaticCallPayloadEvidence p helab calleeTy argumentTy returnTy
        returnTarget returnObligation)
    (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy returnTy outputTy)
    (continuation_ok :
      StaticContinuationOk p helab heap Γ outputTy outputΓ rootStaticTy rest) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .expr checkedCallee,
        continuation :=
          .callCallee checkedArgument parameterTarget returnTarget
            returnObligation :: rest }
      rootStaticTy checkedExpected := by
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env,
          control :=
            .expr
              (.call checkedCallee checkedArgument parameterTarget returnTarget
                returnObligation),
          continuation := rest }
        { heap := heap, env := env, control := .expr checkedCallee,
          continuation :=
            .callCallee checkedArgument parameterTarget returnTarget
              returnObligation :: rest } :=
    .focusCall
  have hsafe' := Checked.checked_preservation hsafe hstep
  exact ⟨
    { Γ := Γ
      controlTy := calleeTy
      outputΓ := outputΓ
      env_ok := env_ok
      control_ok := .expr callee_ok
      continuation_ok :=
        .cons
          (.callCallee argument_ok payload output_subtype)
          continuation_ok },
    hsafe'⟩

private theorem static_state_step_focusCall
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env,
          control :=
            .expr
              (.call checkedCallee checkedArgument parameterTarget returnTarget
                returnObligation),
          continuation := rest }
        rootStaticTy checkedExpected) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .expr checkedCallee,
        continuation :=
          .callCallee checkedArgument parameterTarget returnTarget
            returnObligation :: rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  rcases witness with
    ⟨_, _, _, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | expr expr_ok =>
      rcases staticCheckedExprOk_call expr_ok with
        ⟨calleeTy, argumentTy, returnTy, payload, callee_ok, argument_ok,
          output_subtype⟩
      exact static_state_step_focusCall_fromEvidence hsafe env_ok callee_ok
        argument_ok payload output_subtype continuation_ok

private theorem static_state_step_focusEnforce_fromEvidence
    (hsafe :
      Checked.CheckedStateSafe
        (embedClassTable p.classes)
        helab.cp.classes
        heap
        env
        (.expr (.enforce checkedBody target obligation))
        rest
        checkedExpected)
    (env_ok : StaticEnvOk p helab heap env Γ)
    (body_ok : StaticCheckedExprOk p helab Γ checkedBody producerTy)
    (boundary : StaticTypeBoundaryEvidence p helab producerTy target obligation)
    (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy producerTy outputTy)
    (continuation_ok :
      StaticContinuationOk p helab heap Γ outputTy outputΓ rootStaticTy rest) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .expr checkedBody,
        continuation := .enforce target obligation :: rest }
      rootStaticTy checkedExpected := by
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env,
          control := .expr (.enforce checkedBody target obligation),
          continuation := rest }
        { heap := heap, env := env, control := .expr checkedBody,
          continuation := .enforce target obligation :: rest } :=
    .focusEnforce
  have hsafe' := Checked.checked_preservation hsafe hstep
  exact ⟨
    { Γ := Γ
      controlTy := producerTy
      outputΓ := outputΓ
      env_ok := env_ok
      control_ok := .expr body_ok
      continuation_ok :=
        .cons
          (.enforce boundary output_subtype)
          continuation_ok },
    hsafe'⟩

private theorem static_state_step_focusEnforce
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env,
          control := .expr (.enforce checkedBody target obligation),
          continuation := rest }
        rootStaticTy checkedExpected) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .expr checkedBody,
        continuation := .enforce target obligation :: rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  rcases witness with
    ⟨_, _, _, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | expr expr_ok =>
      rcases staticCheckedExprOk_enforce expr_ok with
        ⟨producerTy, boundary, body_ok, output_subtype⟩
      exact static_state_step_focusEnforce_fromEvidence hsafe env_ok body_ok
        boundary output_subtype continuation_ok

private theorem static_state_step_focusDynAttrAccess_fromEvidence
    (hsafe :
      Checked.CheckedStateSafe
        (embedClassTable p.classes)
        helab.cp.classes
        heap
        env
        (.expr (.dynAttrAccess checkedBase attributeName obligation))
        rest
        checkedExpected)
    (env_ok : StaticEnvOk p helab heap env Γ)
    (base_ok : StaticCheckedExprOk p helab Γ checkedBase receiverTy)
    (payload :
      StaticDynAttributePayloadEvidence p helab receiverTy attributeName
        obligation resultTy)
    (output_subtype : IsSubtype helab.core.toOriginalWellFormedClassHierarchy resultTy outputTy)
    (continuation_ok :
      StaticContinuationOk p helab heap Γ outputTy outputΓ rootStaticTy rest) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .expr checkedBase,
        continuation := .dynAttrAccess attributeName obligation :: rest }
      rootStaticTy checkedExpected := by
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env,
          control := .expr (.dynAttrAccess checkedBase attributeName obligation),
          continuation := rest }
        { heap := heap, env := env, control := .expr checkedBase,
          continuation := .dynAttrAccess attributeName obligation :: rest } :=
    .focusDynAttrAccess
  have hsafe' := Checked.checked_preservation hsafe hstep
  exact ⟨
    { Γ := Γ
      controlTy := receiverTy
      outputΓ := outputΓ
      env_ok := env_ok
      control_ok := .expr base_ok
      continuation_ok :=
        .cons
          (.dynAttrAccess payload output_subtype)
          continuation_ok },
    hsafe'⟩

private theorem static_state_step_focusDynAttrAccess
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env,
          control := .expr (.dynAttrAccess checkedBase attributeName obligation),
          continuation := rest }
        rootStaticTy checkedExpected) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .expr checkedBase,
        continuation := .dynAttrAccess attributeName obligation :: rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  rcases witness with
    ⟨_, _, _, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | expr expr_ok =>
      rcases staticCheckedExprOk_dynAttrAccess expr_ok with
        ⟨receiverTy, resultTy, payload, base_ok, output_subtype⟩
      exact static_state_step_focusDynAttrAccess_fromEvidence hsafe env_ok
        base_ok payload output_subtype continuation_ok

private theorem static_state_step_varSuccess
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .expr (.var x),
          continuation := rest }
        rootStaticTy checkedExpected)
    (env_lookup : env.lookup x = some value) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .val value,
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .expr (.var x),
          continuation := rest }
        { heap := heap, env := env, control := .val value,
          continuation := rest } :=
    .varSuccess env_lookup
  have hsafe' := Checked.checked_preservation hsafe hstep
  rcases witness with
    ⟨Γ, controlTy, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | expr expr_ok =>
      exact ⟨
        { Γ := Γ
          controlTy := controlTy
          outputΓ := outputΓ
          env_ok := env_ok
          control_ok := .val
            (staticCheckedExprOk_var_value expr_ok env_ok env_lookup)
          continuation_ok := continuation_ok },
        hsafe'⟩

private theorem static_state_step_varError
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .expr (.var x),
          continuation := rest }
        rootStaticTy checkedExpected)
    (env_lookup : env.lookup x = none) :
    StaticStateOk p helab
      { heap := heap, env := env,
        control := .runtimeError ("Variable not found: " ++ x),
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨_witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .expr (.var x),
          continuation := rest }
        { heap := heap, env := env,
          control := .runtimeError ("Variable not found: " ++ x),
          continuation := rest } :=
    .varError env_lookup
  have hsafe' := Checked.checked_preservation hsafe hstep
  exact False.elim (hsafe'.not_runtimeError _ rfl)

private theorem static_state_step_constNone
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .expr .constNone,
          continuation := rest }
        rootStaticTy checkedExpected) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .val (.objRef noneOid),
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .expr .constNone,
          continuation := rest }
        { heap := heap, env := env, control := .val (.objRef noneOid),
          continuation := rest } :=
    .constNone
  have hsafe' := Checked.checked_preservation hsafe hstep
  obtain ⟨_, _, _, _, hheap, _, _, _, _⟩ := hsafe
  rcases witness with
    ⟨Γ, controlTy, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | expr expr_ok =>
      exact ⟨
        { Γ := Γ
          controlTy := controlTy
          outputΓ := outputΓ
          env_ok := env_ok
          control_ok := .val
            (staticCheckedExprOk_constNone_value expr_ok hheap)
          continuation_ok := continuation_ok },
        hsafe'⟩

private theorem static_state_step_constTrue
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .expr .constTrue,
          continuation := rest }
        rootStaticTy checkedExpected) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .val (.objRef trueOid),
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .expr .constTrue,
          continuation := rest }
        { heap := heap, env := env, control := .val (.objRef trueOid),
          continuation := rest } :=
    .constTrue
  have hsafe' := Checked.checked_preservation hsafe hstep
  obtain ⟨_, _, _, _, hheap, _, _, _, _⟩ := hsafe
  rcases witness with
    ⟨Γ, controlTy, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | expr expr_ok =>
      exact ⟨
        { Γ := Γ
          controlTy := controlTy
          outputΓ := outputΓ
          env_ok := env_ok
          control_ok := .val
            (staticCheckedExprOk_constTrue_value expr_ok hheap)
          continuation_ok := continuation_ok },
        hsafe'⟩

private theorem static_state_step_constFalse
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .expr .constFalse,
          continuation := rest }
        rootStaticTy checkedExpected) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .val (.objRef falseOid),
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .expr .constFalse,
          continuation := rest }
        { heap := heap, env := env, control := .val (.objRef falseOid),
          continuation := rest } :=
    .constFalse
  have hsafe' := Checked.checked_preservation hsafe hstep
  obtain ⟨_, _, _, _, hheap, _, _, _, _⟩ := hsafe
  rcases witness with
    ⟨Γ, controlTy, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | expr expr_ok =>
      exact ⟨
        { Γ := Γ
          controlTy := controlTy
          outputΓ := outputΓ
          env_ok := env_ok
          control_ok := .val
            (staticCheckedExprOk_constFalse_value expr_ok hheap)
          continuation_ok := continuation_ok },
        hsafe'⟩

private theorem static_state_step_newSuccess
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .expr (.new className),
          continuation := rest }
        rootStaticTy checkedExpected)
    (class_lookup :
      findGClass (embedClassTable p.classes) className = some checkedClass)
    (notBool : className ≠ boolClass)
    (notNone : className ≠ noneClass)
    (notBoundMethod : className ≠ boundMethodClass)
    (allocation :
      heap.alloc ⟨className, .ordinary⟩ = (objectId, heap')) :
    StaticStateOk p helab
      { heap := heap', env := env, control := .val (.objRef objectId),
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .expr (.new className),
          continuation := rest }
        { heap := heap', env := env, control := .val (.objRef objectId),
          continuation := rest } :=
    .newSuccess class_lookup notBool notNone notBoundMethod allocation
  have hsafe' := Checked.checked_preservation hsafe hstep
  obtain ⟨_, _, _, _, hheap, _, _, _, _⟩ := hsafe
  let heapMono :
      ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj :=
    fun _ _ hlookup =>
      checkedHeap_alloc_preserves_old hheap.idsBounded allocation hlookup
  rcases witness with
    ⟨Γ, controlTy, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | expr expr_ok =>
      exact ⟨
        { Γ := Γ
          controlTy := controlTy
          outputΓ := outputΓ
          env_ok := staticEnvOk_heapMono heapMono env_ok
          control_ok := .val
            (staticCheckedExprOk_new_value expr_ok allocation)
          continuation_ok :=
            staticContinuationOk_heapMono heapMono continuation_ok },
        hsafe'⟩

private theorem static_state_step_newClassNotFound
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .expr (.new className),
          continuation := rest }
        rootStaticTy checkedExpected)
    (class_lookup :
      findGClass (embedClassTable p.classes) className = none) :
    StaticStateOk p helab
      { heap := heap, env := env,
        control := .runtimeError ("Class not found: " ++ className),
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨_witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .expr (.new className),
          continuation := rest }
        { heap := heap, env := env,
          control := .runtimeError ("Class not found: " ++ className),
          continuation := rest } :=
    .newClassNotFound class_lookup
  have hsafe' := Checked.checked_preservation hsafe hstep
  exact False.elim (hsafe'.not_runtimeError _ rfl)

private theorem static_state_step_newBuiltinError
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .expr (.new className),
          continuation := rest }
        rootStaticTy checkedExpected)
    (class_lookup :
      findGClass (embedClassTable p.classes) className = some checkedClass)
    (builtin :
      className = boolClass ∨ className = noneClass ∨
        className = boundMethodClass) :
    StaticStateOk p helab
      { heap := heap, env := env,
        control :=
          .runtimeError ("Cannot instantiate builtin class: " ++ className),
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨_witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .expr (.new className),
          continuation := rest }
        { heap := heap, env := env,
          control :=
            .runtimeError ("Cannot instantiate builtin class: " ++ className),
          continuation := rest } :=
    .newBuiltinError class_lookup builtin
  have hsafe' := Checked.checked_preservation hsafe hstep
  exact False.elim (hsafe'.not_runtimeError _ rfl)

private theorem static_state_step_isInstanceTrue
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env,
          control := .expr (.isInstance variableName className),
          continuation := rest }
        rootStaticTy checkedExpected)
    (env_lookup : env.lookup variableName = some (.objRef objectId))
    (object_lookup : heap.lookup objectId = some object)
    (class_lookup :
      findGClass (embedClassTable p.classes) object.className =
        some checkedClass)
    (class_mro :
      GComputeMro (embedClassTable p.classes) checkedClass mro)
    (class_mem : className ∈ mro) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .val (.objRef trueOid),
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env,
          control := .expr (.isInstance variableName className),
          continuation := rest }
        { heap := heap, env := env, control := .val (.objRef trueOid),
          continuation := rest } :=
    .isInstanceTrue env_lookup object_lookup class_lookup class_mro class_mem
  have hsafe' := Checked.checked_preservation hsafe hstep
  obtain ⟨_, _, _, _, hheap, _, _, _, _⟩ := hsafe
  rcases witness with
    ⟨Γ, controlTy, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | expr expr_ok =>
      exact ⟨
        { Γ := Γ
          controlTy := controlTy
          outputΓ := outputΓ
          env_ok := env_ok
          control_ok := .val
            (staticCheckedExprOk_isInstance_value expr_ok hheap
              trueOid hheap.initialTrue)
          continuation_ok := continuation_ok },
        hsafe'⟩

private theorem static_state_step_isInstanceFalse
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env,
          control := .expr (.isInstance variableName className),
          continuation := rest }
        rootStaticTy checkedExpected)
    (env_lookup : env.lookup variableName = some (.objRef objectId))
    (object_lookup : heap.lookup objectId = some object)
    (class_lookup :
      findGClass (embedClassTable p.classes) object.className =
        some checkedClass)
    (class_mro :
      GComputeMro (embedClassTable p.classes) checkedClass mro)
    (class_not_mem : className ∉ mro) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .val (.objRef falseOid),
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env,
          control := .expr (.isInstance variableName className),
          continuation := rest }
        { heap := heap, env := env, control := .val (.objRef falseOid),
          continuation := rest } :=
    .isInstanceFalse env_lookup object_lookup class_lookup class_mro class_not_mem
  have hsafe' := Checked.checked_preservation hsafe hstep
  obtain ⟨_, _, _, _, hheap, _, _, _, _⟩ := hsafe
  rcases witness with
    ⟨Γ, controlTy, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | expr expr_ok =>
      exact ⟨
        { Γ := Γ
          controlTy := controlTy
          outputΓ := outputΓ
          env_ok := env_ok
          control_ok := .val
            (staticCheckedExprOk_isInstance_value expr_ok hheap
              falseOid hheap.initialFalse)
          continuation_ok := continuation_ok },
        hsafe'⟩

private theorem static_state_step_isInstanceVarNotFound
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env,
          control := .expr (.isInstance variableName className),
          continuation := rest }
        rootStaticTy checkedExpected)
    (env_lookup : env.lookup variableName = none) :
    StaticStateOk p helab
      { heap := heap, env := env,
        control := .runtimeError ("Variable not found: " ++ variableName),
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨_witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env,
          control := .expr (.isInstance variableName className),
          continuation := rest }
        { heap := heap, env := env,
          control := .runtimeError ("Variable not found: " ++ variableName),
          continuation := rest } :=
    .isInstanceVarNotFound env_lookup
  have hsafe' := Checked.checked_preservation hsafe hstep
  exact False.elim (hsafe'.not_runtimeError _ rfl)

private theorem static_state_step_returnEnforceBlame
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .val value,
          continuation := .enforce target obligation :: rest }
        rootStaticTy checkedExpected)
    (henforce :
      EnforceValue (embedClassTable p.classes) heap value
        (compileBoundaryTarget target) .blame) :
    StaticStateOk p helab
      { heap := heap, env := env,
        control := .blame
          { obligation := obligation, cause := .boundary value target },
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .val value,
          continuation := .enforce target obligation :: rest }
        { heap := heap, env := env,
          control := .blame
            { obligation := obligation, cause := .boundary value target },
          continuation := rest } :=
    .returnEnforceBlame henforce
  have hsafe' := Checked.checked_preservation hsafe hstep
  obtain ⟨_, _, _, _, hheap, _, _, _, _⟩ := hsafe
  rcases witness with
    ⟨Γ, _, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | val value_ok =>
      cases continuation_ok with
      | cons frame rest_ok =>
          cases frame with
          | enforce boundary _ =>
              exact ⟨
                { Γ := Γ
                  controlTy := _
                  outputΓ := outputΓ
                  env_ok := env_ok
                  control_ok := .blame
                    (staticTypeBoundaryEvidence_causeSatisfies
                      boundary hheap value_ok)
                  continuation_ok := rest_ok },
                hsafe'⟩

private theorem static_state_step_returnEnforceOk
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .val value,
          continuation := .enforce target obligation :: rest }
        rootStaticTy checkedExpected)
    (henforce :
      EnforceValue (embedClassTable p.classes) heap value
        (compileBoundaryTarget target) .ok) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .val value,
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .val value,
          continuation := .enforce target obligation :: rest }
        { heap := heap, env := env, control := .val value,
          continuation := rest } :=
    .returnEnforceOk henforce
  have hsafe' := Checked.checked_preservation hsafe hstep
  rcases witness with
    ⟨Γ, _, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | val value_ok =>
      cases continuation_ok with
      | cons frame rest_ok =>
          cases frame with
          | enforce _ output_subtype =>
              exact ⟨
                { Γ := Γ
                  controlTy := _
                  outputΓ := outputΓ
                  env_ok := env_ok
                  control_ok := .val
                    (.sub value_ok output_subtype)
                  continuation_ok := rest_ok },
                hsafe'⟩

private theorem static_state_step_returnAwaitArgumentBlame
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .val argument,
          continuation :=
            .awaitArgument receiverOid checkedMethod returnTarget returnObligation :: rest }
        rootStaticTy checkedExpected)
    (henforce :
      EnforceValue (embedClassTable p.classes) heap argument
        (compileBoundaryTarget checkedMethod.paramTy) .blame) :
    StaticStateOk p helab
      { heap := heap, env := env,
        control := .blame
          { obligation := checkedMethod.parameterObligation,
            cause := .methodParameter argument checkedMethod },
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .val argument,
          continuation :=
            .awaitArgument receiverOid checkedMethod returnTarget returnObligation :: rest }
        { heap := heap, env := env,
          control := .blame
            { obligation := checkedMethod.parameterObligation,
              cause := .methodParameter argument checkedMethod },
          continuation := rest } :=
    .returnAwaitArgumentBlame henforce
  have hsafe' := Checked.checked_preservation hsafe hstep
  obtain ⟨_, _, _, _, hheap, _, _, _, _⟩ := hsafe
  rcases witness with
    ⟨Γ, _, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | val argument_ok =>
      cases continuation_ok with
      | cons frame rest_ok =>
          cases frame with
          | awaitArgument _ origin _ _
              _
              declared_to_call _ =>
              have hargumentSatisfies :
                  Checked.SourceObligationHolds
                    (embedClassTable p.classes) helab.cp.classes heap argument
                    (.hasType
                      (.methodParameter origin.definingClassName origin.sourceMethod.name)
                      (embedTy origin.sourceMethod.paramTy)) :=
                checkedValueSatisfies_staticSubtype hheap (callable_domain_subtype declared_to_call)
                  (staticValueOk_satisfies hheap argument_ok)
              have hsatisfies :
                  Checked.CauseSatisfiesObligation
                    (embedClassTable p.classes) helab.cp.classes heap
                    (.methodParameter argument checkedMethod)
                    checkedMethod.parameterObligation := by
                rw [origin.parameterObligation_eq]
                simp [Checked.CauseSatisfiesObligation,
                  origin.parameterObligation_eq, origin.paramTy_eq,
                  hargumentSatisfies]
              exact ⟨
                { Γ := Γ
                  controlTy := _
                  outputΓ := outputΓ
                  env_ok := env_ok
                  control_ok := .blame hsatisfies
                  continuation_ok := rest_ok },
                hsafe'⟩

private theorem static_state_step_returnAwaitArgumentOk
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .val argument,
          continuation :=
            .awaitArgument receiverOid checkedMethod returnTarget returnObligation :: rest }
        rootStaticTy checkedExpected)
    (henforce :
      EnforceValue (embedClassTable p.classes) heap argument
        (compileBoundaryTarget checkedMethod.paramTy) .ok) :
    StaticStateOk p helab
      { heap := heap,
        env := [(checkedMethod.param, argument),
          (checkedMethod.receiverParam, .objRef receiverOid)],
        control := .expr checkedMethod.body,
        continuation :=
          .enforce checkedMethod.returnTy checkedMethod.returnObligation ::
            .enforce returnTarget returnObligation ::
            .returnTo env :: rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .val argument,
          continuation :=
            .awaitArgument receiverOid checkedMethod returnTarget returnObligation :: rest }
        { heap := heap,
          env := [(checkedMethod.param, argument),
            (checkedMethod.receiverParam, .objRef receiverOid)],
          control := .expr checkedMethod.body,
          continuation :=
            .enforce checkedMethod.returnTy checkedMethod.returnObligation ::
              .enforce returnTarget returnObligation ::
              .returnTo env :: rest } :=
    .returnAwaitArgumentOk henforce
  have hsafe' := Checked.checked_preservation hsafe hstep
  obtain ⟨_, _, _, _, hheap, _, _, _, _⟩ := hsafe
  rcases witness with
    ⟨_, _, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | val argument_ok =>
      cases continuation_ok with
      | cons frame rest_ok =>
          cases frame with
          | awaitArgument _ origin receiver_ok _
              callReturn
              declared_to_call output_subtype =>
              have method_to_call_return :=
                callable_return_subtype declared_to_call
                  (fun empty => by
                    have satisfied := checkedValueSatisfies_staticSubtype hheap empty
                      (staticValueOk_satisfies hheap argument_ok)
                    cases satisfied)
              let bodyΓ : TyEnv :=
                [(origin.sourceMethod.param, origin.sourceMethod.paramTy),
                 (origin.sourceMethod.receiverParam,
                  .class_ origin.definingClassName)]
              have argumentParamOk :
                  StaticValueOk p helab heap argument origin.sourceMethod.paramTy :=
                .sub argument_ok (callable_domain_subtype declared_to_call)
              have bodyEnvOk :
                  StaticEnvOk p helab heap
                    [(checkedMethod.param, argument),
                     (checkedMethod.receiverParam, .objRef receiverOid)]
                    bodyΓ := by
                intro y Ty hlookup
                by_cases hyParam : origin.sourceMethod.param = y
                · subst y
                  have hTy : Ty = origin.sourceMethod.paramTy := by
                    have hTy' : origin.sourceMethod.paramTy = Ty := by
                      simpa [bodyΓ, NamedEnv.lookup] using hlookup
                    exact hTy'.symm
                  subst hTy
                  exact ⟨argument, by
                    simp [NamedEnv.lookup, origin.param_eq], argumentParamOk⟩
                · by_cases hyReceiver : origin.sourceMethod.receiverParam = y
                  · subst y
                    have hTy :
                        Ty = .class_ origin.definingClassName := by
                      have hTy' :
                          .class_ origin.definingClassName = Ty := by
                        simpa [bodyΓ, NamedEnv.lookup, hyParam] using hlookup
                      exact hTy'.symm
                    subst hTy
                    exact ⟨.objRef receiverOid, by
                      simp [NamedEnv.lookup, origin.param_eq,
                        origin.receiverParam_eq, hyParam], receiver_ok⟩
                  · simp [bodyΓ, NamedEnv.lookup, hyParam, hyReceiver] at hlookup
              have bodyOk :
                  StaticCheckedExprOk p helab bodyΓ
                    checkedMethod.body origin.sourceMethod.returnTy := by
                rw [origin.body_eq]
                exact .compiled
                  (bridge := origin.body_bridge)
                  (checkedEnv :=
                    [(origin.sourceMethod.param,
                      embedTy origin.sourceMethod.paramTy),
                     (origin.sourceMethod.receiverParam,
                      .class_ origin.definingClassName)])
                  (target := .any)
                  (site := .methodBody origin.definingClassName
                    origin.sourceMethod.name [])
                  staticOutputFact_any
                  origin.body_bridge.output_subtype
              exact ⟨
                { Γ := bodyΓ
                  controlTy := origin.sourceMethod.returnTy
                  outputΓ := outputΓ
                  env_ok := bodyEnvOk
                  control_ok := .expr bodyOk
                  continuation_ok :=
                    .cons
                      (.enforce (staticTypeBoundaryEvidence_methodReturn origin) method_to_call_return)
                      (.cons
                        (.enforce callReturn output_subtype)
                        (.cons (.returnTo env_ok) rest_ok)) },
                hsafe'⟩

private theorem static_state_step_returnFromBody
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .val value,
          continuation := .returnTo callerEnv :: rest }
        rootStaticTy checkedExpected) :
    StaticStateOk p helab
      { heap := heap, env := callerEnv, control := .val value,
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .val value,
          continuation := .returnTo callerEnv :: rest }
        { heap := heap, env := callerEnv, control := .val value,
          continuation := rest } :=
    .returnFromBody
  have hsafe' := Checked.checked_preservation hsafe hstep
  rcases witness with
    ⟨_, controlTy, outputΓ, _, control_ok, continuation_ok⟩
  cases control_ok with
  | val value_ok =>
      cases continuation_ok with
      | cons frame rest_ok =>
          cases frame with
          | returnTo callerEnvOk =>
              exact ⟨
                { Γ := _
                  controlTy := controlTy
                  outputΓ := outputΓ
                  env_ok := callerEnvOk
                  control_ok := .val value_ok
                  continuation_ok := rest_ok },
                hsafe'⟩

private theorem static_state_step_returnCondTrue
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .val (.objRef trueOid),
          continuation := .cond thenBranch elseBranch :: rest }
        rootStaticTy checkedExpected) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .expr thenBranch,
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .val (.objRef trueOid),
          continuation := .cond thenBranch elseBranch :: rest }
        { heap := heap, env := env, control := .expr thenBranch,
          continuation := rest } :=
    .returnCondTrue
  have hsafe' := Checked.checked_preservation hsafe hstep
  rcases witness with
    ⟨Γ, _, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | val _ =>
      cases continuation_ok with
      | cons frame rest_ok =>
          cases frame with
          | cond thenOk _ =>
              exact ⟨
                { Γ := Γ
                  controlTy := _
                  outputΓ := outputΓ
                  env_ok := env_ok
                  control_ok := .expr thenOk
                  continuation_ok := rest_ok },
                hsafe'⟩

private theorem static_state_step_returnCondFalse
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .val (.objRef falseOid),
          continuation := .cond thenBranch elseBranch :: rest }
        rootStaticTy checkedExpected) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .expr elseBranch,
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .val (.objRef falseOid),
          continuation := .cond thenBranch elseBranch :: rest }
        { heap := heap, env := env, control := .expr elseBranch,
          continuation := rest } :=
    .returnCondFalse
  have hsafe' := Checked.checked_preservation hsafe hstep
  rcases witness with
    ⟨Γ, _, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | val _ =>
      cases continuation_ok with
      | cons frame rest_ok =>
          cases frame with
          | cond _ elseOk =>
              exact ⟨
                { Γ := Γ
                  controlTy := _
                  outputΓ := outputΓ
                  env_ok := env_ok
                  control_ok := .expr elseOk
                  continuation_ok := rest_ok },
                hsafe'⟩

private theorem static_state_step_returnCondNotBool
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .val (.objRef condOid),
          continuation := .cond thenBranch elseBranch :: rest }
        rootStaticTy checkedExpected)
    (hnotTrue : condOid ≠ trueOid)
    (hnotFalse : condOid ≠ falseOid) :
    StaticStateOk p helab
      { heap := heap, env := env,
        control := .runtimeError "Condition must evaluate to TRUE or FALSE",
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨_witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .val (.objRef condOid),
          continuation := .cond thenBranch elseBranch :: rest }
        { heap := heap, env := env,
          control := .runtimeError "Condition must evaluate to TRUE or FALSE",
          continuation := rest } :=
    .returnCondNotBool hnotTrue hnotFalse
  have hsafe' := Checked.checked_preservation hsafe hstep
  exact False.elim (hsafe'.not_runtimeError _ rfl)

private theorem static_state_step_returnDynAttrAccess
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .val (.objRef receiverOid),
          continuation := .dynAttrAccess attributeName obligation :: rest }
        rootStaticTy checkedExpected)
    (receiver_lookup : heap.lookup receiverOid = some receiverObject)
    (class_lookup :
      findGClass (embedClassTable p.classes) receiverObject.className =
        some receiverClass)
    (receiver_mro :
      GComputeMro (embedClassTable p.classes) receiverClass receiverMro)
    (checked_lookup :
      findCheckedMethodInMro helab.cp.classes receiverMro attributeName =
        some checkedMethod)
    (allocation :
      heap.alloc ⟨boundMethodClass, .boundMethod receiverOid checkedMethod⟩ =
        (boundMethodOid, heap')) :
    StaticStateOk p helab
      { heap := heap', env := env, control := .val (.objRef boundMethodOid),
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .val (.objRef receiverOid),
          continuation := .dynAttrAccess attributeName obligation :: rest }
        { heap := heap', env := env, control := .val (.objRef boundMethodOid),
          continuation := rest } :=
    .returnDynAttrAccess receiver_lookup class_lookup receiver_mro
      checked_lookup allocation
  have hsafe' := Checked.checked_preservation hsafe hstep
  obtain ⟨_, _, _, _, hheap, _, _, _, _⟩ := hsafe
  let heapMono :
      ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj :=
    fun _ _ hlookup =>
      checkedHeap_alloc_preserves_old hheap.idsBounded allocation hlookup
  rcases witness with
    ⟨Γ, _, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | val receiver_ok =>
      cases continuation_ok with
      | cons frame rest_ok =>
          cases frame with
          | dynAttrAccess payload output_subtype =>
              exact ⟨
                { Γ := Γ
                  controlTy := _
                  outputΓ := outputΓ
                  env_ok := staticEnvOk_heapMono heapMono env_ok
                  control_ok := .val
                    (.sub
                      (payload.boundMethodOk hheap receiver_ok receiver_lookup
                        class_lookup receiver_mro checked_lookup allocation)
                      output_subtype)
                  continuation_ok :=
                    staticContinuationOk_heapMono heapMono rest_ok },
                hsafe'⟩

private theorem static_state_step_returnAttrAccess
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .val (.objRef receiverOid),
          continuation := .attrAccess attributeName :: rest }
        rootStaticTy checkedExpected)
    (receiver_lookup : heap.lookup receiverOid = some receiverObject)
    (class_lookup :
      findGClass (embedClassTable p.classes) receiverObject.className =
        some receiverClass)
    (receiver_mro :
      GComputeMro (embedClassTable p.classes) receiverClass receiverMro)
    (checked_lookup :
      findCheckedMethodInMro helab.cp.classes receiverMro attributeName =
        some checkedMethod)
    (allocation :
      heap.alloc ⟨boundMethodClass, .boundMethod receiverOid checkedMethod⟩ =
        (boundMethodOid, heap')) :
    StaticStateOk p helab
      { heap := heap', env := env, control := .val (.objRef boundMethodOid),
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .val (.objRef receiverOid),
          continuation := .attrAccess attributeName :: rest }
        { heap := heap', env := env, control := .val (.objRef boundMethodOid),
          continuation := rest } :=
    .returnAttrAccess receiver_lookup class_lookup receiver_mro
      checked_lookup allocation
  have hsafe' := Checked.checked_preservation hsafe hstep
  obtain ⟨_, _, _, _, hheap, _, _, _, _⟩ := hsafe
  let heapMono :
      ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj :=
    fun _ _ hlookup =>
      checkedHeap_alloc_preserves_old hheap.idsBounded allocation hlookup
  rcases witness with
    ⟨Γ, _, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | val receiver_ok =>
      cases continuation_ok with
      | cons frame rest_ok =>
          cases frame with
          | attrAccess selection output_subtype =>
              exact ⟨
                { Γ := Γ
                  controlTy := _
                  outputΓ := outputΓ
                  env_ok := staticEnvOk_heapMono heapMono env_ok
                  control_ok := .val
                    (.sub
                      (staticValueOk_boundMethod_of_attrSelection hheap
                        selection receiver_ok receiver_lookup class_lookup
                        receiver_mro checked_lookup allocation)
                      output_subtype)
                  continuation_ok :=
                    staticContinuationOk_heapMono heapMono rest_ok },
                hsafe'⟩

private theorem static_state_step_returnAttrAccessNotFound
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .val (.objRef receiverOid),
          continuation := .attrAccess attributeName :: rest }
        rootStaticTy checkedExpected)
    (receiver_lookup : heap.lookup receiverOid = some receiverObject)
    (class_lookup :
      findGClass (embedClassTable p.classes) receiverObject.className =
        some receiverClass)
    (receiver_mro :
      GComputeMro (embedClassTable p.classes) receiverClass receiverMro)
    (checked_not_found :
      findCheckedMethodInMro helab.cp.classes receiverMro attributeName = none) :
    StaticStateOk p helab
      { heap := heap, env := env,
        control := .runtimeError
          ("Attribute not found: " ++ attributeName ++ " in class " ++
            receiverObject.className),
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨_witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .val (.objRef receiverOid),
          continuation := .attrAccess attributeName :: rest }
        { heap := heap, env := env,
          control := .runtimeError
            ("Attribute not found: " ++ attributeName ++ " in class " ++
              receiverObject.className),
          continuation := rest } :=
    .returnAttrAccessNotFound receiver_lookup class_lookup receiver_mro
      checked_not_found
  have hsafe' := Checked.checked_preservation hsafe hstep
  exact False.elim (hsafe'.not_runtimeError _ rfl)

private theorem static_state_step_returnDynAttrAccessNotFound
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .val (.objRef oid),
          continuation := .dynAttrAccess attributeName obligation :: rest }
        rootStaticTy checkedExpected)
    (hlookup : heap.lookup oid = some obj)
    (hfind : findGClass (embedClassTable p.classes) obj.className = some cls)
    (hmro : GComputeMro (embedClassTable p.classes) cls mro)
    (hnotfound : findCheckedMethodInMro helab.cp.classes mro attributeName = none) :
    StaticStateOk p helab
      { heap := heap, env := env,
        control := .blame
          { obligation := obligation,
            cause := .missingAttribute (.objRef oid) attributeName },
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  obtain ⟨_, _, _, _, hheap, _, _, _, _⟩ := hsafe
  rcases witness with
    ⟨_, _, _, _, control_ok, continuation_ok⟩
  cases control_ok with
  | val receiver_ok =>
      cases continuation_ok with
      | cons frame _ =>
          cases frame with
          | dynAttrAccess payload _ =>
              have hholds :=
                payload.attrEvidence.holds hheap receiver_ok
              rw [payload.attrEvidence.obligation_eq] at hholds
              rcases hholds with
                ⟨semanticOid, semanticObj, semanticCls, semanticMro, sourceMethod,
                  hreceiver, hsemanticLookup, hsemanticClass, hsemanticMro,
                  hsourceLookup⟩
              cases hreceiver
              rw [hlookup] at hsemanticLookup
              cases hsemanticLookup
              rw [hfind] at hsemanticClass
              cases hsemanticClass
              have hmroEq : semanticMro = mro :=
                gComputeMro_determinism hsemanticMro hmro
              have hsourceLookupMro :
                  findGMethodInMro (embedClassTable p.classes) mro attributeName =
                    some sourceMethod := by
                simpa [hmroEq] using hsourceLookup
              let lookup :=
                Checked.isCompiledClassTable_findMethodInMro
                  helab.classesCompiled
                  hsourceLookupMro
              have hfound :
                  findCheckedMethodInMro helab.cp.classes mro attributeName =
                    some lookup.member2 :=
                lookup.found
              rw [hnotfound] at hfound
              cases hfound

private theorem static_state_step_returnCallCalleeBound
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .val (.objRef calleeOid),
          continuation :=
            .callCallee checkedArgument parameterTarget returnTarget
              returnObligation :: rest }
        rootStaticTy checkedExpected)
    (bound_lookup :
      heap.lookup calleeOid =
        some ⟨boundMethodClass, .boundMethod receiverOid checkedMethod⟩) :
    StaticStateOk p helab
      { heap := heap, env := env, control := .expr checkedArgument,
        continuation :=
          .awaitArgument receiverOid checkedMethod returnTarget
            returnObligation :: rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  have hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes
        { heap := heap, env := env, control := .val (.objRef calleeOid),
          continuation :=
            .callCallee checkedArgument parameterTarget returnTarget
              returnObligation :: rest }
        { heap := heap, env := env, control := .expr checkedArgument,
          continuation :=
            .awaitArgument receiverOid checkedMethod returnTarget
              returnObligation :: rest } :=
    .returnCallCalleeBound bound_lookup
  have hsafe' := Checked.checked_preservation hsafe hstep
  obtain ⟨_, _, _, _, hheap, _, _, _, _⟩ := hsafe
  rcases witness with
    ⟨Γ, _, outputΓ, env_ok, control_ok, continuation_ok⟩
  cases control_ok with
  | val callee_ok =>
      cases continuation_ok with
      | cons frame rest_ok =>
          cases frame with
          | callCallee argument_ok payload output_subtype =>
              obtain
                ⟨receiverObject, receiver_lookup, origin, receiver_ok,
                  declared_to_selected⟩ :=
                staticCallDispatchEvidence_of_boundMethod hheap
                  payload.callee_to_callable callee_ok bound_lookup
              exact ⟨
                { Γ := Γ
                  controlTy := _
                  outputΓ := outputΓ
                  env_ok := env_ok
                  control_ok := .expr argument_ok
                  continuation_ok :=
                    .cons
                      (.awaitArgument receiver_lookup origin receiver_ok
                        _
                        payload.returnBoundary
                        declared_to_selected
                        output_subtype)
                      rest_ok },
                hsafe'⟩

private theorem static_state_step_returnCallCalleeNotCallable
    (hstate :
      StaticStateOk p helab
        { heap := heap, env := env, control := .val (.objRef calleeOid),
          continuation :=
            .callCallee checkedArgument parameterTarget returnTarget
              returnObligation :: rest }
        rootStaticTy checkedExpected)
    (ordinary_lookup :
      heap.lookup calleeOid = some ⟨className, .ordinary⟩) :
    StaticStateOk p helab
      { heap := heap, env := env,
        control := .runtimeError "Cannot call non-invokable value",
        continuation := rest }
      rootStaticTy checkedExpected := by
  obtain ⟨witness, hsafe⟩ := hstate
  obtain ⟨_, _, _, _, hheap, _, _, _, _⟩ := hsafe
  rcases witness with
    ⟨_, _, _, _, control_ok, continuation_ok⟩
  cases control_ok with
  | val callee_ok =>
      cases continuation_ok with
      | cons frame _ =>
          cases frame with
          | callCallee _ payload _ =>
              exact False.elim
                (staticValueOk_callSelection_not_ordinary hheap
                  payload.callee_to_callable callee_ok ordinary_lookup)

private theorem static_state_step
    (hstate : StaticStateOk p helab s rootStaticTy checkedExpected)
    (hstep :
      Checked.Step (embedClassTable p.classes) helab.cp.classes s s') :
    StaticStateOk p helab s' rootStaticTy checkedExpected := by
  cases hstep with
  | focusAttrAccess =>
      exact static_state_step_focusAttrAccess hstate
  | focusCall =>
      exact static_state_step_focusCall hstate
  | focusCond test_not_isInstance =>
      exact static_state_step_focusCond hstate test_not_isInstance
  | condIsInstanceTrue env_lookup object_lookup class_lookup class_mro
      class_mem =>
      exact static_state_step_condIsInstanceTrue hstate env_lookup
        object_lookup class_lookup class_mro class_mem
  | condIsInstanceFalse env_lookup object_lookup class_lookup class_mro
      class_not_mem =>
      exact static_state_step_condIsInstanceFalse hstate env_lookup
        object_lookup class_lookup class_mro class_not_mem
  | condIsInstanceVarNotFound env_lookup =>
      exact static_state_step_condIsInstanceVarNotFound hstate env_lookup
  | focusEnforce =>
      exact static_state_step_focusEnforce hstate
  | focusDynAttrAccess =>
      exact static_state_step_focusDynAttrAccess hstate
  | varSuccess env_lookup =>
      exact static_state_step_varSuccess hstate env_lookup
  | varError env_lookup =>
      exact static_state_step_varError hstate env_lookup
  | newSuccess class_lookup notBool notNone notBoundMethod allocation =>
      exact static_state_step_newSuccess hstate class_lookup notBool notNone
        notBoundMethod allocation
  | newClassNotFound class_lookup =>
      exact static_state_step_newClassNotFound hstate class_lookup
  | newBuiltinError class_lookup builtin =>
      exact static_state_step_newBuiltinError hstate class_lookup builtin
  | constNone =>
      exact static_state_step_constNone hstate
  | constTrue =>
      exact static_state_step_constTrue hstate
  | constFalse =>
      exact static_state_step_constFalse hstate
  | isInstanceTrue env_lookup object_lookup class_lookup class_mro class_mem =>
      exact static_state_step_isInstanceTrue hstate env_lookup object_lookup
        class_lookup class_mro class_mem
  | isInstanceFalse env_lookup object_lookup class_lookup class_mro
      class_not_mem =>
      exact static_state_step_isInstanceFalse hstate env_lookup object_lookup
        class_lookup class_mro class_not_mem
  | isInstanceVarNotFound env_lookup =>
      exact static_state_step_isInstanceVarNotFound hstate env_lookup
  | returnAttrAccess receiver_lookup class_lookup receiver_mro checked_lookup
      allocation =>
      exact static_state_step_returnAttrAccess hstate receiver_lookup
        class_lookup receiver_mro checked_lookup allocation
  | returnAttrAccessNotFound receiver_lookup class_lookup receiver_mro
      checked_not_found =>
      exact static_state_step_returnAttrAccessNotFound hstate receiver_lookup
        class_lookup receiver_mro checked_not_found
  | returnDynAttrAccess receiver_lookup class_lookup receiver_mro
      checked_lookup allocation =>
      exact static_state_step_returnDynAttrAccess hstate receiver_lookup
        class_lookup receiver_mro checked_lookup allocation
  | returnDynAttrAccessNotFound receiver_lookup class_lookup receiver_mro
      checked_not_found =>
      exact static_state_step_returnDynAttrAccessNotFound hstate
        receiver_lookup class_lookup receiver_mro checked_not_found
  | returnCallCalleeBound bound_lookup =>
      exact static_state_step_returnCallCalleeBound hstate bound_lookup
  | returnCallCalleeNotCallable ordinary_lookup =>
      exact static_state_step_returnCallCalleeNotCallable hstate ordinary_lookup
  | returnAwaitArgumentOk henforce =>
      exact static_state_step_returnAwaitArgumentOk hstate henforce
  | returnAwaitArgumentBlame henforce =>
      exact static_state_step_returnAwaitArgumentBlame hstate henforce
  | returnCondTrue =>
      exact static_state_step_returnCondTrue hstate
  | returnCondFalse =>
      exact static_state_step_returnCondFalse hstate
  | returnCondNotBool hnotTrue hnotFalse =>
      exact static_state_step_returnCondNotBool hstate hnotTrue hnotFalse
  | returnFromBody =>
      exact static_state_step_returnFromBody hstate
  | returnEnforceOk henforce =>
      exact static_state_step_returnEnforceOk hstate henforce
  | returnEnforceBlame henforce =>
      exact static_state_step_returnEnforceBlame hstate henforce
  | blameUnwindAttrAccess =>
      exact static_state_step_blame hstate rfl .blameUnwindAttrAccess
  | blameUnwindCallCallee =>
      exact static_state_step_blame hstate rfl .blameUnwindCallCallee
  | blameUnwindAwaitArgument =>
      exact static_state_step_blame hstate rfl .blameUnwindAwaitArgument
  | blameUnwindCond =>
      exact static_state_step_blame hstate rfl .blameUnwindCond
  | blameUnwindReturnTo =>
      exact static_state_step_blame hstate rfl .blameUnwindReturnTo
  | blameUnwindEnforce =>
      exact static_state_step_blame hstate rfl .blameUnwindEnforce
  | blameUnwindDynAttrAccess =>
      exact static_state_step_blame hstate rfl .blameUnwindDynAttrAccess
  | errorUnwindAttrAccess =>
      exact (static_state_runtimeError_false hstate).elim
  | errorUnwindCallCallee =>
      exact (static_state_runtimeError_false hstate).elim
  | errorUnwindAwaitArgument =>
      exact (static_state_runtimeError_false hstate).elim
  | errorUnwindCond =>
      exact (static_state_runtimeError_false hstate).elim
  | errorUnwindReturnTo =>
      exact (static_state_runtimeError_false hstate).elim
  | errorUnwindEnforce =>
      exact (static_state_runtimeError_false hstate).elim
  | errorUnwindDynAttrAccess =>
      exact (static_state_runtimeError_false hstate).elim

private theorem static_state_steps
    (hstate : StaticStateOk p helab s rootStaticTy checkedExpected)
    (hsteps :
      Checked.Steps (embedClassTable p.classes) helab.cp.classes s finalState) :
    StaticStateOk p helab finalState rootStaticTy checkedExpected := by
  induction hsteps with
  | refl =>
      exact hstate
  | step hstep _ ih =>
      exact ih (static_state_step hstate hstep)

theorem embedded_static_final_blame_satisfies_obligation
    (helab : EmbeddedStaticElaboration p)
    (hsteps : Checked.Steps
      (embedClassTable p.classes)
      helab.cp.classes
      (Checked.initialState helab.cp)
      finalState)
    (hfinal : Checked.finalResult? finalState =
      some (heap', CheckedResult.blame info)) :
    Checked.CauseSatisfiesObligation
      (embedClassTable p.classes)
      helab.cp.classes
      heap'
      info.cause
      info.obligation :=
  static_state_final_blame_satisfies
    (static_state_steps (static_state_initial helab) hsteps) hfinal

theorem embedded_static_no_blame
    (helab : EmbeddedStaticElaboration p)
    (hsteps : Checked.Steps
      (embedClassTable p.classes)
      helab.cp.classes
      (Checked.initialState helab.cp)
      finalState)
    (hfinal : Checked.finalResult? finalState =
      some (heap', CheckedResult.blame info)) :
    False :=
  Checked.no_final_blame_of_causeSatisfies
    helab.compiled hsteps hfinal
    (embedded_static_final_blame_satisfies_obligation helab hsteps hfinal)

theorem embedded_static_success
    (helab : EmbeddedStaticElaboration p)
    (hsteps : Checked.Steps
      (embedClassTable p.classes)
      helab.cp.classes
      (Checked.initialState helab.cp)
      finalState)
    (hfinal : Checked.finalResult? finalState = some (heap', result)) :
    ∃ v, result = CheckedResult.success v :=
  match Checked.gradual_soundness_at helab.compiled hsteps hfinal with
  | .inl ⟨v, hresult, _⟩ => ⟨v, hresult⟩
  | .inr ⟨_, hresult⟩ =>
      (embedded_static_no_blame helab hsteps (hresult ▸ hfinal)).elim
