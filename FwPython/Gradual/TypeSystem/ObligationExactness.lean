import FwPython.Gradual.TypeSystem.Source.Compile
import FwPython.Gradual.TypeSystem.ClassTable.Compile
import FwPython.Gradual.Checked.Invariants
import FwPython.Gradual.Checked.HeapPreservation

/-! # Exact source obligations in compiled checked programs -/

namespace Checked

/-- A checked boundary target and stored source obligation describe the same
source type expectation for an expression or method-return site. -/
def BoundaryObligationExact
    (gct : GClassTable)
    (target : CheckedTarget)
    (obligation : SourceObligation) : Prop :=
  exists site gradualType,
    obligation = .hasType site gradualType /\
    (match site with
     | .expression _ => True
     | .methodReturn _ _ => True
     | .methodParameter _ _ => False) /\
    target = checkedTargetOfGTy gradualType /\
    CheckedTargetTy gct gradualType /\
    WellFormedGTy gct gradualType

/-- A checked method-parameter target and stored source obligation describe the
same source method-parameter type expectation. -/
def MethodParameterObligationExact
    (gct : GClassTable)
    (target : CheckedTarget)
    (obligation : SourceObligation) : Prop :=
  exists className methodName gradualType,
    obligation = .hasType (.methodParameter className methodName) gradualType /\
    target = checkedTargetOfGTy gradualType /\
    CheckedTargetTy gct gradualType /\
    WellFormedGTy gct gradualType

/-- A dynamic attribute operation and stored source obligation describe the
same attribute lookup expectation. -/
def AttributeObligationExact
    (attributeName : Identifier)
    (obligation : SourceObligation) : Prop :=
  exists site,
    obligation = .hasAttribute site attributeName

/-- Every blame-capable operation inside a checked expression stores an
obligation matching the operation it can blame for. -/
def CheckedExprObligationsExact
    (gct : GClassTable) : CheckedExpr -> Prop
  | .var _ => True
  | .new _ => True
  | .attrAccess base _ =>
      CheckedExprObligationsExact gct base
  | .call callee arg _ returnTy returnObligation =>
      CheckedExprObligationsExact gct callee /\
      CheckedExprObligationsExact gct arg /\
      BoundaryObligationExact gct returnTy returnObligation
  | .constNone => True
  | .constTrue => True
  | .constFalse => True
  | .cond test thenBranch elseBranch =>
      CheckedExprObligationsExact gct test /\
      CheckedExprObligationsExact gct thenBranch /\
      CheckedExprObligationsExact gct elseBranch
  | .isInstance _ _ => True
  | .enforce body target obligation =>
      CheckedExprObligationsExact gct body /\
      BoundaryObligationExact gct target obligation
  | .dynAttrAccess body attrName obligation =>
      CheckedExprObligationsExact gct body /\
      AttributeObligationExact attrName obligation

/-- A checked method stores exact source obligations on both method boundaries
and has an exact checked body. -/
def CheckedMethodObligationsExact
    (gct : GClassTable)
    (method : CheckedMethod) : Prop :=
  MethodParameterObligationExact gct method.paramTy method.parameterObligation /\
  BoundaryObligationExact gct method.returnTy method.returnObligation /\
  CheckedExprObligationsExact gct method.body

/-- A checked continuation frame stores exact obligations for any checked
operation it may resume. -/
def CheckedFrameObligationsExact
    (gct : GClassTable) : Checked.Frame -> Prop
  | .attrAccess _ => True
  | .callCallee arg _ returnTy returnObligation =>
      CheckedExprObligationsExact gct arg /\
      BoundaryObligationExact gct returnTy returnObligation
  | .awaitArgument _ method returnTy returnObligation =>
      CheckedMethodObligationsExact gct method /\
      BoundaryObligationExact gct returnTy returnObligation
  | .cond thenBranch elseBranch =>
      CheckedExprObligationsExact gct thenBranch /\
      CheckedExprObligationsExact gct elseBranch
  | .returnTo _ => True
  | .enforce target obligation =>
      BoundaryObligationExact gct target obligation
  | .dynAttrAccess attrName obligation =>
      AttributeObligationExact attrName obligation

/-- A checked continuation stores exact obligations for every pending frame,
in stack order from the next frame to resume through the outer frames. -/
def CheckedContinuationObligationsExact
    (gct : GClassTable) : Checked.Continuation -> Prop
  | [] => True
  | frame :: continuation =>
      CheckedFrameObligationsExact gct frame /\
      CheckedContinuationObligationsExact gct continuation

/-- A checked program stores source obligations that match every compiled
operation capable of producing checked blame. -/
structure CheckedProgramObligationsExact
    (gct : GClassTable)
    (cp : CheckedProgram) : Prop where
  /-- The checked main expression stores exact obligations for its blame-capable
  operations. -/
  main_exact : CheckedExprObligationsExact gct cp.main
  /-- Every checked method reachable through the program class table stores
  exact obligations for its parameter boundary, return boundary, and body. -/
  method_exact :
    ∀ cname checkedClass checkedMethod,
      findCheckedClass cp.classes cname = some checkedClass →
      checkedMethod ∈ checkedClass.methods →
      CheckedMethodObligationsExact gct checkedMethod

theorem boundaryObligationExact_checkedTargetOfGTy
    (site : SourceSite)
    (hsite :
      match site with
      | .expression _ => True
      | .methodReturn _ _ => True
      | .methodParameter _ _ => False)
    (hchecked : CheckedTargetTy gct G)
    (hwf : WellFormedGTy gct G) :
    BoundaryObligationExact gct
      (checkedTargetOfGTy G)
      (.hasType site G) :=
  ⟨site, G, rfl, hsite, rfl, hchecked, hwf⟩

theorem methodParameterObligationExact_checkedTargetOfGTy
    (className methodName : Identifier)
    (hchecked : CheckedTargetTy gct G)
    (hwf : WellFormedGTy gct G) :
    MethodParameterObligationExact gct
      (checkedTargetOfGTy G)
      (.hasType (.methodParameter className methodName) G) :=
  ⟨className, methodName, G, rfl, rfl, hchecked, hwf⟩

theorem attributeObligationExact_hasAttribute
    (site : SourceExpressionSite)
    (attrName : Identifier) :
    AttributeObligationExact attrName (.hasAttribute site attrName) :=
  ⟨site, rfl⟩

/-- Exactness for a compiled boundary wrapper follows from exactness of the
wrapped checked body and the checked/well-formed target facts. -/
theorem compileEnforce_obligationsExact
    {body : CheckedExpr}
    (hbody : CheckedExprObligationsExact gct body)
    (hPruntime : CheckedTargetTy gct P)
    (hPwf : WellFormedGTy gct P)
    (site : SourceExpressionSite) :
    CheckedExprObligationsExact gct (compileEnforce body P site) :=
  ⟨hbody,
    boundaryObligationExact_checkedTargetOfGTy (.expression site) trivial hPruntime hPwf⟩

theorem compileCheck_obligationsExact
    (hwfct : WellFormedGClassTableCore gct)
    (hPruntime : CheckedTargetTy gct P)
    (hPwf : WellFormedGTy gct P)
    (hsrc : GSrcInfer gct hwfct Gamma expr sourceType)
    (Delta : GTyEnv)
    (site : SourceExpressionSite) :
    CheckedExprObligationsExact gct
      (compileCheck hsrc Delta P site) := by
  induction hsrc generalizing Delta P site hPruntime hPwf with
  | var hlook =>
      exact compileEnforce_obligationsExact (body := .var _) trivial hPruntime hPwf site
  | constNone =>
      exact compileEnforce_obligationsExact (body := .constNone) trivial hPruntime hPwf site
  | constTrue =>
      exact compileEnforce_obligationsExact (body := .constTrue) trivial hPruntime hPwf site
  | constFalse =>
      exact compileEnforce_obligationsExact (body := .constFalse) trivial hPruntime hPwf site
  | new hfind hbool hnone hboundMethod =>
      exact compileEnforce_obligationsExact (body := .new _) trivial hPruntime hPwf site
  | isInstance hlook hfind =>
      exact compileEnforce_obligationsExact (body := .isInstance _ _) trivial hPruntime hPwf site
  | attrAccess hbase hattr ih =>
      exact compileEnforce_obligationsExact (body := .dynAttrAccess _ _ _)
        ⟨ih (.classFormula .any) .any Delta (site.child .attributeReceiver),
          attributeObligationExact_hasAttribute site _⟩
        hPruntime hPwf site
  | call hcallee harg hcall ihC ihA =>
      rename_i argSrcTy _
      have harg_wf := callSourceTy?_argumentWellFormed hwfct hcall
      let D : GTy := callParamTarget argSrcTy
      have hDruntime : CheckedTargetTy gct D :=
        callParamTarget_checkedTarget (gct := gct) (argSrcTy := argSrcTy)
      have hDwf : WellFormedGTy gct D :=
        callParamTarget_wellFormed (gct := gct) (argSrcTy := argSrcTy) harg_wf
      have hCallableRuntime : CheckedTargetTy gct (.callable D P) :=
        .callable hDruntime hPruntime
      have hCallableWf : WellFormedGTy gct (.callable D P) := .callable hDwf hPwf
      change CheckedExprObligationsExact gct
        (.call
          (compileCheck hcallee Delta (.callable D P) (site.child .callCallee))
          (compileCheck harg Delta D (site.child .callArgument))
          (callParamCheckedTarget argSrcTy)
          (checkedTargetOfGTy P)
          (.hasType (.expression site) P))
      exact ⟨
        ihC hCallableRuntime hCallableWf Delta (site.child .callCallee),
        ihA hDruntime hDwf Delta (site.child .callArgument),
        boundaryObligationExact_checkedTargetOfGTy (.expression site) trivial hPruntime hPwf
      ⟩
  | cond _ htest _ hthen helse ihTest ihThen ihElse =>
      change CheckedExprObligationsExact gct
        (.cond
          (compileCheck htest Delta (.class_ boolClass) (site.child .conditionTest))
          (compileCheck hthen Delta P (site.child .conditionThen))
          (compileCheck helse Delta P (site.child .conditionElse)))
      exact ⟨
        ihTest (.classFormula FormulaGTy.class_) (boolClass_wellFormed hwfct)
          Delta (site.child .conditionTest),
        ihThen hPruntime hPwf Delta (site.child .conditionThen),
        ihElse hPruntime hPwf Delta (site.child .conditionElse)
      ⟩
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
      rename_i b C sourceClass thenBranch thenSrcTy elseBranch elseSrcTy localGamma x
      rw [compileCheck]
      exact ⟨trivial,
        ihThen hPruntime hPwf _ (site.child .conditionThen),
        ihElse hPruntime hPwf _ (site.child .conditionElse)⟩

theorem isCompiledMethodAt_obligationsExact
    (hwfct : WellFormedGClassTableCore gct)
    (hfindClass : findGClass gct className = some sourceClass)
    (hmethodMem : sourceMethod ∈ sourceClass.methods)
    (hcompiled :
      Checked.IsCompiledMethodAt gct hwfct className sourceMethod checkedMethod) :
    CheckedMethodObligationsExact gct checkedMethod := by
  have hsigChecked := hwfct.allMethodSignaturesCheckedTarget _ _ _ hfindClass hmethodMem
  have hsigWf := hwfct.allMethodSignaturesWellFormed _ _ _ hfindClass hmethodMem
  refine ⟨?_, ?_, ?_⟩
  · rw [hcompiled.paramTy_eq, hcompiled.parameterObligation_eq]
    exact methodParameterObligationExact_checkedTargetOfGTy
      className sourceMethod.name hsigChecked.1 hsigWf.1
  · rw [hcompiled.returnTy_eq, hcompiled.returnObligation_eq]
    exact boundaryObligationExact_checkedTargetOfGTy
      (.methodReturn className sourceMethod.name) trivial hsigChecked.2 hsigWf.2
  · rw [hcompiled.body_eq]
    exact compileCheck_obligationsExact hwfct (.classFormula .any) .any
      hcompiled.body_hsrc
      [(sourceMethod.param, sourceMethod.paramTy),
       (sourceMethod.receiverParam, .class_ className)]
      (.methodBody className sourceMethod.name [])

theorem checkedMethodObligationsExact_of_boundMethod_lookup
    (hcompiled : Checked.IsCompiledClassTable gct hwfct cct)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hlookup :
      heap.lookup calleeOid =
        some ⟨boundMethodClass, .boundMethod receiverOid method⟩) :
    CheckedMethodObligationsExact gct method := by
  obtain ⟨receiverObject, _hreceiverLookup, hmethodInReceiverMro⟩ :=
    hheap.payloadReceiverValid calleeOid boundMethodClass receiverOid method hlookup
  obtain ⟨_receiverClass, mro, _hfindReceiverClass, _hreceiverMro, hfindMethod⟩ :=
    hmethodInReceiverMro
  obtain ⟨definingClassName, checkedClass, _hmemMro, hfindCheckedClass, hmethodMem⟩ :=
    findCheckedMethodInMro_provenance hfindMethod
  obtain ⟨sourceClass, sourceMethod, hfindSourceClass, hsourceMethodMem, hmethodCompiled⟩ :=
    Checked.traceMethodToSource hcompiled hfindCheckedClass hmethodMem
  exact hmethodCompiled.elim
    (fun hcompiledMethod =>
      isCompiledMethodAt_obligationsExact
        hwfct hfindSourceClass hsourceMethodMem hcompiledMethod)

theorem obligationsExact_of_elaboration
    {gp : GProgram} {P : GTy} {cp : CheckedProgram}
    (hcompiled : ElaboratesProgramAt gp P cp) :
    CheckedProgramObligationsExact gp.classes cp := by
  refine
    { main_exact := ?_
      method_exact := ?_ }
  · rw [hcompiled.main_eq]
    exact compileCheck_obligationsExact hcompiled.hwfct
      hcompiled.target_checkedTarget hcompiled.target_wf
      hcompiled.main_hsrc [] (.main [])
  · intro cname checkedClass checkedMethod hfindCheckedClass hmethodMem
    obtain ⟨sourceClass, sourceMethod, hfindSourceClass, hsourceMethodMem,
      hmethodCompiled⟩ :=
      Checked.traceMethodToSource
        hcompiled.classes_elab hfindCheckedClass hmethodMem
    exact hmethodCompiled.elim
      (fun hcompiledMethod =>
        isCompiledMethodAt_obligationsExact
          hcompiled.hwfct hfindSourceClass hsourceMethodMem hcompiledMethod)

end Checked
