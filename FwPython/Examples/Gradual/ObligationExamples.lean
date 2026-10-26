import FwPython.Gradual

/-! # Source Obligation Regression Examples -/

open Checked

/-! ## Source compilation obligations -/

example
    (hcompiled : Checked.ElaboratesProgramAt gp P cp) :
    Checked.CheckedProgramObligationsExact gp.classes cp :=
  Checked.obligationsExact_of_elaboration hcompiled

example
    (Gamma : SBindingEnv)
    (hlook : Gamma.lookupBinding x = some b) :
    compileCheck (GSrcInfer.var (gct := gct) (hwfct := hwfct) hlook)
      Delta P site =
      .enforce (.var x) (checkedTargetOfGTy P) (.hasType (.expression site) P) := by
  rfl

example
    (hbase : GSrcInfer gct hwfct Gamma base baseSrcTy)
    (hattr : attrSourceTy? gct baseSrcTy attr = some resultTy) :
    compileCheck (GSrcInfer.attrAccess hbase hattr) Delta P site =
      .enforce
        (.dynAttrAccess
          (compileCheck hbase Delta .any (site.child .attributeReceiver))
          attr
          (.hasAttribute site attr))
        (checkedTargetOfGTy P)
        (.hasType (.expression site) P) := by
  rfl

example
    (hcallee : GSrcInfer gct hwfct Gamma callee calleeSrcTy)
    (harg : GSrcInfer gct hwfct Gamma arg argSrcTy)
    (hcall :
        callSourceTy? gct calleeSrcTy argSrcTy hwfct = some resultTy) :
    let parameterTy := callParamTarget argSrcTy
    compileCheck
      (GSrcInfer.call hcallee harg hcall)
      Delta P site =
      .call
        (compileCheck hcallee Delta (.callable parameterTy P) (site.child .callCallee))
        (compileCheck harg Delta parameterTy (site.child .callArgument))
        (callParamCheckedTarget argSrcTy)
        (checkedTargetOfGTy P)
        (.hasType (.expression site) P) := by
  rfl

example
    (hnot : GExpr.notIsInstance conditionExpression)
    (htest : GSrcInfer gct hwfct Gamma conditionExpression testSrcTy)
    (hassign : AssignableTo gct hwfct.toWellFormedClassHierarchy testSrcTy (.class_ boolClass))
    (hthen : GSrcInfer gct hwfct Gamma thenExpression thenSrcTy)
    (helse : GSrcInfer gct hwfct Gamma elseExpression elseSrcTy) :
    compileCheck (GSrcInfer.cond hnot htest hassign hthen helse) Delta P site =
      .cond
        (compileCheck htest Delta (.class_ boolClass) (site.child .conditionTest))
        (compileCheck hthen Delta P (site.child .conditionThen))
        (compileCheck helse Delta P (site.child .conditionElse)) := by
  rfl

section condIsInstance
variable
    (Gamma : SBindingEnv)
    (hlook : Gamma.lookupBinding x = some b)
    (hfind : findGClass gct C = some cls)
    (hthen :
      GSrcInfer gct hwfct
        (Gamma.updateSource x (isInstanceThenRefinement b.sourceTy C))
        thenExpression
        thenSrcTy)
    (helse :
      GSrcInfer gct hwfct
        (Gamma.updateSource x (isInstanceElseRefinement b.sourceTy C))
        elseExpression
        elseSrcTy)

example
    (hdelta : Delta.lookup x = some T)
    (href : CheckedBranchRefineOk gct T C) :
    compileCheck (GSrcInfer.condIsInstance hlook hfind hthen helse) Delta P site =
      .cond (.isInstance x C)
        (compileCheck hthen
          (Delta.update x (isInstanceThenRefinement T C))
          P
          (site.child .conditionThen))
        (compileCheck helse
          (Delta.update x (isInstanceElseRefinement T C))
          P
          (site.child .conditionElse)) := by
  simp [compileCheck, condIsInstanceBranchEnvironments, hdelta, href]

example
    (hdelta : Delta.lookup x = some T)
    (href : ¬ CheckedBranchRefineOk gct T C) :
    compileCheck (GSrcInfer.condIsInstance hlook hfind hthen helse) Delta P site =
      .cond (.isInstance x C)
        (compileCheck hthen Delta P (site.child .conditionThen))
        (compileCheck helse Delta P (site.child .conditionElse)) := by
  simp [compileCheck, condIsInstanceBranchEnvironments, hdelta, href]

example
    (hdelta : Delta.lookup x = none) :
    compileCheck (GSrcInfer.condIsInstance hlook hfind hthen helse) Delta P site =
      .cond (.isInstance x C)
        (compileCheck hthen Delta P (site.child .conditionThen))
        (compileCheck helse Delta P (site.child .conditionElse)) := by
  simp [compileCheck, condIsInstanceBranchEnvironments, hdelta]

example :
    condIsInstanceBranchEnvironments gct [("x", .any)] "x" "Dog" =
      ([("x", .class_ "Dog")], [("x", .negClass "Dog")]) := by
  have href : CheckedBranchRefineOk gct .any "Dog" :=
    ⟨.classFormula .class_, .classFormula .negClass⟩
  simp [condIsInstanceBranchEnvironments, NamedEnv.lookup, NamedEnv.update,
    href, isInstanceThenRefinement, isInstanceElseRefinement,
    isInstanceRefinementWith, isInstanceRefinementBase?]

example :
    CheckedBranchRefineOk gct (.union (.callable .any .any) .any) "Dog" := by
  exact ⟨.classFormula .class_, .classFormula .negClass⟩

example
    (hnot : ¬ BMCompatibleFormula gct (.class_ "Dog")) :
    ¬ CheckedTargetTy gct
      (isInstanceThenRefinement (.intersection (.callable .any .any) .any) "Dog") := by
  intro htarget
  simp [isInstanceThenRefinement, isInstanceRefinementWith,
    isInstanceRefinementBase?] at htarget
  cases htarget with
  | classFormula hformula =>
      cases hformula with
      | intersection hcall _ => cases hcall
  | interCallableLeft _ _ hbm =>
      exact hnot hbm

end condIsInstance

/-! ## Method-return and call-site blame payloads

Step-rule shapes for `Step.returnEnforceBlame` already live in
`StepExamples.lean`; the examples below pin the obligation payload that flows
out of method-return and call-site blame, exercising the
`SourceObligation.hasType` constructors for the `.methodReturn` and
`.expression` site kinds. -/

example
    (henf :
      EnforceValue ct heap resultVal
        (compileBoundaryTarget methodReturnTarget)
        .blame) :
    Step ct cct
      { heap, env, control := .val resultVal,
        continuation :=
          .enforce methodReturnTarget
              (.hasType (.methodReturn cname methodName) methodReturnTy) ::
            .enforce callReturnTarget callReturnObligation ::
            .returnTo callerEnv :: k }
      { heap, env,
        control := .blame
          { obligation := .hasType (.methodReturn cname methodName) methodReturnTy,
            cause := .boundary resultVal methodReturnTarget },
        continuation :=
          .enforce callReturnTarget callReturnObligation ::
            .returnTo callerEnv :: k } :=
  .returnEnforceBlame henf

example
    (henf :
      EnforceValue ct heap resultVal
        (compileBoundaryTarget callReturnTarget)
        .blame) :
    Step ct cct
      { heap, env, control := .val resultVal,
        continuation :=
          .enforce callReturnTarget
              (.hasType (.expression callSite) callReturnTy) ::
            .returnTo callerEnv :: k }
      { heap, env,
        control := .blame
          { obligation := .hasType (.expression callSite) callReturnTy,
            cause := .boundary resultVal callReturnTarget },
        continuation := .returnTo callerEnv :: k } :=
  .returnEnforceBlame henf

/-! ## Blame-adequacy relation shape -/

example :
    Checked.CauseViolatesObligation gct cct heap
      (.boundary value target)
      (.hasAttribute site attrName) -> False :=
  id

example :
    Checked.CauseViolatesObligation gct cct heap
      (.boundary value target)
      (.hasType (.methodParameter className methodName) G) -> False :=
  id

example
    (h :
      Checked.CauseViolatesObligation gct cct heap
        (.missingAttribute receiver actualName)
        (.hasAttribute site expectedName)) :
    actualName = expectedName :=
  h.1

example
    (h :
      Checked.CauseViolatesObligation gct cct heap
        (.boundary value target)
        (.hasType (.expression site) G)) :
    target = checkedTargetOfGTy G :=
  h.1

example
    (h :
      Checked.CauseViolatesObligation gct cct heap
        (.methodParameter argument method)
        (.hasType (.methodParameter className methodName) G)) :
    method.paramTy = checkedTargetOfGTy G :=
  h.2.1

example
    (htarget : target = checkedTargetOfGTy G)
    (hholds :
      Checked.SourceObligationHolds gct cct heap value
        (.hasType (.expression site) G)) :
    Checked.CauseSatisfiesObligation gct cct heap
      (.boundary value target)
      (.hasType (.expression site) G) :=
  ⟨htarget, hholds⟩

example
    (hcompiled : Checked.ElaboratesProgramAt gp P cp)
    (hsteps :
      Checked.Steps gp.classes cp.classes
        (Checked.initialState cp)
        finalState)
    (hfinal :
      Checked.finalResult? finalState =
        some (heap', CheckedResult.blame info)) :
    Checked.CauseViolatesObligation
      gp.classes cp.classes heap' info.cause info.obligation :=
  Checked.blame_adequacy hcompiled hsteps hfinal

example
    (hcompiled : Checked.ElaboratesProgramAt gp P cp)
    (hsteps :
      Checked.Steps gp.classes cp.classes
        (Checked.initialState cp)
        finalState)
    (hfinal :
      Checked.finalResult? finalState =
        some (heap', CheckedResult.blame info))
    (hsat :
      Checked.CauseSatisfiesObligation
        gp.classes cp.classes heap' info.cause info.obligation) :
    False :=
  Checked.no_final_blame_of_causeSatisfies hcompiled hsteps hfinal hsat
