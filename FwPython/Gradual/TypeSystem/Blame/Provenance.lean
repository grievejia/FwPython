import FwPython.Gradual.TypeSystem.Blame.BoundaryOrigin
import FwPython.Gradual.Checked.MultiStep
import FwPython.Gradual.TypeSystem.ClassTable.Compile
import FwPython.Gradual.TypeSystem.EnforcementClassification

/-! # Blame provenance

This file tracks where compiled labels come from, proves that execution
preserves registration of those labels, and recovers a unique syntactic
origin for any final blame label. -/

namespace Checked

/-- `CompiledBoundaryOrigin hcompiled origin ℓ` says that label `ℓ`
    appears at the specific compiled origin `origin`. -/
def CompiledBoundaryOrigin
    (_hcompiled : ElaboratesProgramAt gp P cp) :
    BoundaryOrigin → Label → Prop
  | .mainEnforce exprPath c p, ℓ =>
      ∃ e labels, cp.main.nodeAt exprPath = some (.enforce e c labels) ∧ ℓ = labels.at p
  | .mainDynAttr exprPath, ℓ =>
      ∃ e attr, cp.main.nodeAt exprPath = some (.dynAttrAccess e attr ℓ)
  | .mainCallReturn exprPath c p, ℓ =>
      ∃ callee arg paramTy labels,
        cp.main.nodeAt exprPath = some (.call callee arg paramTy c labels) ∧
        ℓ = labels.at p
  | .methodParameter definerName methodName c p, ℓ =>
      ∃ cc, ∃ gm, ∃ cm,
        ∃ (_hfc : findCheckedClass cp.classes definerName = some cc),
        ∃ (_hmem : cm ∈ cc.methods),
        ∃ (_hcm : IsCompiledMethodAt gp.classes definerName gm cm),
        ∃ (hc : c = cm.paramTy),
        gm.name = methodName ∧ ℓ = (hc ▸ cm.parameterLabels).at p
  | .methodReturn definerName methodName c p, ℓ =>
      ∃ cc, ∃ gm, ∃ cm,
        ∃ (_hfc : findCheckedClass cp.classes definerName = some cc),
        ∃ (_hmem : cm ∈ cc.methods),
        ∃ (_hcm : IsCompiledMethodAt gp.classes definerName gm cm),
        ∃ (hc : c = cm.returnTy),
        gm.name = methodName ∧ ℓ = (hc ▸ cm.returnLabels).at p
  | .methodBodyEnforce definerName methodName exprPath c p, ℓ =>
      ∃ cc gm cm e labels,
        findCheckedClass cp.classes definerName = some cc ∧
        cm ∈ cc.methods ∧
        IsCompiledMethodAt gp.classes definerName gm cm ∧
        gm.name = methodName ∧
        cm.body.nodeAt exprPath = some (.enforce e c labels) ∧
        ℓ = labels.at p
  | .methodBodyDynAttr definerName methodName exprPath, ℓ =>
      ∃ cc gm cm e attr,
        findCheckedClass cp.classes definerName = some cc ∧
        cm ∈ cc.methods ∧
        IsCompiledMethodAt gp.classes definerName gm cm ∧
        gm.name = methodName ∧
        cm.body.nodeAt exprPath = some (.dynAttrAccess e attr ℓ)
  | .methodBodyCallReturn definerName methodName exprPath c p, ℓ =>
      ∃ cc gm cm callee arg paramTy labels,
        findCheckedClass cp.classes definerName = some cc ∧
        cm ∈ cc.methods ∧
        IsCompiledMethodAt gp.classes definerName gm cm ∧
        gm.name = methodName ∧
        cm.body.nodeAt exprPath = some (.call callee arg paramTy c labels) ∧
        ℓ = labels.at p

/-- A label is registered when it appears at some compiled origin. -/
def CompiledBoundaryLabel
    (hcompiled : ElaboratesProgramAt gp P cp)
    (ℓ : Label) : Prop :=
  ∃ origin, CompiledBoundaryOrigin hcompiled origin ℓ

/-- Every label in the boundary tree appears at some compiled origin. -/
def BoundaryLabelsRegistered
    (hcompiled : ElaboratesProgramAt gp P cp)
    (labels : BoundaryLabels c) : Prop :=
  ∀ p, CompiledBoundaryLabel hcompiled (labels.at p)

/-- A checked method is registered when it can be traced back to a compiled
    gradual method. -/
def CheckedMethodLabelsRegistered
    (_hcompiled : ElaboratesProgramAt gp P cp)
    (cm : CheckedMethod) : Prop :=
  ∃ definerName cc gm,
    findCheckedClass cp.classes definerName = some cc ∧
    cm ∈ cc.methods ∧
    IsCompiledMethodAt gp.classes definerName gm cm

/-- Expression-level label registration. -/
def CheckedExprLabelsRegistered
    (hcompiled : ElaboratesProgramAt gp P cp) :
    CheckedExpr → Prop
  | .var _ => True
  | .new _ => True
  | .attrAccess base _ => CheckedExprLabelsRegistered hcompiled base
  | .call callee arg _ _ returnLabels =>
      CheckedExprLabelsRegistered hcompiled callee ∧
        CheckedExprLabelsRegistered hcompiled arg ∧
        BoundaryLabelsRegistered hcompiled returnLabels
  | .constNone => True
  | .constTrue => True
  | .constFalse => True
  | .cond test thenBr elseBr =>
      CheckedExprLabelsRegistered hcompiled test ∧
        CheckedExprLabelsRegistered hcompiled thenBr ∧
        CheckedExprLabelsRegistered hcompiled elseBr
  | .isInstance _ _ => True
  | .enforce e _ labels =>
      CheckedExprLabelsRegistered hcompiled e ∧
        BoundaryLabelsRegistered hcompiled labels
  | .dynAttrAccess e _ ℓ =>
      CheckedExprLabelsRegistered hcompiled e ∧
        CompiledBoundaryLabel hcompiled ℓ

/-- Value-level label registration. -/
def CheckedValueLabelsRegistered
    (_hcompiled : ElaboratesProgramAt gp P cp) :
    CheckedValue → Prop
  | .objRef _ => True

/-- Environment-level label registration. -/
def CheckedEnvLabelsRegistered
    (hcompiled : ElaboratesProgramAt gp P cp)
    (env : CheckedEnv) : Prop :=
  ∀ name v, env.lookup name = some v → CheckedValueLabelsRegistered hcompiled v

/-- Control-level label registration. -/
def ControlLabelsRegistered
    (hcompiled : ElaboratesProgramAt gp P cp) :
    Control → Prop
  | .expr e => CheckedExprLabelsRegistered hcompiled e
  | .val v => CheckedValueLabelsRegistered hcompiled v
  | .blame ℓ => CompiledBoundaryLabel hcompiled ℓ
  | .runtimeError _ => True

/-- Frame-level label registration. -/
def FrameLabelsRegistered
    (hcompiled : ElaboratesProgramAt gp P cp) :
    Frame → Prop
  | .attrAccess _ => True
  | .callCallee arg _ _ returnLabels =>
      CheckedExprLabelsRegistered hcompiled arg ∧
        BoundaryLabelsRegistered hcompiled returnLabels
  | .callValue argVal _ _ returnLabels =>
      CheckedValueLabelsRegistered hcompiled argVal ∧
        BoundaryLabelsRegistered hcompiled returnLabels
  | .awaitArgument _ cm _ returnLabels =>
      CheckedMethodLabelsRegistered hcompiled cm ∧
        BoundaryLabelsRegistered hcompiled returnLabels
  | .cond thenBr elseBr =>
      CheckedExprLabelsRegistered hcompiled thenBr ∧
        CheckedExprLabelsRegistered hcompiled elseBr
  | .returnTo callerEnv => CheckedEnvLabelsRegistered hcompiled callerEnv
  | .enforce _ labels => BoundaryLabelsRegistered hcompiled labels
  | .dynAttrAccess _ ℓ => CompiledBoundaryLabel hcompiled ℓ

/-- Heap-level label registration. -/
def HeapLabelsRegistered
    (hcompiled : ElaboratesProgramAt gp P cp)
    (heap : CheckedHeap) : Prop :=
  ∀ oid recvOid cm,
    heap.lookup oid = some ⟨boundMethodClass, .boundMethod recvOid cm⟩ →
      CheckedMethodLabelsRegistered hcompiled cm

/-- State-level label registration. -/
def StateLabelsRegistered
    (hcompiled : ElaboratesProgramAt gp P cp)
    (s : State) : Prop :=
  HeapLabelsRegistered hcompiled s.heap ∧
    CheckedEnvLabelsRegistered hcompiled s.env ∧
    ControlLabelsRegistered hcompiled s.control ∧
    ∀ frame ∈ s.continuation, FrameLabelsRegistered hcompiled frame

theorem boundaryLabels_subtree_registered
    (hlabels : BoundaryLabelsRegistered hcompiled labels) :
    BoundaryLabelsRegistered hcompiled (labels.subtree p) := by
  intro q
  simpa [BoundaryLabels.at_subtree] using hlabels (BoundaryPath.append p q)

theorem boundaryLabels_direct_registered
    (hlabels : BoundaryLabelsRegistered hcompiled labels) :
    CompiledBoundaryLabel hcompiled labels.direct := by
  simpa [BoundaryLabels.direct] using hlabels .here

theorem env_nil_registered :
    CheckedEnvLabelsRegistered hcompiled [] := by
  intro _ _ hlookup
  simp [NamedEnv.lookup] at hlookup

theorem env_cons_registered
    (hv : CheckedValueLabelsRegistered hcompiled v)
    (henv : CheckedEnvLabelsRegistered hcompiled env) :
    CheckedEnvLabelsRegistered hcompiled ((name, v) :: env) := by
  intro name' v' hlookup
  by_cases hEq : name' = name
  · subst name'
    simp [NamedEnv.lookup] at hlookup
    cases hlookup
    exact hv
  · have hEq' : name ≠ name' := by
        intro hEq''
        exact hEq hEq''.symm
    have hlookupTail : env.lookup name' = some v' := by
      simpa [NamedEnv.lookup, hEq'] using hlookup
    exact henv _ _ hlookupTail

theorem checkedMethod_parameterLabels_registered
    (hreg : CheckedMethodLabelsRegistered hcompiled cm) :
    BoundaryLabelsRegistered hcompiled cm.parameterLabels := by
  intro p
  rcases hreg with ⟨definerName, cc, gm, hfc, hmem, hcm⟩
  refine ⟨.methodParameter definerName gm.name cm.paramTy p, ?_⟩
  exact ⟨cc, gm, cm, hfc, hmem, hcm, rfl, rfl, rfl⟩

theorem checkedMethod_returnLabels_registered
    (hreg : CheckedMethodLabelsRegistered hcompiled cm) :
    BoundaryLabelsRegistered hcompiled cm.returnLabels := by
  intro p
  rcases hreg with ⟨definerName, cc, gm, hfc, hmem, hcm⟩
  refine ⟨.methodReturn definerName gm.name cm.returnTy p, ?_⟩
  exact ⟨cc, gm, cm, hfc, hmem, hcm, rfl, rfl, rfl⟩

theorem checkedMethodInMro_registered
    (hcompiled : ElaboratesProgramAt gp P cp)
    (_hmro : GComputeMro gp.classes recvCls mro)
    (hfind : findCheckedMethodInMro cp.classes mro methodName = some cm) :
    CheckedMethodLabelsRegistered hcompiled cm := by
  obtain ⟨definerName, cc, _, hfc, hmem⟩ := findCheckedMethodInMro_provenance hfind
  obtain ⟨_, gm, _, _, hcm⟩ := traceMethodToSource hcompiled.classes_elab hfc hmem
  exact ⟨definerName, cc, gm, hfc, hmem, hcm⟩

private theorem compileCheck_main_registered
    (hcompiled : ElaboratesProgramAt gp P cp)
    {Γ e srcTy Δ Q n path}
    (hsrc : GSrcInfer gp.classes hcompiled.hwfct Γ e srcTy) :
    cp.main.nodeAt path = some (compileCheck .main hsrc Δ Q n).1 →
      CheckedExprLabelsRegistered hcompiled (compileCheck .main hsrc Δ Q n).1 := by
  match hsrc with
  | .var (x := x) _ =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      exact ⟨trivial, fun p => ⟨.mainEnforce path _ p, ⟨.var x, _, hnode, rfl⟩⟩⟩
  | .constNone =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      exact ⟨trivial, fun p => ⟨.mainEnforce path _ p, ⟨.constNone, _, hnode, rfl⟩⟩⟩
  | .constTrue =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      exact ⟨trivial, fun p => ⟨.mainEnforce path _ p, ⟨.constTrue, _, hnode, rfl⟩⟩⟩
  | .constFalse =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      exact ⟨trivial, fun p => ⟨.mainEnforce path _ p, ⟨.constFalse, _, hnode, rfl⟩⟩⟩
  | .new (cname := cname) _ _ _ _ =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      exact ⟨trivial, fun p => ⟨.mainEnforce path _ p, ⟨.new cname, _, hnode, rfl⟩⟩⟩
  | .attrAccess (attr := attr) hbase _ =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      have hbaseNode :
          cp.main.nodeAt (path ++ [.enforceBody, .dynAttrBase]) =
            some (compileCheck .main hbase Δ .any n).1 := by
        simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.enforceBody, .dynAttrBase]) hnode)
      have hdynNode :
          cp.main.nodeAt (path ++ [.enforceBody]) =
            some (.dynAttrAccess (compileCheck .main hbase Δ .any n).1 attr
              (freshLabel .main .context (compileCheck .main hbase Δ .any n).2).1) := by
        simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.enforceBody]) hnode)
      refine ⟨?_, ?_⟩
      · refine ⟨compileCheck_main_registered hcompiled (Δ := Δ) (Q := .any) (n := n)
          (path := path ++ [.enforceBody, .dynAttrBase]) hbase hbaseNode, ?_⟩
        exact ⟨.mainDynAttr (path ++ [.enforceBody]), ⟨(compileCheck .main hbase Δ .any n).1, attr, hdynNode⟩⟩
      · intro p
        exact ⟨.mainEnforce path _ p,
          ⟨.dynAttrAccess (compileCheck .main hbase Δ .any n).1 attr
            (freshLabel .main .context (compileCheck .main hbase Δ .any n).2).1, _, hnode, rfl⟩⟩
  | .call (argSrcTy := argSrcTy) hcallee harg _ _ _ _ =>
      let D := callParamTarget gp.classes argSrcTy
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered, D] at hnode ⊢
      have hcalleeNode :
          cp.main.nodeAt (path ++ [.callCallee]) =
            some (compileCheck .main hcallee Δ (.callable D Q) n).1 := by
        simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.callCallee]) hnode)
      have hargNode :
          cp.main.nodeAt (path ++ [.callArg]) =
            some (compileCheck .main harg Δ D
              (compileCheck .main hcallee Δ (.callable D Q) n).2).1 := by
        simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.callArg]) hnode)
      have hreturnLabels :
          BoundaryLabelsRegistered hcompiled
            (mkBoundaryLabels .main .positive
              (compileBoundaryTarget (checkedTargetOfRuntimePublicTy Q))
              (compileCheck .main harg Δ D
                (compileCheck .main hcallee Δ (.callable D Q) n).2).2).1 := by
        intro p
        refine ⟨.mainCallReturn path _ p, ?_⟩
        exact ⟨_, _, _, _, hnode, rfl⟩
      exact ⟨compileCheck_main_registered hcompiled
          (Δ := Δ) (Q := .callable D Q) (n := n)
          (path := path ++ [.callCallee]) hcallee hcalleeNode,
        compileCheck_main_registered hcompiled
          (Δ := Δ) (Q := D)
          (n := (compileCheck .main hcallee Δ (.callable D Q) n).2)
          (path := path ++ [.callArg]) harg hargNode,
        hreturnLabels⟩
  | .cond _ htest _ hthen helse =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      have htestNode :
          cp.main.nodeAt (path ++ [.condTest]) =
            some (compileCheck .main htest Δ (.class_ boolClass) n).1 := by
        simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condTest]) hnode)
      have hthenNode :
          cp.main.nodeAt (path ++ [.condThen]) =
            some (compileCheck .main hthen Δ Q
              (compileCheck .main htest Δ (.class_ boolClass) n).2).1 := by
        simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condThen]) hnode)
      have helseNode :
          cp.main.nodeAt (path ++ [.condElse]) =
            some (compileCheck .main helse Δ Q
              (compileCheck .main hthen Δ Q
                (compileCheck .main htest Δ (.class_ boolClass) n).2).2).1 := by
        simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condElse]) hnode)
      exact ⟨compileCheck_main_registered hcompiled
          (Δ := Δ) (Q := .class_ boolClass) (n := n)
          (path := path ++ [.condTest]) htest htestNode,
        compileCheck_main_registered hcompiled
          (Δ := Δ) (Q := Q)
          (n := (compileCheck .main htest Δ (.class_ boolClass) n).2)
          (path := path ++ [.condThen]) hthen hthenNode,
        compileCheck_main_registered hcompiled
          (Δ := Δ) (Q := Q)
          (n := (compileCheck .main hthen Δ Q
            (compileCheck .main htest Δ (.class_ boolClass) n).2).2)
          (path := path ++ [.condElse]) helse helseNode⟩
  | .isInstance (x := x) (C := C) _ _ =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      exact ⟨trivial, fun p => ⟨.mainEnforce path _ p, ⟨.isInstance x C, _, hnode, rfl⟩⟩⟩
  | .condIsInstance (x := x) (C := C) _ _ hthen helse =>
      intro hnode
      cases hΔ : Δ.lookup x with
      | none =>
          simp [compileCheck, hΔ, CheckedExprLabelsRegistered] at hnode ⊢
          have hthenNode :
              cp.main.nodeAt (path ++ [.condThen]) =
                some (compileCheck .main hthen Δ Q n).1 := by
            simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condThen]) hnode)
          have helseNode :
              cp.main.nodeAt (path ++ [.condElse]) =
                some (compileCheck .main helse Δ Q (compileCheck .main hthen Δ Q n).2).1 := by
            simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condElse]) hnode)
          exact ⟨compileCheck_main_registered hcompiled
              (Δ := Δ) (Q := Q) (n := n) (path := path ++ [.condThen]) hthen hthenNode,
            compileCheck_main_registered hcompiled
              (Δ := Δ) (Q := Q)
              (n := (compileCheck .main hthen Δ Q n).2)
              (path := path ++ [.condElse]) helse helseNode⟩
      | some T =>
          by_cases href : CheckedBranchRefineOk gp.classes T C
          · simp [compileCheck, hΔ, href, CheckedExprLabelsRegistered] at hnode ⊢
            have hthenNode :
                cp.main.nodeAt (path ++ [.condThen]) =
                  some (compileCheck .main hthen
                    (Δ.update x (.intersection T (.class_ C))) Q n).1 := by
              simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condThen]) hnode)
            have helseNode :
                cp.main.nodeAt (path ++ [.condElse]) =
                  some (compileCheck .main helse
                    (Δ.update x (.intersection T (.negClass C))) Q
                    (compileCheck .main hthen
                      (Δ.update x (.intersection T (.class_ C))) Q n).2).1 := by
              simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condElse]) hnode)
            exact ⟨compileCheck_main_registered hcompiled
                (Δ := Δ.update x (.intersection T (.class_ C))) (Q := Q) (n := n)
                (path := path ++ [.condThen]) hthen hthenNode,
              compileCheck_main_registered hcompiled
                (Δ := Δ.update x (.intersection T (.negClass C))) (Q := Q)
                (n := (compileCheck .main hthen
                  (Δ.update x (.intersection T (.class_ C))) Q n).2)
                (path := path ++ [.condElse]) helse helseNode⟩
          · simp [compileCheck, hΔ, href, CheckedExprLabelsRegistered] at hnode ⊢
            have hthenNode :
                cp.main.nodeAt (path ++ [.condThen]) =
                  some (compileCheck .main hthen Δ Q n).1 := by
              simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condThen]) hnode)
            have helseNode :
                cp.main.nodeAt (path ++ [.condElse]) =
                  some (compileCheck .main helse Δ Q (compileCheck .main hthen Δ Q n).2).1 := by
              simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condElse]) hnode)
            exact ⟨compileCheck_main_registered hcompiled
                (Δ := Δ) (Q := Q) (n := n) (path := path ++ [.condThen]) hthen hthenNode,
              compileCheck_main_registered hcompiled
                (Δ := Δ) (Q := Q)
                (n := (compileCheck .main hthen Δ Q n).2)
                (path := path ++ [.condElse]) helse helseNode⟩
termination_by sizeOf hsrc

private theorem compileCheck_methodBody_registered
    (hcompiled : ElaboratesProgramAt gp P cp)
    (hfc : findCheckedClass cp.classes definerName = some cc)
    (hmem : cm ∈ cc.methods)
    (hcm : IsCompiledMethodAt gp.classes definerName gm cm)
    {hwfct Γ e srcTy Δ Q n path}
    (hsrc : GSrcInfer gp.classes hwfct Γ e srcTy) :
    cm.body.nodeAt path = some (compileCheck (.methodBody definerName gm.name) hsrc Δ Q n).1 →
      CheckedExprLabelsRegistered hcompiled
        (compileCheck (.methodBody definerName gm.name) hsrc Δ Q n).1 := by
  match hsrc with
  | .var (x := x) _ =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      exact ⟨trivial, fun p => ⟨.methodBodyEnforce definerName gm.name path _ p,
        ⟨cc, gm, cm, .var x, _, hfc, hmem, hcm, rfl, hnode, rfl⟩⟩⟩
  | .constNone =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      exact ⟨trivial, fun p => ⟨.methodBodyEnforce definerName gm.name path _ p,
        ⟨cc, gm, cm, .constNone, _, hfc, hmem, hcm, rfl, hnode, rfl⟩⟩⟩
  | .constTrue =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      exact ⟨trivial, fun p => ⟨.methodBodyEnforce definerName gm.name path _ p,
        ⟨cc, gm, cm, .constTrue, _, hfc, hmem, hcm, rfl, hnode, rfl⟩⟩⟩
  | .constFalse =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      exact ⟨trivial, fun p => ⟨.methodBodyEnforce definerName gm.name path _ p,
        ⟨cc, gm, cm, .constFalse, _, hfc, hmem, hcm, rfl, hnode, rfl⟩⟩⟩
  | .new (cname := cname) _ _ _ _ =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      exact ⟨trivial, fun p => ⟨.methodBodyEnforce definerName gm.name path _ p,
        ⟨cc, gm, cm, .new cname, _, hfc, hmem, hcm, rfl, hnode, rfl⟩⟩⟩
  | .attrAccess (attr := attr) hbase _ =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      have hbaseNode :
          cm.body.nodeAt (path ++ [.enforceBody, .dynAttrBase]) =
            some (compileCheck (.methodBody definerName gm.name) hbase Δ .any n).1 := by
        simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.enforceBody, .dynAttrBase]) hnode)
      have hdynNode :
          cm.body.nodeAt (path ++ [.enforceBody]) =
            some (.dynAttrAccess (compileCheck (.methodBody definerName gm.name) hbase Δ .any n).1 attr
              (freshLabel (.methodBody definerName gm.name) .context
                (compileCheck (.methodBody definerName gm.name) hbase Δ .any n).2).1) := by
        simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.enforceBody]) hnode)
      refine ⟨?_, ?_⟩
      · refine ⟨compileCheck_methodBody_registered hcompiled hfc hmem hcm
          (Δ := Δ) (Q := .any) (n := n)
          (path := path ++ [.enforceBody, .dynAttrBase]) hbase hbaseNode, ?_⟩
        exact ⟨.methodBodyDynAttr definerName gm.name (path ++ [.enforceBody]),
          ⟨cc, gm, cm, (compileCheck (.methodBody definerName gm.name) hbase Δ .any n).1,
            attr, hfc, hmem, hcm, rfl, hdynNode⟩⟩
      · intro p
        exact ⟨.methodBodyEnforce definerName gm.name path _ p,
          ⟨cc, gm, cm,
            .dynAttrAccess (compileCheck (.methodBody definerName gm.name) hbase Δ .any n).1 attr
              (freshLabel (.methodBody definerName gm.name) .context
                (compileCheck (.methodBody definerName gm.name) hbase Δ .any n).2).1,
            _, hfc, hmem, hcm, rfl, hnode, rfl⟩⟩
  | .call (argSrcTy := argSrcTy) hcallee harg _ _ _ _ =>
      let D := callParamTarget gp.classes argSrcTy
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered, D] at hnode ⊢
      have hcalleeNode :
          cm.body.nodeAt (path ++ [.callCallee]) =
            some (compileCheck (.methodBody definerName gm.name) hcallee Δ (.callable D Q) n).1 := by
        simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.callCallee]) hnode)
      have hargNode :
          cm.body.nodeAt (path ++ [.callArg]) =
            some (compileCheck (.methodBody definerName gm.name) harg Δ D
              (compileCheck (.methodBody definerName gm.name) hcallee Δ (.callable D Q) n).2).1 := by
        simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.callArg]) hnode)
      have hreturnLabels :
          BoundaryLabelsRegistered hcompiled
            (mkBoundaryLabels (.methodBody definerName gm.name) .positive
              (compileBoundaryTarget (checkedTargetOfRuntimePublicTy Q))
              (compileCheck (.methodBody definerName gm.name) harg Δ D
                (compileCheck (.methodBody definerName gm.name) hcallee Δ (.callable D Q) n).2).2).1 := by
        intro p
        refine ⟨.methodBodyCallReturn definerName gm.name path _ p, ?_⟩
        exact ⟨cc, gm, cm, _, _, _, _, hfc, hmem, hcm, rfl, hnode, rfl⟩
      exact ⟨compileCheck_methodBody_registered hcompiled hfc hmem hcm
          (Δ := Δ) (Q := .callable D Q) (n := n)
          (path := path ++ [.callCallee]) hcallee hcalleeNode,
        compileCheck_methodBody_registered hcompiled hfc hmem hcm
          (Δ := Δ) (Q := D)
          (n := (compileCheck (.methodBody definerName gm.name) hcallee Δ (.callable D Q) n).2)
          (path := path ++ [.callArg]) harg hargNode,
        hreturnLabels⟩
  | .cond _ htest _ hthen helse =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      have htestNode :
          cm.body.nodeAt (path ++ [.condTest]) =
            some (compileCheck (.methodBody definerName gm.name) htest Δ (.class_ boolClass) n).1 := by
        simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condTest]) hnode)
      have hthenNode :
          cm.body.nodeAt (path ++ [.condThen]) =
            some (compileCheck (.methodBody definerName gm.name) hthen Δ Q
              (compileCheck (.methodBody definerName gm.name) htest Δ (.class_ boolClass) n).2).1 := by
        simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condThen]) hnode)
      have helseNode :
          cm.body.nodeAt (path ++ [.condElse]) =
            some (compileCheck (.methodBody definerName gm.name) helse Δ Q
              (compileCheck (.methodBody definerName gm.name) hthen Δ Q
                (compileCheck (.methodBody definerName gm.name) htest Δ (.class_ boolClass) n).2).2).1 := by
        simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condElse]) hnode)
      exact ⟨compileCheck_methodBody_registered hcompiled hfc hmem hcm
          (Δ := Δ) (Q := .class_ boolClass) (n := n)
          (path := path ++ [.condTest]) htest htestNode,
        compileCheck_methodBody_registered hcompiled hfc hmem hcm
          (Δ := Δ) (Q := Q)
          (n := (compileCheck (.methodBody definerName gm.name) htest Δ (.class_ boolClass) n).2)
          (path := path ++ [.condThen]) hthen hthenNode,
        compileCheck_methodBody_registered hcompiled hfc hmem hcm
          (Δ := Δ) (Q := Q)
          (n := (compileCheck (.methodBody definerName gm.name) hthen Δ Q
            (compileCheck (.methodBody definerName gm.name) htest Δ (.class_ boolClass) n).2).2)
          (path := path ++ [.condElse]) helse helseNode⟩
  | .isInstance (x := x) (C := C) _ _ =>
      intro hnode
      dsimp [compileCheck, CheckedExprLabelsRegistered] at hnode ⊢
      exact ⟨trivial, fun p => ⟨.methodBodyEnforce definerName gm.name path _ p,
        ⟨cc, gm, cm, .isInstance x C, _, hfc, hmem, hcm, rfl, hnode, rfl⟩⟩⟩
  | .condIsInstance (x := x) (C := C) _ _ hthen helse =>
      intro hnode
      cases hΔ : Δ.lookup x with
      | none =>
          simp [compileCheck, hΔ, CheckedExprLabelsRegistered] at hnode ⊢
          have hthenNode :
              cm.body.nodeAt (path ++ [.condThen]) =
                some (compileCheck (.methodBody definerName gm.name) hthen Δ Q n).1 := by
            simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condThen]) hnode)
          have helseNode :
              cm.body.nodeAt (path ++ [.condElse]) =
                some (compileCheck (.methodBody definerName gm.name) helse Δ Q
                  (compileCheck (.methodBody definerName gm.name) hthen Δ Q n).2).1 := by
            simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condElse]) hnode)
          exact ⟨compileCheck_methodBody_registered hcompiled hfc hmem hcm
              (Δ := Δ) (Q := Q) (n := n) (path := path ++ [.condThen]) hthen hthenNode,
            compileCheck_methodBody_registered hcompiled hfc hmem hcm
              (Δ := Δ) (Q := Q)
              (n := (compileCheck (.methodBody definerName gm.name) hthen Δ Q n).2)
              (path := path ++ [.condElse]) helse helseNode⟩
      | some T =>
          by_cases href : CheckedBranchRefineOk gp.classes T C
          · simp [compileCheck, hΔ, href, CheckedExprLabelsRegistered] at hnode ⊢
            have hthenNode :
                cm.body.nodeAt (path ++ [.condThen]) =
                  some (compileCheck (.methodBody definerName gm.name) hthen
                    (Δ.update x (.intersection T (.class_ C))) Q n).1 := by
              simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condThen]) hnode)
            have helseNode :
                cm.body.nodeAt (path ++ [.condElse]) =
                  some (compileCheck (.methodBody definerName gm.name) helse
                    (Δ.update x (.intersection T (.negClass C))) Q
                    (compileCheck (.methodBody definerName gm.name) hthen
                      (Δ.update x (.intersection T (.class_ C))) Q n).2).1 := by
              simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condElse]) hnode)
            exact ⟨compileCheck_methodBody_registered hcompiled hfc hmem hcm
                (Δ := Δ.update x (.intersection T (.class_ C))) (Q := Q) (n := n)
                (path := path ++ [.condThen]) hthen hthenNode,
              compileCheck_methodBody_registered hcompiled hfc hmem hcm
                (Δ := Δ.update x (.intersection T (.negClass C))) (Q := Q)
                (n := (compileCheck (.methodBody definerName gm.name) hthen
                  (Δ.update x (.intersection T (.class_ C))) Q n).2)
                (path := path ++ [.condElse]) helse helseNode⟩
          · simp [compileCheck, hΔ, href, CheckedExprLabelsRegistered] at hnode ⊢
            have hthenNode :
                cm.body.nodeAt (path ++ [.condThen]) =
                  some (compileCheck (.methodBody definerName gm.name) hthen Δ Q n).1 := by
              simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condThen]) hnode)
            have helseNode :
                cm.body.nodeAt (path ++ [.condElse]) =
                  some (compileCheck (.methodBody definerName gm.name) helse Δ Q
                    (compileCheck (.methodBody definerName gm.name) hthen Δ Q n).2).1 := by
              simpa [CheckedExpr.nodeAt] using (CheckedExpr.nodeAt_append (p := path) (q := [.condElse]) hnode)
            exact ⟨compileCheck_methodBody_registered hcompiled hfc hmem hcm
                (Δ := Δ) (Q := Q) (n := n) (path := path ++ [.condThen]) hthen hthenNode,
              compileCheck_methodBody_registered hcompiled hfc hmem hcm
                (Δ := Δ) (Q := Q)
                (n := (compileCheck (.methodBody definerName gm.name) hthen Δ Q n).2)
                (path := path ++ [.condElse]) helse helseNode⟩
termination_by sizeOf hsrc

theorem main_registered
    (hcompiled : ElaboratesProgramAt gp P cp) :
    CheckedExprLabelsRegistered hcompiled cp.main := by
  have hnode : cp.main.nodeAt [] = some (compileCheck .main hcompiled.main_hsrc [] P 0).1 := by
    simp [hcompiled.main_eq, CheckedExpr.nodeAt]
  simpa [hcompiled.main_eq] using
    compileCheck_main_registered hcompiled (Δ := []) (Q := P) (n := 0)
      (path := []) hcompiled.main_hsrc hnode

theorem checkedMethod_body_registered
    (hreg : CheckedMethodLabelsRegistered hcompiled cm) :
    CheckedExprLabelsRegistered hcompiled cm.body := by
  rcases hreg with ⟨definerName, cc, gm, hfc, hmem, hcm⟩
  obtain ⟨_, _, hsrc, hbody⟩ := hcm.body_compiled
  have hnode :
      cm.body.nodeAt [] =
        some (compileCheck (.methodBody definerName gm.name) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1 := by
    simp [hbody, CheckedExpr.nodeAt]
  simpa [hbody] using
    compileCheck_methodBody_registered hcompiled hfc hmem hcm
      (Δ := [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)])
      (Q := gm.returnTy) (n := 0) (path := []) hsrc hnode

theorem initialHeap_registered
    (hcompiled : ElaboratesProgramAt gp P cp) :
    HeapLabelsRegistered hcompiled CheckedHeap.initial := by
  intro _ _ _ hlookup
  unfold CheckedHeap.initial at hlookup
  unfold CheckedHeap.lookup at hlookup
  simp only [RuntimeHeap.lookup, RuntimeHeap.lookupList, noneOid, trueOid, falseOid] at hlookup
  split at hlookup
  · exfalso
    have hclass : noneClass = boundMethodClass := by
      exact congrArg CheckedHeapObject.className (Option.some.inj hlookup)
    exact (by decide : noneClass ≠ boundMethodClass) hclass
  · split at hlookup
    · exfalso
      have hclass : boolClass = boundMethodClass := by
        exact congrArg CheckedHeapObject.className (Option.some.inj hlookup)
      exact (by decide : boolClass ≠ boundMethodClass) hclass
    · split at hlookup
      · exfalso
        have hclass : boolClass = boundMethodClass := by
          exact congrArg CheckedHeapObject.className (Option.some.inj hlookup)
        exact (by decide : boolClass ≠ boundMethodClass) hclass
      · cases hlookup

theorem initialState_registered
    (hcompiled : ElaboratesProgramAt gp P cp) :
    StateLabelsRegistered hcompiled (initialState cp) := by
  refine ⟨initialHeap_registered hcompiled, env_nil_registered, ?_, ?_⟩
  · simpa [initialState, expressionState, ControlLabelsRegistered] using main_registered hcompiled
  · intro frame hmem
    cases hmem

theorem enforceValue_ok_registered
    (hcompiled : ElaboratesProgramAt gp P cp)
    {c : BoundaryContract}
    {labels : BoundaryLabels c}
    (hlabels : BoundaryLabelsRegistered hcompiled labels)
    (_hheap : HeapLabelsRegistered hcompiled heap)
    (hv : CheckedValueLabelsRegistered hcompiled v)
    (henf : EnforceValue gp.classes heap v c labels r) :
    ∀ v', r = .ok v' → CheckedValueLabelsRegistered hcompiled v' := by
  induction henf generalizing hcompiled with
  | unknown => intro _ hr; cases hr; simpa using hv
  | classObjRefOk | callableObjRefTransparentOk | negClassObjRefOk =>
      intro _ hr; cases hr; trivial
  | unionLeft _ ih | unionRight _ _ _ ih =>
      exact ih hcompiled (boundaryLabels_subtree_registered hlabels) _hheap hv
  | intersectionOk _ _ ihLeft ihRight =>
      have hv' : CheckedValueLabelsRegistered hcompiled _ :=
        ihLeft hcompiled (boundaryLabels_subtree_registered hlabels) _hheap hv _ rfl
      exact ihRight hcompiled (boundaryLabels_subtree_registered hlabels) _hheap hv'
  | bottom | classObjRefBlame | callableObjRefBlame | unionBlame
  | intersectionBlameLeft | intersectionBlameRight | negClassObjRefBlame =>
      intro _ hr; cases hr

theorem enforceValue_blame_registered
    (hcompiled : ElaboratesProgramAt gp P cp)
    {c : BoundaryContract}
    {labels : BoundaryLabels c}
    (hlabels : BoundaryLabelsRegistered hcompiled labels)
    (_hheap : HeapLabelsRegistered hcompiled heap)
    (_hv : CheckedValueLabelsRegistered hcompiled v)
    (henf : EnforceValue gp.classes heap v c labels r) :
    ∀ ℓ, r = .blame ℓ → CompiledBoundaryLabel hcompiled ℓ := by
  induction henf generalizing hcompiled with
  | bottom | classObjRefBlame | callableObjRefBlame | unionBlame
  | intersectionBlameLeft | intersectionBlameRight | negClassObjRefBlame =>
      intro _ hr; cases hr; simpa using boundaryLabels_direct_registered hlabels
  | unknown | classObjRefOk | callableObjRefTransparentOk | unionLeft
  | unionRight | intersectionOk | negClassObjRefOk =>
      intro _ hr; cases hr

theorem heap_alloc_preserves_HeapLabelsRegistered
    (hcompiled : ElaboratesProgramAt gp P cp)
    (hheap : HeapLabelsRegistered hcompiled heap)
    (halloc : heap.alloc obj = (oid, heap'))
    (hnew :
      ∀ recvOid cm,
        obj = ⟨boundMethodClass, .boundMethod recvOid cm⟩ →
          CheckedMethodLabelsRegistered hcompiled cm) :
    HeapLabelsRegistered hcompiled heap' := by
  intro oid' recvOid' cm' hlookup
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj halloc
  unfold CheckedHeap.lookup at hlookup
  simp only [RuntimeHeap.lookup, RuntimeHeap.lookupList] at hlookup
  split at hlookup
  · exact hnew _ _ (Option.some.inj hlookup)
  · exact hheap _ _ _ hlookup

private theorem tail_frames_registered
    (hcont : ∀ frame ∈ head :: k, FrameLabelsRegistered hcompiled frame) :
    ∀ frame ∈ k, FrameLabelsRegistered hcompiled frame := by
  intro frame hmem
  exact hcont frame (by simp [hmem])

private theorem cons_frames_registered
    (hhead : FrameLabelsRegistered hcompiled head)
    (hcont : ∀ frame ∈ k, FrameLabelsRegistered hcompiled frame) :
    ∀ frame ∈ head :: k, FrameLabelsRegistered hcompiled frame := by
  intro frame hmem
  cases hmem with
  | head =>
      simpa using hhead
  | tail _ hmem =>
      exact hcont _ hmem

theorem step_preserves_registered
    (hcompiled : ElaboratesProgramAt gp P cp)
    (hreg : StateLabelsRegistered hcompiled s)
    (hstep : Checked.Step gp.classes cp.classes s s') :
    StateLabelsRegistered hcompiled s' := by
  rcases hreg with ⟨hheap, henv, hctrl, hcont⟩
  cases hstep with
  | focusAttrAccess =>
      exact ⟨hheap, henv, hctrl,
        cons_frames_registered (by simp [FrameLabelsRegistered]) hcont⟩
  | focusCall =>
      rcases hctrl with ⟨hcallee, harg, hreturnLabels⟩
      exact ⟨hheap, henv, hcallee,
        cons_frames_registered ⟨harg, hreturnLabels⟩ hcont⟩
  | focusCond _ =>
      rcases hctrl with ⟨htest, hthen, helse⟩
      exact ⟨hheap, henv, htest,
        cons_frames_registered ⟨hthen, helse⟩ hcont⟩
  | condIsInstanceTrue _ _ _ _ _ =>
      rcases hctrl with ⟨_, hthen, _⟩
      exact ⟨hheap, henv, hthen,
        cons_frames_registered (by simpa [FrameLabelsRegistered] using henv) hcont⟩
  | condIsInstanceFalse _ _ _ _ _ =>
      rcases hctrl with ⟨_, _, helse⟩
      exact ⟨hheap, henv, helse,
        cons_frames_registered (by simpa [FrameLabelsRegistered] using henv) hcont⟩
  | condIsInstanceVarNotFound _ | varError _ =>
      exact ⟨hheap, henv, trivial, hcont⟩
  | focusEnforce =>
      rcases hctrl with ⟨he, hlabels⟩
      exact ⟨hheap, henv, he,
        cons_frames_registered (by simpa [FrameLabelsRegistered] using hlabels) hcont⟩
  | focusDynAttrAccess =>
      rcases hctrl with ⟨hbase, hlabel⟩
      exact ⟨hheap, henv, hbase,
        cons_frames_registered (by simpa [FrameLabelsRegistered] using hlabel) hcont⟩
  | varSuccess hlookup =>
      exact ⟨hheap, henv, henv _ _ hlookup, hcont⟩
  | newSuccess _ _ _ hbm halloc =>
      have hheap' := heap_alloc_preserves_HeapLabelsRegistered hcompiled hheap halloc
        (fun _ _ hEq => by
          have hpayload : CheckedObjectPayload.ordinary = .boundMethod _ _ :=
            congrArg CheckedHeapObject.payload hEq
          cases hpayload)
      exact ⟨hheap', henv, trivial, hcont⟩
  | newClassNotFound _ | newBuiltinError _ _ | constNone | constTrue | constFalse
  | isInstanceTrue _ _ _ _ _ | isInstanceFalse _ _ _ _ _ | isInstanceVarNotFound _ =>
      exact ⟨hheap, henv, trivial, hcont⟩
  | returnAttrAccess _ _ hmro hfindMethod halloc =>
      have hcm : CheckedMethodLabelsRegistered hcompiled _ :=
        checkedMethodInMro_registered hcompiled hmro hfindMethod
      have hheap' := heap_alloc_preserves_HeapLabelsRegistered hcompiled hheap halloc
        (fun _ _ hEq => by
          cases hEq
          exact hcm)
      exact ⟨hheap', henv, trivial, tail_frames_registered hcont⟩
  | returnAttrAccessNotFound _ _ _ _ | returnCallCalleeNotCallable _
  | returnCallValueNotCallable _ | returnCondNotBool _ _ | errorUnwindAttrAccess
  | errorUnwindCallCallee | errorUnwindAwaitArgument | errorUnwindCallValue
  | errorUnwindCond | errorUnwindEnforce | errorUnwindDynAttrAccess =>
      exact ⟨hheap, henv, trivial, tail_frames_registered hcont⟩
  | returnDynAttrAccess _ _ hmro hfindMethod halloc =>
      have hcm : CheckedMethodLabelsRegistered hcompiled _ :=
        checkedMethodInMro_registered hcompiled hmro hfindMethod
      have hheap' := heap_alloc_preserves_HeapLabelsRegistered hcompiled hheap halloc
        (fun _ _ hEq => by
          cases hEq
          exact hcm)
      exact ⟨hheap', henv, trivial, tail_frames_registered hcont⟩
  | returnDynAttrAccessNotFound _ _ _ _ =>
      rename_i obj cls mro attr heap0 env0 objOid lbl k hlook hfind hmro hnone
      have hframe : CompiledBoundaryLabel hcompiled lbl := by
        simpa [FrameLabelsRegistered] using
          (hcont (.dynAttrAccess attr lbl) (by simp))
      exact ⟨hheap, henv, hframe, tail_frames_registered hcont⟩
  | returnCallCalleeBound hlookup =>
      rename_i heap0 env0 calleeOid arg paramTy returnTy returnLabels k recvOid m
      have hframe :
          CheckedExprLabelsRegistered hcompiled arg ∧
            BoundaryLabelsRegistered hcompiled returnLabels := by
        simpa [FrameLabelsRegistered] using
          (hcont (.callCallee arg paramTy returnTy returnLabels) (by simp))
      rcases hframe with ⟨harg, hreturnLabels⟩
      have hm : CheckedMethodLabelsRegistered hcompiled m :=
        hheap _ _ _ hlookup
      exact ⟨hheap, henv, harg,
        cons_frames_registered ⟨hm, hreturnLabels⟩ (tail_frames_registered hcont)⟩
  | returnAwaitArgumentOk henf =>
      rename_i heap0 argVal argVal' env0 recvOid m returnTy returnLabels k
      have hframe :
          CheckedMethodLabelsRegistered hcompiled m ∧
            BoundaryLabelsRegistered hcompiled returnLabels := by
        simpa [FrameLabelsRegistered] using
          (hcont (.awaitArgument recvOid m returnTy returnLabels) (by simp))
      rcases hframe with ⟨hm, hcallReturnLabels⟩
      have hparamLabels := checkedMethod_parameterLabels_registered hm
      have harg' : CheckedValueLabelsRegistered hcompiled argVal' :=
        enforceValue_ok_registered hcompiled hparamLabels hheap hctrl henf _ rfl
      have hrecvEnv : CheckedEnvLabelsRegistered hcompiled
          [(m.receiverParam, .objRef recvOid)] :=
        env_cons_registered trivial env_nil_registered
      have hcallEnv : CheckedEnvLabelsRegistered hcompiled
          [(m.param, argVal'), (m.receiverParam, .objRef recvOid)] :=
        env_cons_registered harg' hrecvEnv
      have hbody : CheckedExprLabelsRegistered hcompiled m.body :=
        checkedMethod_body_registered hm
      have hretLabels := checkedMethod_returnLabels_registered hm
      exact ⟨hheap, hcallEnv, hbody,
        cons_frames_registered (by simpa [FrameLabelsRegistered] using hretLabels)
          (cons_frames_registered (by simpa [FrameLabelsRegistered] using hcallReturnLabels)
            (cons_frames_registered (by simpa [FrameLabelsRegistered] using henv)
              (tail_frames_registered hcont)))⟩
  | returnAwaitArgumentBlame henf =>
      rename_i heap0 argVal env0 recvOid m returnTy returnLabels k
      have hframe :
          CheckedMethodLabelsRegistered hcompiled m ∧
            BoundaryLabelsRegistered hcompiled returnLabels := by
        simpa [FrameLabelsRegistered] using
          (hcont (.awaitArgument recvOid m returnTy returnLabels) (by simp))
      rcases hframe with ⟨hm, _hcallReturnLabels⟩
      have hparamLabels := checkedMethod_parameterLabels_registered hm
      have hblame : CompiledBoundaryLabel hcompiled m.parameterLabels.direct :=
        enforceValue_blame_registered hcompiled hparamLabels hheap hctrl henf _ rfl
      exact ⟨hheap, henv, hblame, tail_frames_registered hcont⟩
  | returnCallValueBound hlookup =>
      rename_i heap0 env0 calleeOid argVal paramTy returnTy returnLabels k recvOid m
      have hframe :
          CheckedValueLabelsRegistered hcompiled argVal ∧
            BoundaryLabelsRegistered hcompiled returnLabels := by
        simpa [FrameLabelsRegistered] using
          (hcont (.callValue argVal paramTy returnTy returnLabels) (by simp))
      rcases hframe with ⟨harg, hreturnLabels⟩
      have hm : CheckedMethodLabelsRegistered hcompiled m :=
        hheap _ _ _ hlookup
      exact ⟨hheap, henv, harg,
        cons_frames_registered ⟨hm, hreturnLabels⟩ (tail_frames_registered hcont)⟩
  | returnCondTrue =>
      rename_i heap0 env0 thenBr elseBr k
      have hframe :
          CheckedExprLabelsRegistered hcompiled thenBr ∧
            CheckedExprLabelsRegistered hcompiled elseBr := by
        simpa [FrameLabelsRegistered] using
          (hcont (.cond thenBr elseBr) (by simp))
      rcases hframe with ⟨hthen, _⟩
      exact ⟨hheap, henv, hthen, tail_frames_registered hcont⟩
  | returnCondFalse =>
      rename_i heap0 env0 thenBr elseBr k
      have hframe :
          CheckedExprLabelsRegistered hcompiled thenBr ∧
            CheckedExprLabelsRegistered hcompiled elseBr := by
        simpa [FrameLabelsRegistered] using
          (hcont (.cond thenBr elseBr) (by simp))
      rcases hframe with ⟨_, helse⟩
      exact ⟨hheap, henv, helse, tail_frames_registered hcont⟩
  | returnFromBody =>
      rename_i heap0 env0 v callerEnv k
      have hcallerEnv : CheckedEnvLabelsRegistered hcompiled callerEnv := by
        simpa [FrameLabelsRegistered] using
          (hcont (.returnTo callerEnv) (by simp))
      exact ⟨hheap, hcallerEnv, hctrl, tail_frames_registered hcont⟩
  | returnEnforceOk henf =>
      rename_i heap0 v c labels v' env0 k
      have hlabels : BoundaryLabelsRegistered hcompiled labels := by
        simpa [FrameLabelsRegistered] using
          (hcont (.enforce c labels) (by simp))
      have hv' : CheckedValueLabelsRegistered hcompiled v' :=
        enforceValue_ok_registered hcompiled hlabels hheap hctrl henf _ rfl
      exact ⟨hheap, henv, hv', tail_frames_registered hcont⟩
  | returnEnforceBlame henf =>
      rename_i heap0 v c labels env0 k
      have hlabels : BoundaryLabelsRegistered hcompiled labels := by
        simpa [FrameLabelsRegistered] using
          (hcont (.enforce c labels) (by simp))
      have hblame : CompiledBoundaryLabel hcompiled labels.direct :=
        enforceValue_blame_registered hcompiled hlabels hheap hctrl henf _ rfl
      exact ⟨hheap, henv, hblame, tail_frames_registered hcont⟩
  | blameUnwindAttrAccess | blameUnwindCallCallee | blameUnwindAwaitArgument
  | blameUnwindCallValue | blameUnwindCond | blameUnwindEnforce
  | blameUnwindDynAttrAccess =>
      exact ⟨hheap, henv, hctrl, tail_frames_registered hcont⟩
  | blameUnwindReturnTo =>
      rename_i heap0 env0 lbl callerEnv k
      have hcallerEnv : CheckedEnvLabelsRegistered hcompiled callerEnv := by
        simpa [FrameLabelsRegistered] using
          (hcont (.returnTo callerEnv) (by simp))
      exact ⟨hheap, hcallerEnv, hctrl, tail_frames_registered hcont⟩
  | errorUnwindReturnTo =>
      rename_i heap0 env0 err callerEnv k
      have hcallerEnv : CheckedEnvLabelsRegistered hcompiled callerEnv := by
        simpa [FrameLabelsRegistered] using
          (hcont (.returnTo callerEnv) (by simp))
      exact ⟨hheap, hcallerEnv, trivial, tail_frames_registered hcont⟩

theorem steps_preserve_registered
    (hcompiled : ElaboratesProgramAt gp P cp)
    (hreg : StateLabelsRegistered hcompiled s)
    (hsteps : Checked.Steps gp.classes cp.classes s s') :
    StateLabelsRegistered hcompiled s' := by
  induction hsteps with
  | refl =>
      exact hreg
  | step hs hsteps ih =>
      exact ih (step_preserves_registered hcompiled hreg hs)

private theorem compileCheck_dynAttr_scope_fixed
    (scope : LabelScope)
    {Γ e srcTy Δ P n exprPath e' attr ℓ}
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    (compileCheck scope hsrc Δ P n).1.nodeAt exprPath = some (.dynAttrAccess e' attr ℓ) →
      ℓ.scope = scope := by
  match hsrc with
  | .var _ | .constNone | .constTrue | .constFalse | .new _ _ _ _ | .isInstance _ _ =>
      intro hnode
      cases exprPath with
      | nil =>
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case enforceBody =>
            cases rest <;> simp [CheckedExpr.nodeAt] at hnode
  | .attrAccess (attr := attrName) hbase _ =>
      intro hnode
      cases exprPath with
      | nil => simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          cases child <;>
            (try simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode)
          case enforceBody =>
              cases rest with
              | nil =>
                  simp [CheckedExpr.nodeAt] at hnode
                  rcases hnode with ⟨rfl, rfl, rfl⟩
                  rfl
              | cons child' tail =>
                  cases child' <;>
                    (try simp [CheckedExpr.nodeAt] at hnode)
                  case dynAttrBase =>
                      exact compileCheck_dynAttr_scope_fixed
                        (scope := scope) (Δ := Δ) (P := .any) (n := n)
                        (exprPath := tail) (e' := e') (attr := attr) (ℓ := ℓ)
                        hbase hnode
  | .call (argSrcTy := argSrcTy) hcallee harg _ _ _ _ =>
      let D := callParamTarget gct argSrcTy
      intro hnode
      cases exprPath with
      | nil => simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case callCallee =>
              exact compileCheck_dynAttr_scope_fixed
                (scope := scope) (Δ := Δ) (P := .callable D P) (n := n)
                (exprPath := rest) (e' := e') (attr := attr) (ℓ := ℓ)
                hcallee hnode
          case callArg =>
              exact compileCheck_dynAttr_scope_fixed
                (scope := scope) (Δ := Δ) (P := D)
                (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
                (exprPath := rest) (e' := e') (attr := attr) (ℓ := ℓ)
                harg hnode
  | .cond _ htest _ hthen helse =>
      intro hnode
      cases exprPath with
      | nil => simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case condTest =>
              exact compileCheck_dynAttr_scope_fixed
                (scope := scope) (Δ := Δ) (P := .class_ boolClass) (n := n)
                (exprPath := rest) (e' := e') (attr := attr) (ℓ := ℓ)
                htest hnode
          case condThen =>
              exact compileCheck_dynAttr_scope_fixed
                (scope := scope) (Δ := Δ) (P := P)
                (n := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                (exprPath := rest) (e' := e') (attr := attr) (ℓ := ℓ)
                hthen hnode
          case condElse =>
              exact compileCheck_dynAttr_scope_fixed
                (scope := scope) (Δ := Δ) (P := P)
                (n := (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                (exprPath := rest) (e' := e') (attr := attr) (ℓ := ℓ)
                helse hnode
  | .condIsInstance (x := x) (C := C) _ _ hthen helse =>
      intro hnode
      cases hΔ : Δ.lookup x with
      | none =>
          cases exprPath with
          | nil => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
          | cons child rest =>
              cases child with
              | condTest =>
                  simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
                  cases rest <;> simp [CheckedExpr.nodeAt] at hnode
              | condThen =>
                  simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
                  exact compileCheck_dynAttr_scope_fixed
                    (scope := scope) (Δ := Δ) (P := P) (n := n)
                    (exprPath := rest) (e' := e') (attr := attr) (ℓ := ℓ)
                    hthen hnode
              | condElse =>
                  simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
                  exact compileCheck_dynAttr_scope_fixed
                    (scope := scope) (Δ := Δ) (P := P)
                    (n := (compileCheck scope hthen Δ P n).2)
                    (exprPath := rest) (e' := e') (attr := attr) (ℓ := ℓ)
                    helse hnode
              | attrBase | callCallee | callArg | enforceBody | dynAttrBase =>
                  simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
      | some T =>
          by_cases href : CheckedBranchRefineOk gct T C
          · cases exprPath with
            | nil => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
            | cons child rest =>
                cases child with
                | condTest =>
                    simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                    cases rest <;> simp [CheckedExpr.nodeAt] at hnode
                | condThen =>
                    simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                    exact compileCheck_dynAttr_scope_fixed
                      (scope := scope) (Δ := Δ.update x (.intersection T (.class_ C)))
                      (P := P) (n := n)
                      (exprPath := rest) (e' := e') (attr := attr) (ℓ := ℓ)
                      hthen hnode
                | condElse =>
                    simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                    exact compileCheck_dynAttr_scope_fixed
                      (scope := scope) (Δ := Δ.update x (.intersection T (.negClass C)))
                      (P := P)
                      (n := (compileCheck scope hthen
                        (Δ.update x (.intersection T (.class_ C))) P n).2)
                      (exprPath := rest) (e' := e') (attr := attr) (ℓ := ℓ)
                      helse hnode
                | attrBase | callCallee | callArg | enforceBody | dynAttrBase =>
                    simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
          · cases exprPath with
            | nil => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
            | cons child rest =>
                cases child with
                | condTest =>
                    simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                    cases rest <;> simp [CheckedExpr.nodeAt] at hnode
                | condThen =>
                    simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                    exact compileCheck_dynAttr_scope_fixed
                      (scope := scope) (Δ := Δ) (P := P) (n := n)
                      (exprPath := rest) (e' := e') (attr := attr) (ℓ := ℓ)
                      hthen hnode
                | condElse =>
                    simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                    exact compileCheck_dynAttr_scope_fixed
                      (scope := scope) (Δ := Δ) (P := P)
                      (n := (compileCheck scope hthen Δ P n).2)
                      (exprPath := rest) (e' := e') (attr := attr) (ℓ := ℓ)
                      helse hnode
                | attrBase | callCallee | callArg | enforceBody | dynAttrBase =>
                    simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode

private theorem BoundaryPath.cast_injective
    {c c' : BoundaryContract}
    (h : c = c') :
    Function.Injective (fun p : BoundaryPath c => cast (congrArg BoundaryPath h) p) := by
  intro p q hp
  cases h
  simpa using hp

theorem compiled_boundary_origin_scope
    (hcompiled : ElaboratesProgramAt gp P cp)
    (horig : CompiledBoundaryOrigin hcompiled origin ℓ) :
    ℓ.scope = origin.labelScope := by
  cases origin with
  | mainEnforce exprPath c p =>
      rcases horig with ⟨e, labels, hnode, rfl⟩
      have hnode' :
          (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPath =
            some (.enforce e c labels) := by
        simpa [hcompiled.main_eq] using hnode
      obtain ⟨k, hk⟩ := compileCheck_enforce_labels_form
        (scope := .main) (hsrc := hcompiled.main_hsrc) (Δ := []) (P := P) (n := 0)
        (exprPath := exprPath) (e' := e) (c := c) (labels := labels) hnode'
      rw [hk]
      simpa using mkBoundaryLabels_scope_fixed (compileBoundaryTarget c) p .main .positive k
  | mainDynAttr exprPath =>
      rcases horig with ⟨e, attr, hnode⟩
      have hnode' :
          (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPath =
            some (.dynAttrAccess e attr ℓ) := by
        simpa [hcompiled.main_eq] using hnode
      exact compileCheck_dynAttr_scope_fixed
        (scope := .main) (Δ := []) (P := P) (n := 0) (exprPath := exprPath)
        (e' := e) (attr := attr) (ℓ := ℓ) hcompiled.main_hsrc hnode'
  | mainCallReturn exprPath c p =>
      rcases horig with ⟨callee, arg, paramTy, labels, hnode, hlabel⟩
      have hnode' :
          (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPath =
            some (.call callee arg paramTy c labels) := by
        simpa [hcompiled.main_eq] using hnode
      obtain ⟨k, hlabels⟩ := compileCheck_call_return_labels_form
        (scope := .main) (hsrc := hcompiled.main_hsrc) (Δ := []) (P := P) (n := 0)
        (exprPath := exprPath) (callee := callee) (arg := arg)
        (paramTy := paramTy) (returnTy := c) hnode'
      have hlabel' : ℓ = labels.at p := by simpa using hlabel
      rw [hlabel', hlabels]
      simpa using
        mkBoundaryLabels_scope_fixed (compileBoundaryTarget c) p .main .positive k
  | methodParameter definerName methodName c p =>
      rcases horig with ⟨cc, gm, cm, hfc, hmem, hcm, hc, hname, hlabel⟩
      cases hc
      rw [hlabel]
      have hcontract : cm.parameterContract = compileBoundaryRaw gm.paramTy := by
        simpa [hcm.paramTy_eq] using hcm.paramContract_eq
      have hlabelsEq :
          cast (congrArg BoundaryLabels hcontract) cm.parameterLabels =
            (mkBoundaryLabels (.methodParameter definerName gm.name) .negative
              (compileBoundaryRaw gm.paramTy) 0).1 := by
        simpa [hcontract] using hcm.parameterLabels_eq
      calc
        (cm.parameterLabels.at p).scope
            = ((cast (congrArg BoundaryLabels hcontract) cm.parameterLabels).at
                (cast (congrArg BoundaryPath hcontract) p)).scope := by
              simpa using congrArg Label.scope
                (BoundaryLabels.at_cast hcontract cm.parameterLabels p).symm
        _ = (((mkBoundaryLabels (.methodParameter definerName gm.name) .negative
                (compileBoundaryRaw gm.paramTy) 0).1).at
              (cast (congrArg BoundaryPath hcontract) p)).scope := by rw [hlabelsEq]
        _ = .methodParameter definerName methodName := by
              simpa [hname] using
                (mkBoundaryLabels_scope_fixed (compileBoundaryRaw gm.paramTy)
                  (cast (congrArg BoundaryPath hcontract) p)
                  (.methodParameter definerName gm.name) .negative 0)
  | methodReturn definerName methodName c p =>
      rcases horig with ⟨cc, gm, cm, hfc, hmem, hcm, hc, hname, hlabel⟩
      cases hc
      rw [hlabel]
      have hcontract : cm.returnContract = compileBoundaryRaw gm.returnTy := by
        simpa [hcm.returnTy_eq] using hcm.returnContract_eq
      have hlabelsEq :
          cast (congrArg BoundaryLabels hcontract) cm.returnLabels =
            (mkBoundaryLabels (.methodReturn definerName gm.name) .positive
              (compileBoundaryRaw gm.returnTy) 0).1 := by
        simpa [hcontract] using hcm.returnLabels_eq
      calc
        (cm.returnLabels.at p).scope
            = ((cast (congrArg BoundaryLabels hcontract) cm.returnLabels).at
                (cast (congrArg BoundaryPath hcontract) p)).scope := by
              simpa using congrArg Label.scope
                (BoundaryLabels.at_cast hcontract cm.returnLabels p).symm
        _ = (((mkBoundaryLabels (.methodReturn definerName gm.name) .positive
                (compileBoundaryRaw gm.returnTy) 0).1).at
              (cast (congrArg BoundaryPath hcontract) p)).scope := by rw [hlabelsEq]
        _ = .methodReturn definerName methodName := by
              simpa [hname] using
                (mkBoundaryLabels_scope_fixed (compileBoundaryRaw gm.returnTy)
                  (cast (congrArg BoundaryPath hcontract) p)
                  (.methodReturn definerName gm.name) .positive 0)
  | methodBodyEnforce definerName methodName exprPath c p =>
      rcases horig with ⟨cc, gm, cm, e, labels, hfc, hmem, hcm, hname, hnode, rfl⟩
      obtain ⟨_, _, hsrc, hbody⟩ := hcm.body_compiled
      have hnode' :
          (compileCheck (.methodBody definerName methodName) hsrc
            [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
            gm.returnTy 0).1.nodeAt exprPath =
            some (.enforce e c labels) := by
        simpa [hbody, hname] using hnode
      obtain ⟨k, hk⟩ := compileCheck_enforce_labels_form
        (scope := .methodBody definerName methodName) (hsrc := hsrc)
        (Δ := [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)])
        (P := gm.returnTy) (n := 0) (exprPath := exprPath)
        (e' := e) (c := c) (labels := labels) hnode'
      rw [hk]
      simpa using
        mkBoundaryLabels_scope_fixed (compileBoundaryTarget c) p
          (.methodBody definerName methodName) .positive k
  | methodBodyDynAttr definerName methodName exprPath =>
      rcases horig with ⟨cc, gm, cm, e, attr, hfc, hmem, hcm, hname, hnode⟩
      obtain ⟨_, _, hsrc, hbody⟩ := hcm.body_compiled
      have hnode' :
          (compileCheck (.methodBody definerName methodName) hsrc
            [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
            gm.returnTy 0).1.nodeAt exprPath =
            some (.dynAttrAccess e attr ℓ) := by
        simpa [hbody, hname] using hnode
      exact compileCheck_dynAttr_scope_fixed
        (scope := .methodBody definerName methodName)
        (Δ := [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)])
        (P := gm.returnTy) (n := 0) (exprPath := exprPath)
        (e' := e) (attr := attr) (ℓ := ℓ) hsrc hnode'
  | methodBodyCallReturn definerName methodName exprPath c p =>
      rcases horig with ⟨cc, gm, cm, callee, arg, paramTy, labels,
        hfc, hmem, hcm, hname, hnode, hlabel⟩
      obtain ⟨_, _, hsrc, hbody⟩ := hcm.body_compiled
      have hnode' :
          (compileCheck (.methodBody definerName methodName) hsrc
            [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
            gm.returnTy 0).1.nodeAt exprPath =
            some (.call callee arg paramTy c labels) := by
        simpa [hbody, hname] using hnode
      obtain ⟨k, hlabels⟩ := compileCheck_call_return_labels_form
        (scope := .methodBody definerName methodName) (hsrc := hsrc)
        (Δ := [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)])
        (P := gm.returnTy) (n := 0) (exprPath := exprPath)
        (callee := callee) (arg := arg) (paramTy := paramTy) (returnTy := c) hnode'
      have hlabel' : ℓ = labels.at p := by simpa using hlabel
      rw [hlabel', hlabels]
      simpa using
        mkBoundaryLabels_scope_fixed (compileBoundaryTarget c) p
          (.methodBody definerName methodName) .positive k

private theorem compiled_boundary_origin_labelScope_eq
    (hcompiled : ElaboratesProgramAt gp P cp)
    (horig₁ : CompiledBoundaryOrigin hcompiled origin₁ ℓ₁)
    (horig₂ : CompiledBoundaryOrigin hcompiled origin₂ ℓ₂)
    (hscope : ℓ₁.scope = ℓ₂.scope) :
    origin₁.labelScope = origin₂.labelScope := by
  calc
    origin₁.labelScope = ℓ₁.scope := (compiled_boundary_origin_scope hcompiled horig₁).symm
    _ = ℓ₂.scope := hscope
    _ = origin₂.labelScope := compiled_boundary_origin_scope hcompiled horig₂

theorem compiled_boundary_same_scope_same_site_same_origin
    (hwfct : WellFormedGClassTableCore gp.classes)
    (hcompiled : ElaboratesProgramAt gp P cp)
    (horig₁ : CompiledBoundaryOrigin hcompiled origin₁ ℓ₁)
    (horig₂ : CompiledBoundaryOrigin hcompiled origin₂ ℓ₂)
    (hscope : ℓ₁.scope = ℓ₂.scope)
    (hsite : ℓ₁.site = ℓ₂.site) :
    origin₁ = origin₂ := by
  cases origin₁ <;> cases origin₂
  all_goals
    try
      have hs := compiled_boundary_origin_labelScope_eq hcompiled horig₁ horig₂ hscope
      cases hs
  case mainEnforce.mainEnforce.refl =>
    rename_i exprPath₁ c₁ p₁ exprPath₂ c₂ p₂
    rcases horig₁ with ⟨e₁, labels₁, hnode₁, rfl⟩
    rcases horig₂ with ⟨e₂, labels₂, hnode₂, rfl⟩
    have hnode₁' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPath₁ =
          some (.enforce e₁ c₁ labels₁) := by
      simpa [hcompiled.main_eq] using hnode₁
    have hnode₂' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPath₂ =
          some (.enforce e₂ c₂ labels₂) := by
      simpa [hcompiled.main_eq] using hnode₂
    obtain ⟨hpath, hlabels, hc⟩ := compileCheck_enforce_site_unique
      (scope := .main) (hsrc := hcompiled.main_hsrc) (Δ := []) (P := P) (n := 0)
      (exprPath₁ := exprPath₁) (exprPath₂ := exprPath₂)
      (e₁ := e₁) (e₂ := e₂) (c₁ := c₁) (c₂ := c₂)
      (labels₁ := labels₁) (labels₂ := labels₂) (p₁ := p₁) (p₂ := p₂)
      hnode₁' hnode₂' hsite
    cases hpath
    cases hc
    have hlabelsEq : labels₁ = labels₂ := eq_of_heq hlabels
    cases hlabelsEq
    obtain ⟨k, hk⟩ := compileCheck_enforce_labels_form
      (scope := .main) (hsrc := hcompiled.main_hsrc) (Δ := []) (P := P) (n := 0)
      (exprPath := exprPath₁) (e' := e₁) (c := c₁) (labels := labels₁) hnode₁'
    have hp : p₁ = p₂ := by
      apply (mkBoundaryLabels_at_site_eq_iff_path_eq
        (scope := .main) (pol := .positive) (c := compileBoundaryTarget c₁) (n := k)).1
      simpa [hk] using hsite
    cases hp
    rfl
  case mainEnforce.mainDynAttr.refl =>
    rename_i exprPathE c p exprPathD
    rcases horig₁ with ⟨eE, labels, hnodeE, rfl⟩
    rcases horig₂ with ⟨eD, attr, hnodeD⟩
    have hnodeE' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPathE =
          some (.enforce eE c labels) := by
      simpa [hcompiled.main_eq] using hnodeE
    have hnodeD' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPathD =
          some (.dynAttrAccess eD attr ℓ₂) := by
      simpa [hcompiled.main_eq] using hnodeD
    exfalso
    exact compileCheck_cross_kind_site_disjoint
      (scope := .main) (hsrc := hcompiled.main_hsrc) (Δ := []) (P := P) (n := 0)
      (exprPathE := exprPathE) (exprPathD := exprPathD)
      (eE := eE) (c := c) (labels := labels) (p := p)
      (eD := eD) (attr := attr) (ℓ := ℓ₂)
      hnodeE' hnodeD' hsite
  case mainDynAttr.mainEnforce.refl =>
    rename_i exprPathD exprPathE c p
    rcases horig₁ with ⟨eD, attr, hnodeD⟩
    rcases horig₂ with ⟨eE, labels, hnodeE, rfl⟩
    have hnodeD' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPathD =
          some (.dynAttrAccess eD attr ℓ₁) := by
      simpa [hcompiled.main_eq] using hnodeD
    have hnodeE' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPathE =
          some (.enforce eE c labels) := by
      simpa [hcompiled.main_eq] using hnodeE
    exfalso
    exact compileCheck_cross_kind_site_disjoint
      (scope := .main) (hsrc := hcompiled.main_hsrc) (Δ := []) (P := P) (n := 0)
      (exprPathE := exprPathE) (exprPathD := exprPathD)
      (eE := eE) (c := c) (labels := labels) (p := p)
      (eD := eD) (attr := attr) (ℓ := ℓ₁)
      hnodeE' hnodeD' hsite.symm
  case mainDynAttr.mainDynAttr.refl =>
    rename_i exprPath₁ exprPath₂
    rcases horig₁ with ⟨e₁, attr₁, hnode₁⟩
    rcases horig₂ with ⟨e₂, attr₂, hnode₂⟩
    have hnode₁' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPath₁ =
          some (.dynAttrAccess e₁ attr₁ ℓ₁) := by
      simpa [hcompiled.main_eq] using hnode₁
    have hnode₂' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPath₂ =
          some (.dynAttrAccess e₂ attr₂ ℓ₂) := by
      simpa [hcompiled.main_eq] using hnode₂
    obtain ⟨hpath, _, _, _⟩ := compileCheck_dynAttr_site_unique
      (scope := .main) (hsrc := hcompiled.main_hsrc) (Δ := []) (P := P) (n := 0)
      (exprPath₁ := exprPath₁) (exprPath₂ := exprPath₂)
      (e₁ := e₁) (e₂ := e₂) (attr₁ := attr₁) (attr₂ := attr₂)
      (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
      hnode₁' hnode₂' hsite
    cases hpath
    rfl
  case methodParameter.methodParameter.refl =>
    rename_i definerName methodName c₁ p₁ c₂ p₂
    rcases horig₁ with ⟨cc₁, gm₁, cm₁, hfc₁, hmem₁, hcm₁, hc₁, hname₁, hlabel₁⟩
    rcases horig₂ with ⟨cc₂, gm₂, cm₂, hfc₂, hmem₂, hcm₂, hc₂, hname₂, hlabel₂⟩
    cases (findCheckedClass_functional hfc₁ hfc₂ : cc₁ = cc₂)
    cases (compiledMethod_named_unique hwfct hcompiled hfc₁ hmem₁ hmem₂ hcm₁ hcm₂
      (hname₁.trans hname₂.symm) : cm₁ = cm₂)
    cases hc₁
    cases hc₂
    have hsite' : (cm₁.parameterLabels.at p₁).site = (cm₁.parameterLabels.at p₂).site := by
      simpa [hlabel₁, hlabel₂] using hsite
    have hcontract : cm₁.parameterContract = compileBoundaryRaw gm₁.paramTy := by
      simpa [hcm₁.paramTy_eq] using hcm₁.paramContract_eq
    have hlabelsEq :
        cast (congrArg BoundaryLabels hcontract) cm₁.parameterLabels =
          (mkBoundaryLabels (.methodParameter definerName methodName) .negative
            (compileBoundaryRaw gm₁.paramTy) 0).1 := by
      simpa [hcontract, hname₁] using hcm₁.parameterLabels_eq
    have hsite'' :
        (((mkBoundaryLabels (.methodParameter definerName methodName) .negative
            (compileBoundaryRaw gm₁.paramTy) 0).1).at
          (cast (congrArg BoundaryPath hcontract) p₁)).site =
        (((mkBoundaryLabels (.methodParameter definerName methodName) .negative
            (compileBoundaryRaw gm₁.paramTy) 0).1).at
          (cast (congrArg BoundaryPath hcontract) p₂)).site := by
      rw [← hlabelsEq]
      have h₁ := congrArg Label.site
        (BoundaryLabels.at_cast hcontract cm₁.parameterLabels p₁)
      have h₂ := congrArg Label.site
        (BoundaryLabels.at_cast hcontract cm₁.parameterLabels p₂)
      simpa using h₁.trans (hsite'.trans h₂.symm)
    have hpCast :
        cast (congrArg BoundaryPath hcontract) p₁ =
          cast (congrArg BoundaryPath hcontract) p₂ :=
      (mkBoundaryLabels_at_site_eq_iff_path_eq
        (scope := .methodParameter definerName methodName) (pol := .negative)
        (c := compileBoundaryRaw gm₁.paramTy) (n := 0)).1 hsite''
    have hp : p₁ = p₂ := BoundaryPath.cast_injective hcontract hpCast
    cases hp
    rfl
  case methodReturn.methodReturn.refl =>
    rename_i definerName methodName c₁ p₁ c₂ p₂
    rcases horig₁ with ⟨cc₁, gm₁, cm₁, hfc₁, hmem₁, hcm₁, hc₁, hname₁, hlabel₁⟩
    rcases horig₂ with ⟨cc₂, gm₂, cm₂, hfc₂, hmem₂, hcm₂, hc₂, hname₂, hlabel₂⟩
    cases (findCheckedClass_functional hfc₁ hfc₂ : cc₁ = cc₂)
    cases (compiledMethod_named_unique hwfct hcompiled hfc₁ hmem₁ hmem₂ hcm₁ hcm₂
      (hname₁.trans hname₂.symm) : cm₁ = cm₂)
    cases hc₁
    cases hc₂
    have hsite' : (cm₁.returnLabels.at p₁).site = (cm₁.returnLabels.at p₂).site := by
      simpa [hlabel₁, hlabel₂] using hsite
    have hcontract : cm₁.returnContract = compileBoundaryRaw gm₁.returnTy := by
      simpa [hcm₁.returnTy_eq] using hcm₁.returnContract_eq
    have hlabelsEq :
        cast (congrArg BoundaryLabels hcontract) cm₁.returnLabels =
          (mkBoundaryLabels (.methodReturn definerName methodName) .positive
            (compileBoundaryRaw gm₁.returnTy) 0).1 := by
      simpa [hcontract, hname₁] using hcm₁.returnLabels_eq
    have hsite'' :
        (((mkBoundaryLabels (.methodReturn definerName methodName) .positive
            (compileBoundaryRaw gm₁.returnTy) 0).1).at
          (cast (congrArg BoundaryPath hcontract) p₁)).site =
        (((mkBoundaryLabels (.methodReturn definerName methodName) .positive
            (compileBoundaryRaw gm₁.returnTy) 0).1).at
          (cast (congrArg BoundaryPath hcontract) p₂)).site := by
      rw [← hlabelsEq]
      have h₁ := congrArg Label.site
        (BoundaryLabels.at_cast hcontract cm₁.returnLabels p₁)
      have h₂ := congrArg Label.site
        (BoundaryLabels.at_cast hcontract cm₁.returnLabels p₂)
      simpa using h₁.trans (hsite'.trans h₂.symm)
    have hpCast :
        cast (congrArg BoundaryPath hcontract) p₁ =
          cast (congrArg BoundaryPath hcontract) p₂ :=
      (mkBoundaryLabels_at_site_eq_iff_path_eq
        (scope := .methodReturn definerName methodName) (pol := .positive)
        (c := compileBoundaryRaw gm₁.returnTy) (n := 0)).1 hsite''
    have hp : p₁ = p₂ := BoundaryPath.cast_injective hcontract hpCast
    cases hp
    rfl
  case methodBodyEnforce.methodBodyEnforce.refl =>
    rename_i definerName methodName exprPath₁ c₁ p₁ exprPath₂ c₂ p₂
    rcases horig₁ with ⟨cc₁, gm₁, cm₁, e₁, labels₁, hfc₁, hmem₁, hcm₁, hname₁, hnode₁, rfl⟩
    rcases horig₂ with ⟨cc₂, gm₂, cm₂, e₂, labels₂, hfc₂, hmem₂, hcm₂, hname₂, hnode₂, rfl⟩
    cases (findCheckedClass_functional hfc₁ hfc₂ : cc₁ = cc₂)
    cases (compiledMethod_named_unique hwfct hcompiled hfc₁ hmem₁ hmem₂ hcm₁ hcm₂
      (hname₁.trans hname₂.symm) : cm₁ = cm₂)
    obtain ⟨_, gm, _, hgmMem, htrace⟩ := traceMethodToSource hcompiled.classes_elab hfc₁ hmem₂
    have htraceName : gm.name = methodName :=
      htrace.name_eq.symm.trans (hcm₁.name_eq.trans hname₁)
    obtain ⟨_, _, hsrc, hbody⟩ := htrace.body_compiled
    have hnode₁' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPath₁ =
          some (.enforce e₁ c₁ labels₁) := by
      simpa [hbody, htraceName] using hnode₁
    have hnode₂' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPath₂ =
          some (.enforce e₂ c₂ labels₂) := by
      simpa [hbody, htraceName] using hnode₂
    obtain ⟨hpath, hlabels, hc⟩ := compileCheck_enforce_site_unique
      (scope := .methodBody definerName methodName) (hsrc := hsrc)
      (Δ := [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)])
      (P := gm.returnTy) (n := 0)
      (exprPath₁ := exprPath₁) (exprPath₂ := exprPath₂)
      (e₁ := e₁) (e₂ := e₂) (c₁ := c₁) (c₂ := c₂)
      (labels₁ := labels₁) (labels₂ := labels₂) (p₁ := p₁) (p₂ := p₂)
      hnode₁' hnode₂' hsite
    cases hpath
    cases hc
    have hlabelsEq : labels₁ = labels₂ := eq_of_heq hlabels
    cases hlabelsEq
    obtain ⟨k, hk⟩ := compileCheck_enforce_labels_form
      (scope := .methodBody definerName methodName) (hsrc := hsrc)
      (Δ := [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)])
      (P := gm.returnTy) (n := 0)
      (exprPath := exprPath₁) (e' := e₁) (c := c₁) (labels := labels₁) hnode₁'
    have hp : p₁ = p₂ := by
      apply (mkBoundaryLabels_at_site_eq_iff_path_eq
        (scope := .methodBody definerName methodName)
        (pol := .positive) (c := compileBoundaryTarget c₁) (n := k)).1
      simpa [hk] using hsite
    cases hp
    rfl
  case methodBodyEnforce.methodBodyDynAttr.refl =>
    rename_i definerName methodName exprPathE c p exprPathD
    rcases horig₁ with ⟨cc₁, gm₁, cm₁, eE, labels, hfc₁, hmem₁, hcm₁, hname₁, hnodeE, rfl⟩
    rcases horig₂ with ⟨cc₂, gm₂, cm₂, eD, attr, hfc₂, hmem₂, hcm₂, hname₂, hnodeD⟩
    cases (findCheckedClass_functional hfc₁ hfc₂ : cc₁ = cc₂)
    cases (compiledMethod_named_unique hwfct hcompiled hfc₁ hmem₁ hmem₂ hcm₁ hcm₂
      (hname₁.trans hname₂.symm) : cm₁ = cm₂)
    obtain ⟨_, gm, _, hgmMem, htrace⟩ := traceMethodToSource hcompiled.classes_elab hfc₁ hmem₂
    have htraceName : gm.name = methodName :=
      htrace.name_eq.symm.trans (hcm₁.name_eq.trans hname₁)
    obtain ⟨_, _, hsrc, hbody⟩ := htrace.body_compiled
    have hnodeE' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPathE =
          some (.enforce eE c labels) := by
      simpa [hbody, htraceName] using hnodeE
    have hnodeD' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPathD =
          some (.dynAttrAccess eD attr ℓ₂) := by
      simpa [hbody, htraceName] using hnodeD
    exfalso
    exact compileCheck_cross_kind_site_disjoint
      (scope := .methodBody definerName methodName) (hsrc := hsrc)
      (Δ := [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)])
      (P := gm.returnTy) (n := 0)
      (exprPathE := exprPathE) (exprPathD := exprPathD)
      (eE := eE) (c := c) (labels := labels) (p := p)
      (eD := eD) (attr := attr) (ℓ := ℓ₂)
      hnodeE' hnodeD' hsite
  case methodBodyDynAttr.methodBodyEnforce.refl =>
    rename_i definerName methodName exprPathD exprPathE c p
    rcases horig₁ with ⟨cc₁, gm₁, cm₁, eD, attr, hfc₁, hmem₁, hcm₁, hname₁, hnodeD⟩
    rcases horig₂ with ⟨cc₂, gm₂, cm₂, eE, labels, hfc₂, hmem₂, hcm₂, hname₂, hnodeE, rfl⟩
    cases (findCheckedClass_functional hfc₁ hfc₂ : cc₁ = cc₂)
    cases (compiledMethod_named_unique hwfct hcompiled hfc₁ hmem₁ hmem₂ hcm₁ hcm₂
      (hname₁.trans hname₂.symm) : cm₁ = cm₂)
    obtain ⟨_, gm, _, hgmMem, htrace⟩ := traceMethodToSource hcompiled.classes_elab hfc₁ hmem₂
    have htraceName : gm.name = methodName :=
      htrace.name_eq.symm.trans (hcm₁.name_eq.trans hname₁)
    obtain ⟨_, _, hsrc, hbody⟩ := htrace.body_compiled
    have hnodeD' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPathD =
          some (.dynAttrAccess eD attr ℓ₁) := by
      simpa [hbody, htraceName] using hnodeD
    have hnodeE' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPathE =
          some (.enforce eE c labels) := by
      simpa [hbody, htraceName] using hnodeE
    exfalso
    exact compileCheck_cross_kind_site_disjoint
      (scope := .methodBody definerName methodName) (hsrc := hsrc)
      (Δ := [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)])
      (P := gm.returnTy) (n := 0)
      (exprPathE := exprPathE) (exprPathD := exprPathD)
      (eE := eE) (c := c) (labels := labels) (p := p)
      (eD := eD) (attr := attr) (ℓ := ℓ₁)
      hnodeE' hnodeD' hsite.symm
  case methodBodyDynAttr.methodBodyDynAttr.refl =>
    rename_i definerName methodName exprPath₁ exprPath₂
    rcases horig₁ with ⟨cc₁, gm₁, cm₁, e₁, attr₁, hfc₁, hmem₁, hcm₁, hname₁, hnode₁⟩
    rcases horig₂ with ⟨cc₂, gm₂, cm₂, e₂, attr₂, hfc₂, hmem₂, hcm₂, hname₂, hnode₂⟩
    cases (findCheckedClass_functional hfc₁ hfc₂ : cc₁ = cc₂)
    cases (compiledMethod_named_unique hwfct hcompiled hfc₁ hmem₁ hmem₂ hcm₁ hcm₂
      (hname₁.trans hname₂.symm) : cm₁ = cm₂)
    obtain ⟨_, gm, _, hgmMem, htrace⟩ := traceMethodToSource hcompiled.classes_elab hfc₁ hmem₂
    have htraceName : gm.name = methodName :=
      htrace.name_eq.symm.trans (hcm₁.name_eq.trans hname₁)
    obtain ⟨_, _, hsrc, hbody⟩ := htrace.body_compiled
    have hnode₁' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPath₁ =
          some (.dynAttrAccess e₁ attr₁ ℓ₁) := by
      simpa [hbody, htraceName] using hnode₁
    have hnode₂' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPath₂ =
          some (.dynAttrAccess e₂ attr₂ ℓ₂) := by
      simpa [hbody, htraceName] using hnode₂
    obtain ⟨hpath, _, _, _⟩ := compileCheck_dynAttr_site_unique
      (scope := .methodBody definerName methodName) (hsrc := hsrc)
      (Δ := [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)])
      (P := gm.returnTy) (n := 0)
      (exprPath₁ := exprPath₁) (exprPath₂ := exprPath₂)
      (e₁ := e₁) (e₂ := e₂) (attr₁ := attr₁) (attr₂ := attr₂)
      (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
      hnode₁' hnode₂' hsite
    cases hpath
    rfl
  case mainEnforce.mainCallReturn.refl =>
    rename_i exprPathE c p exprPathC cC pC
    rcases horig₁ with ⟨eE, labelsE, hnodeE, rfl⟩
    rcases horig₂ with ⟨calleeC, argC, paramTyC, labelsC, hnodeC, hlabelC⟩
    have hnodeE' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPathE =
          some (.enforce eE c labelsE) := by
      simpa [hcompiled.main_eq] using hnodeE
    have hnodeC' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPathC =
          some (.call calleeC argC paramTyC cC labelsC) := by
      simpa [hcompiled.main_eq] using hnodeC
    have hsite' : (labelsE.at p).site = (labelsC.at pC).site := by
      simpa [hlabelC] using hsite
    exfalso
    exact compileCheck_enforce_callReturn_disjoint
      (scope := .main) (hsrc := hcompiled.main_hsrc) (Δ := []) (P := P) (n := 0)
      (exprPathE := exprPathE) (exprPathC := exprPathC)
      (eE := eE) (c := c) (labelsE := labelsE) (pE := p)
      (calleeC := calleeC) (argC := argC) (paramTyC := paramTyC)
      (returnTyC := cC) (labelsC := labelsC) (pC := pC)
      hnodeE' hnodeC' hsite'
  case mainCallReturn.mainEnforce.refl =>
    rename_i exprPathC cC pC exprPathE c p
    rcases horig₁ with ⟨calleeC, argC, paramTyC, labelsC, hnodeC, hlabelC⟩
    rcases horig₂ with ⟨eE, labelsE, hnodeE, rfl⟩
    have hnodeC' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPathC =
          some (.call calleeC argC paramTyC cC labelsC) := by
      simpa [hcompiled.main_eq] using hnodeC
    have hnodeE' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPathE =
          some (.enforce eE c labelsE) := by
      simpa [hcompiled.main_eq] using hnodeE
    have hsite' : (labelsE.at p).site = (labelsC.at pC).site := by
      simpa [hlabelC] using hsite.symm
    exfalso
    exact compileCheck_enforce_callReturn_disjoint
      (scope := .main) (hsrc := hcompiled.main_hsrc) (Δ := []) (P := P) (n := 0)
      (exprPathE := exprPathE) (exprPathC := exprPathC)
      (eE := eE) (c := c) (labelsE := labelsE) (pE := p)
      (calleeC := calleeC) (argC := argC) (paramTyC := paramTyC)
      (returnTyC := cC) (labelsC := labelsC) (pC := pC)
      hnodeE' hnodeC' hsite'
  case mainDynAttr.mainCallReturn.refl =>
    rename_i exprPathD exprPathC cC pC
    rcases horig₁ with ⟨eD, attrD, hnodeD⟩
    rcases horig₂ with ⟨calleeC, argC, paramTyC, labelsC, hnodeC, hlabelC⟩
    have hnodeD' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPathD =
          some (.dynAttrAccess eD attrD ℓ₁) := by
      simpa [hcompiled.main_eq] using hnodeD
    have hnodeC' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPathC =
          some (.call calleeC argC paramTyC cC labelsC) := by
      simpa [hcompiled.main_eq] using hnodeC
    have hsite' : ℓ₁.site = (labelsC.at pC).site := by
      simpa [hlabelC] using hsite
    exfalso
    exact compileCheck_dynAttr_callReturn_disjoint
      (scope := .main) (hsrc := hcompiled.main_hsrc) (Δ := []) (P := P) (n := 0)
      (exprPathD := exprPathD) (exprPathC := exprPathC)
      (eD := eD) (attr := attrD) (ℓD := ℓ₁)
      (calleeC := calleeC) (argC := argC) (paramTyC := paramTyC)
      (returnTyC := cC) (labelsC := labelsC) (pC := pC)
      hnodeD' hnodeC' hsite'
  case mainCallReturn.mainDynAttr.refl =>
    rename_i exprPathC cC pC exprPathD
    rcases horig₁ with ⟨calleeC, argC, paramTyC, labelsC, hnodeC, hlabelC⟩
    rcases horig₂ with ⟨eD, attrD, hnodeD⟩
    have hnodeC' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPathC =
          some (.call calleeC argC paramTyC cC labelsC) := by
      simpa [hcompiled.main_eq] using hnodeC
    have hnodeD' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPathD =
          some (.dynAttrAccess eD attrD ℓ₂) := by
      simpa [hcompiled.main_eq] using hnodeD
    have hsite' : ℓ₂.site = (labelsC.at pC).site := by
      simpa [hlabelC] using hsite.symm
    exfalso
    exact compileCheck_dynAttr_callReturn_disjoint
      (scope := .main) (hsrc := hcompiled.main_hsrc) (Δ := []) (P := P) (n := 0)
      (exprPathD := exprPathD) (exprPathC := exprPathC)
      (eD := eD) (attr := attrD) (ℓD := ℓ₂)
      (calleeC := calleeC) (argC := argC) (paramTyC := paramTyC)
      (returnTyC := cC) (labelsC := labelsC) (pC := pC)
      hnodeD' hnodeC' hsite'
  case mainCallReturn.mainCallReturn.refl =>
    rename_i exprPath₁ c₁ p₁ exprPath₂ c₂ p₂
    rcases horig₁ with ⟨callee₁, arg₁, paramTy₁, labels₁, hnode₁, hlabel₁⟩
    rcases horig₂ with ⟨callee₂, arg₂, paramTy₂, labels₂, hnode₂, hlabel₂⟩
    have hnode₁' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPath₁ =
          some (.call callee₁ arg₁ paramTy₁ c₁ labels₁) := by
      simpa [hcompiled.main_eq] using hnode₁
    have hnode₂' :
        (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPath₂ =
          some (.call callee₂ arg₂ paramTy₂ c₂ labels₂) := by
      simpa [hcompiled.main_eq] using hnode₂
    have hsite' : (labels₁.at p₁).site = (labels₂.at p₂).site := by
      simpa [hlabel₁, hlabel₂] using hsite
    obtain ⟨hpath, hlabels, hretTy⟩ := compileCheck_call_return_site_unique
      (scope := .main) (hsrc := hcompiled.main_hsrc) (Δ := []) (P := P) (n := 0)
      (exprPath₁ := exprPath₁) (exprPath₂ := exprPath₂)
      (callee₁ := callee₁) (arg₁ := arg₁) (paramTy₁ := paramTy₁)
      (returnTy₁ := c₁) (labels₁ := labels₁) (p₁ := p₁)
      (callee₂ := callee₂) (arg₂ := arg₂) (paramTy₂ := paramTy₂)
      (returnTy₂ := c₂) (labels₂ := labels₂) (p₂ := p₂)
      hnode₁' hnode₂' hsite'
    cases hpath
    cases hretTy
    have hlabelsEq : labels₁ = labels₂ := eq_of_heq hlabels
    cases hlabelsEq
    obtain ⟨k, hk⟩ := compileCheck_call_return_labels_form
      (scope := .main) (hsrc := hcompiled.main_hsrc) (Δ := []) (P := P) (n := 0)
      (exprPath := exprPath₁) (callee := callee₁) (arg := arg₁)
      (paramTy := paramTy₁) (returnTy := c₁) hnode₁'
    have hp : p₁ = p₂ := by
      apply (mkBoundaryLabels_at_site_eq_iff_path_eq
        (scope := .main) (pol := .positive)
        (c := compileBoundaryTarget c₁) (n := k)).1
      simpa [hk] using hsite'
    cases hp
    rfl
  case methodBodyEnforce.methodBodyCallReturn.refl =>
    rename_i definerName methodName exprPathE c p exprPathC cC pC
    rcases horig₁ with
      ⟨cc₁, gm₁, cm₁, eE, labelsE, hfc₁, hmem₁, hcm₁, hname₁, hnodeE, rfl⟩
    rcases horig₂ with
      ⟨cc₂, gm₂, cm₂, calleeC, argC, paramTyC, labelsC,
        hfc₂, hmem₂, hcm₂, hname₂, hnodeC, hlabelC⟩
    cases (findCheckedClass_functional hfc₁ hfc₂ : cc₁ = cc₂)
    cases (compiledMethod_named_unique hwfct hcompiled hfc₁ hmem₁ hmem₂ hcm₁ hcm₂
      (hname₁.trans hname₂.symm) : cm₁ = cm₂)
    obtain ⟨_, gm, _, hgmMem, htrace⟩ := traceMethodToSource hcompiled.classes_elab hfc₁ hmem₂
    have htraceName : gm.name = methodName :=
      htrace.name_eq.symm.trans (hcm₁.name_eq.trans hname₁)
    obtain ⟨_, _, hsrc, hbody⟩ := htrace.body_compiled
    have hnodeE' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPathE =
          some (.enforce eE c labelsE) := by
      simpa [hbody, htraceName] using hnodeE
    have hnodeC' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPathC =
          some (.call calleeC argC paramTyC cC labelsC) := by
      simpa [hbody, htraceName] using hnodeC
    have hsite' : (labelsE.at p).site = (labelsC.at pC).site := by
      simpa [hlabelC] using hsite
    exfalso
    exact compileCheck_enforce_callReturn_disjoint
      (scope := .methodBody definerName methodName) (hsrc := hsrc)
      (Δ := [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)])
      (P := gm.returnTy) (n := 0)
      (exprPathE := exprPathE) (exprPathC := exprPathC)
      (eE := eE) (c := c) (labelsE := labelsE) (pE := p)
      (calleeC := calleeC) (argC := argC) (paramTyC := paramTyC)
      (returnTyC := cC) (labelsC := labelsC) (pC := pC)
      hnodeE' hnodeC' hsite'
  case methodBodyCallReturn.methodBodyEnforce.refl =>
    rename_i definerName methodName exprPathC cC pC exprPathE c p
    rcases horig₁ with
      ⟨cc₁, gm₁, cm₁, calleeC, argC, paramTyC, labelsC,
        hfc₁, hmem₁, hcm₁, hname₁, hnodeC, hlabelC⟩
    rcases horig₂ with
      ⟨cc₂, gm₂, cm₂, eE, labelsE, hfc₂, hmem₂, hcm₂, hname₂, hnodeE, rfl⟩
    cases (findCheckedClass_functional hfc₁ hfc₂ : cc₁ = cc₂)
    cases (compiledMethod_named_unique hwfct hcompiled hfc₁ hmem₁ hmem₂ hcm₁ hcm₂
      (hname₁.trans hname₂.symm) : cm₁ = cm₂)
    obtain ⟨_, gm, _, hgmMem, htrace⟩ := traceMethodToSource hcompiled.classes_elab hfc₁ hmem₂
    have htraceName : gm.name = methodName :=
      htrace.name_eq.symm.trans (hcm₁.name_eq.trans hname₁)
    obtain ⟨_, _, hsrc, hbody⟩ := htrace.body_compiled
    have hnodeC' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPathC =
          some (.call calleeC argC paramTyC cC labelsC) := by
      simpa [hbody, htraceName] using hnodeC
    have hnodeE' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPathE =
          some (.enforce eE c labelsE) := by
      simpa [hbody, htraceName] using hnodeE
    have hsite' : (labelsE.at p).site = (labelsC.at pC).site := by
      simpa [hlabelC] using hsite.symm
    exfalso
    exact compileCheck_enforce_callReturn_disjoint
      (scope := .methodBody definerName methodName) (hsrc := hsrc)
      (Δ := [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)])
      (P := gm.returnTy) (n := 0)
      (exprPathE := exprPathE) (exprPathC := exprPathC)
      (eE := eE) (c := c) (labelsE := labelsE) (pE := p)
      (calleeC := calleeC) (argC := argC) (paramTyC := paramTyC)
      (returnTyC := cC) (labelsC := labelsC) (pC := pC)
      hnodeE' hnodeC' hsite'
  case methodBodyDynAttr.methodBodyCallReturn.refl =>
    rename_i definerName methodName exprPathD exprPathC cC pC
    rcases horig₁ with
      ⟨cc₁, gm₁, cm₁, eD, attrD, hfc₁, hmem₁, hcm₁, hname₁, hnodeD⟩
    rcases horig₂ with
      ⟨cc₂, gm₂, cm₂, calleeC, argC, paramTyC, labelsC,
        hfc₂, hmem₂, hcm₂, hname₂, hnodeC, hlabelC⟩
    cases (findCheckedClass_functional hfc₁ hfc₂ : cc₁ = cc₂)
    cases (compiledMethod_named_unique hwfct hcompiled hfc₁ hmem₁ hmem₂ hcm₁ hcm₂
      (hname₁.trans hname₂.symm) : cm₁ = cm₂)
    obtain ⟨_, gm, _, hgmMem, htrace⟩ := traceMethodToSource hcompiled.classes_elab hfc₁ hmem₂
    have htraceName : gm.name = methodName :=
      htrace.name_eq.symm.trans (hcm₁.name_eq.trans hname₁)
    obtain ⟨_, _, hsrc, hbody⟩ := htrace.body_compiled
    have hnodeD' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPathD =
          some (.dynAttrAccess eD attrD ℓ₁) := by
      simpa [hbody, htraceName] using hnodeD
    have hnodeC' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPathC =
          some (.call calleeC argC paramTyC cC labelsC) := by
      simpa [hbody, htraceName] using hnodeC
    have hsite' : ℓ₁.site = (labelsC.at pC).site := by
      simpa [hlabelC] using hsite
    exfalso
    exact compileCheck_dynAttr_callReturn_disjoint
      (scope := .methodBody definerName methodName) (hsrc := hsrc)
      (Δ := [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)])
      (P := gm.returnTy) (n := 0)
      (exprPathD := exprPathD) (exprPathC := exprPathC)
      (eD := eD) (attr := attrD) (ℓD := ℓ₁)
      (calleeC := calleeC) (argC := argC) (paramTyC := paramTyC)
      (returnTyC := cC) (labelsC := labelsC) (pC := pC)
      hnodeD' hnodeC' hsite'
  case methodBodyCallReturn.methodBodyDynAttr.refl =>
    rename_i definerName methodName exprPathC cC pC exprPathD
    rcases horig₁ with
      ⟨cc₁, gm₁, cm₁, calleeC, argC, paramTyC, labelsC,
        hfc₁, hmem₁, hcm₁, hname₁, hnodeC, hlabelC⟩
    rcases horig₂ with
      ⟨cc₂, gm₂, cm₂, eD, attrD, hfc₂, hmem₂, hcm₂, hname₂, hnodeD⟩
    cases (findCheckedClass_functional hfc₁ hfc₂ : cc₁ = cc₂)
    cases (compiledMethod_named_unique hwfct hcompiled hfc₁ hmem₁ hmem₂ hcm₁ hcm₂
      (hname₁.trans hname₂.symm) : cm₁ = cm₂)
    obtain ⟨_, gm, _, hgmMem, htrace⟩ := traceMethodToSource hcompiled.classes_elab hfc₁ hmem₂
    have htraceName : gm.name = methodName :=
      htrace.name_eq.symm.trans (hcm₁.name_eq.trans hname₁)
    obtain ⟨_, _, hsrc, hbody⟩ := htrace.body_compiled
    have hnodeC' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPathC =
          some (.call calleeC argC paramTyC cC labelsC) := by
      simpa [hbody, htraceName] using hnodeC
    have hnodeD' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPathD =
          some (.dynAttrAccess eD attrD ℓ₂) := by
      simpa [hbody, htraceName] using hnodeD
    have hsite' : ℓ₂.site = (labelsC.at pC).site := by
      simpa [hlabelC] using hsite.symm
    exfalso
    exact compileCheck_dynAttr_callReturn_disjoint
      (scope := .methodBody definerName methodName) (hsrc := hsrc)
      (Δ := [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)])
      (P := gm.returnTy) (n := 0)
      (exprPathD := exprPathD) (exprPathC := exprPathC)
      (eD := eD) (attr := attrD) (ℓD := ℓ₂)
      (calleeC := calleeC) (argC := argC) (paramTyC := paramTyC)
      (returnTyC := cC) (labelsC := labelsC) (pC := pC)
      hnodeD' hnodeC' hsite'
  case methodBodyCallReturn.methodBodyCallReturn.refl =>
    rename_i definerName methodName exprPath₁ c₁ p₁ exprPath₂ c₂ p₂
    rcases horig₁ with
      ⟨cc₁, gm₁, cm₁, callee₁, arg₁, paramTy₁, labels₁,
        hfc₁, hmem₁, hcm₁, hname₁, hnode₁, hlabel₁⟩
    rcases horig₂ with
      ⟨cc₂, gm₂, cm₂, callee₂, arg₂, paramTy₂, labels₂,
        hfc₂, hmem₂, hcm₂, hname₂, hnode₂, hlabel₂⟩
    cases (findCheckedClass_functional hfc₁ hfc₂ : cc₁ = cc₂)
    cases (compiledMethod_named_unique hwfct hcompiled hfc₁ hmem₁ hmem₂ hcm₁ hcm₂
      (hname₁.trans hname₂.symm) : cm₁ = cm₂)
    obtain ⟨_, gm, _, hgmMem, htrace⟩ := traceMethodToSource hcompiled.classes_elab hfc₁ hmem₂
    have htraceName : gm.name = methodName :=
      htrace.name_eq.symm.trans (hcm₁.name_eq.trans hname₁)
    obtain ⟨_, _, hsrc, hbody⟩ := htrace.body_compiled
    have hnode₁' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPath₁ =
          some (.call callee₁ arg₁ paramTy₁ c₁ labels₁) := by
      simpa [hbody, htraceName] using hnode₁
    have hnode₂' :
        (compileCheck (.methodBody definerName methodName) hsrc
          [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
          gm.returnTy 0).1.nodeAt exprPath₂ =
          some (.call callee₂ arg₂ paramTy₂ c₂ labels₂) := by
      simpa [hbody, htraceName] using hnode₂
    have hsite' : (labels₁.at p₁).site = (labels₂.at p₂).site := by
      simpa [hlabel₁, hlabel₂] using hsite
    obtain ⟨hpath, hlabels, hretTy⟩ := compileCheck_call_return_site_unique
      (scope := .methodBody definerName methodName) (hsrc := hsrc)
      (Δ := [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)])
      (P := gm.returnTy) (n := 0)
      (exprPath₁ := exprPath₁) (exprPath₂ := exprPath₂)
      (callee₁ := callee₁) (arg₁ := arg₁) (paramTy₁ := paramTy₁)
      (returnTy₁ := c₁) (labels₁ := labels₁) (p₁ := p₁)
      (callee₂ := callee₂) (arg₂ := arg₂) (paramTy₂ := paramTy₂)
      (returnTy₂ := c₂) (labels₂ := labels₂) (p₂ := p₂)
      hnode₁' hnode₂' hsite'
    cases hpath
    cases hretTy
    have hlabelsEq : labels₁ = labels₂ := eq_of_heq hlabels
    cases hlabelsEq
    obtain ⟨k, hk⟩ := compileCheck_call_return_labels_form
      (scope := .methodBody definerName methodName) (hsrc := hsrc)
      (Δ := [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)])
      (P := gm.returnTy) (n := 0)
      (exprPath := exprPath₁) (callee := callee₁) (arg := arg₁)
      (paramTy := paramTy₁) (returnTy := c₁) hnode₁'
    have hp : p₁ = p₂ := by
      apply (mkBoundaryLabels_at_site_eq_iff_path_eq
        (scope := .methodBody definerName methodName) (pol := .positive)
        (c := compileBoundaryTarget c₁) (n := k)).1
      simpa [hk] using hsite'
    cases hp
    rfl

theorem compiled_boundary_origin_unique
    (hwfct : WellFormedGClassTableCore gp.classes)
    (hcompiled : ElaboratesProgramAt gp P cp)
    (horig₁ : CompiledBoundaryOrigin hcompiled origin₁ ℓ)
    (horig₂ : CompiledBoundaryOrigin hcompiled origin₂ ℓ) :
    origin₁ = origin₂ :=
  compiled_boundary_same_scope_same_site_same_origin hwfct hcompiled horig₁ horig₂ rfl rfl

theorem gradual_blame_provenance_at
    (hcompiled : ElaboratesProgramAt gp P cp)
    (hsteps : Checked.Steps gp.classes cp.classes (initialState cp) finalState)
    (hfinal : finalResult? finalState = some (heap', .blame ℓ)) :
    ∃ origin, CompiledBoundaryOrigin hcompiled origin ℓ := by
  have hreg :=
    steps_preserve_registered hcompiled (initialState_registered hcompiled) hsteps
  rcases hreg with ⟨_, _, hctrl, _⟩
  simp only [finalResult?] at hfinal
  split at hfinal
  · cases hfinal
  · obtain ⟨rfl, rfl⟩ := Option.some.inj hfinal
    simpa [CompiledBoundaryLabel] using hctrl
  · cases hfinal
  · cases hfinal

theorem gradual_blame_provenance_origin_unique_at
    (hwfct : WellFormedGClassTableCore gp.classes)
    (hcompiled : ElaboratesProgramAt gp P cp)
    (horig₁ : CompiledBoundaryOrigin hcompiled origin₁ ℓ)
    (horig₂ : CompiledBoundaryOrigin hcompiled origin₂ ℓ) :
    origin₁ = origin₂ :=
  compiled_boundary_origin_unique hwfct hcompiled horig₁ horig₂

end Checked
