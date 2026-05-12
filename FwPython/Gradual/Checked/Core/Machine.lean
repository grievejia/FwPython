import FwPython.Gradual.Checked.Core.Runtime

/-! # Checked Small-Step Continuation Machine -/

namespace Checked

/-- Current control: an expression being evaluated, a returned value,
    a blame signal, or a runtime error. -/
inductive Control : Type where
  | expr : CheckedExpr → Control
  | val : CheckedValue → Control
  | blame : Label → Control
  | runtimeError : String → Control
  deriving DecidableEq, Repr

/-- A continuation frame records one pending evaluation context element. -/
inductive Frame : Type where
  | attrAccess : Identifier → Frame
  | callCallee : CheckedExpr → (paramTy : CheckedTarget) → (returnTy : CheckedTarget) →
      BoundaryLabels (compileBoundaryTarget returnTy) → Frame
  | callValue : CheckedValue → (paramTy : CheckedTarget) → (returnTy : CheckedTarget) →
      BoundaryLabels (compileBoundaryTarget returnTy) → Frame
  | awaitArgument : Nat → CheckedMethod → (returnTy : CheckedTarget) →
      BoundaryLabels (compileBoundaryTarget returnTy) → Frame
  | cond : CheckedExpr → CheckedExpr → Frame
  | returnTo : CheckedEnv → Frame
  | enforce : (target : CheckedTarget) → BoundaryLabels (compileBoundaryTarget target) → Frame
  | dynAttrAccess : Identifier → Label → Frame
  deriving DecidableEq, Repr

theorem _root_.frame_callCallee_inversion
    {arg₁ arg₂ : CheckedExpr}
    {paramTy₁ paramTy₂ returnTy₁ returnTy₂ : CheckedTarget}
    {returnLabels₁ : BoundaryLabels (compileBoundaryTarget returnTy₁)}
    {returnLabels₂ : BoundaryLabels (compileBoundaryTarget returnTy₂)}
    (h :
      Checked.Frame.callCallee arg₁ paramTy₁ returnTy₁ returnLabels₁ =
        Checked.Frame.callCallee arg₂ paramTy₂ returnTy₂ returnLabels₂) :
    ∃ hret : returnTy₁ = returnTy₂,
      arg₁ = arg₂ ∧
      paramTy₁ = paramTy₂ ∧
      hret ▸ returnLabels₁ = returnLabels₂ := by
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem _root_.frame_callValue_inversion
    {arg₁ arg₂ : CheckedValue}
    {paramTy₁ paramTy₂ returnTy₁ returnTy₂ : CheckedTarget}
    {returnLabels₁ : BoundaryLabels (compileBoundaryTarget returnTy₁)}
    {returnLabels₂ : BoundaryLabels (compileBoundaryTarget returnTy₂)}
    (h :
      Checked.Frame.callValue arg₁ paramTy₁ returnTy₁ returnLabels₁ =
        Checked.Frame.callValue arg₂ paramTy₂ returnTy₂ returnLabels₂) :
    ∃ hret : returnTy₁ = returnTy₂,
      arg₁ = arg₂ ∧
      paramTy₁ = paramTy₂ ∧
      hret ▸ returnLabels₁ = returnLabels₂ := by
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem _root_.frame_awaitArgument_inversion
    {recvOid₁ recvOid₂ : Nat}
    {m₁ m₂ : CheckedMethod}
    {returnTy₁ returnTy₂ : CheckedTarget}
    {returnLabels₁ : BoundaryLabels (compileBoundaryTarget returnTy₁)}
    {returnLabels₂ : BoundaryLabels (compileBoundaryTarget returnTy₂)}
    (h :
      Checked.Frame.awaitArgument recvOid₁ m₁ returnTy₁ returnLabels₁ =
        Checked.Frame.awaitArgument recvOid₂ m₂ returnTy₂ returnLabels₂) :
    ∃ hret : returnTy₁ = returnTy₂,
      recvOid₁ = recvOid₂ ∧
      m₁ = m₂ ∧
      hret ▸ returnLabels₁ = returnLabels₂ := by
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A continuation is a stack of frames. -/
abbrev Continuation := List Frame

/-- Machine state: heap, environment, control, and continuation. -/
structure State where
  heap : CheckedHeap
  env : CheckedEnv
  control : Control
  continuation : Continuation
  deriving Repr

/-- Create an expression state. -/
def expressionState (heap : CheckedHeap) (env : CheckedEnv) (expr : CheckedExpr) : State :=
  { heap, env, control := .expr expr, continuation := [] }

/-- Create an initial state for a checked program. -/
def initialState (program : CheckedProgram) : State :=
  expressionState CheckedHeap.initial [] program.main

/-- Extract the final result from a terminal state. -/
def finalResult? : State → Option (CheckedHeap × CheckedResult)
  | { heap, control := .val v, continuation := [], .. } => some (heap, .success v)
  | { heap, control := .blame ℓ, continuation := [], .. } => some (heap, .blame ℓ)
  | { heap, control := .runtimeError err, continuation := [], .. } =>
    some (heap, .runtimeError err)
  | _ => none

/-! ## One-Step Reduction -/

/-- One-step reduction for the checked continuation machine.
    Uses `GClassTable` for class lookup and MRO (shared with the gradual
    source layer), `CheckedClassTable` for method body lookup, and
    `CheckedExpr`/`CheckedValue` for the checked target. -/
inductive Step (ct : GClassTable) (cct : CheckedClassTable) : State → State → Prop where

  -- Expression focus rules

  | focusAttrAccess :
      Step ct cct
        { heap, env, control := .expr (.attrAccess base attrName), continuation := k }
        { heap, env, control := .expr base, continuation := .attrAccess attrName :: k }

  | focusCall :
      Step ct cct
        { heap, env,
          control := .expr (.call callee arg paramTy returnTy returnLabels),
          continuation := k }
        { heap, env, control := .expr callee,
          continuation := .callCallee arg paramTy returnTy returnLabels :: k }

  | focusCond :
      (∀ x C, condExpr ≠ .isInstance x C) →
      Step ct cct
        { heap, env, control := .expr (.cond condExpr thenBr elseBr), continuation := k }
        { heap, env, control := .expr condExpr, continuation := .cond thenBr elseBr :: k }

  | condIsInstanceTrue :
      env.lookup x = some (.objRef objOid) →
      heap.lookup objOid = some obj →
      findGClass ct obj.className = some c →
      GComputeMro ct c mro →
      C ∈ mro →
      Step ct cct
        { heap, env, control := .expr (.cond (.isInstance x C) thenBr elseBr), continuation := k }
        { heap, env, control := .expr thenBr, continuation := .returnTo env :: k }

  | condIsInstanceFalse :
      env.lookup x = some (.objRef objOid) →
      heap.lookup objOid = some obj →
      findGClass ct obj.className = some c →
      GComputeMro ct c mro →
      C ∉ mro →
      Step ct cct
        { heap, env, control := .expr (.cond (.isInstance x C) thenBr elseBr), continuation := k }
        { heap, env, control := .expr elseBr, continuation := .returnTo env :: k }

  | condIsInstanceVarNotFound :
      env.lookup x = none →
      Step ct cct
        { heap, env, control := .expr (.cond (.isInstance x C) thenBr elseBr), continuation := k }
        { heap, env, control := .runtimeError ("Variable not found: " ++ x), continuation := k }

  | focusEnforce :
      Step ct cct
        { heap, env, control := .expr (.enforce e c labels), continuation := k }
        { heap, env, control := .expr e, continuation := .enforce c labels :: k }

  | focusDynAttrAccess :
      Step ct cct
        { heap, env, control := .expr (.dynAttrAccess base attrName ℓ), continuation := k }
        { heap, env, control := .expr base, continuation := .dynAttrAccess attrName ℓ :: k }

  -- Atomic evaluation

  | varSuccess :
      env.lookup x = some v →
      Step ct cct
        { heap, env, control := .expr (.var x), continuation := k }
        { heap, env, control := .val v, continuation := k }

  | varError :
      env.lookup x = none →
      Step ct cct
        { heap, env, control := .expr (.var x), continuation := k }
        { heap, env, control := .runtimeError ("Variable not found: " ++ x), continuation := k }

  | newSuccess :
      findGClass ct cname = some c →
      cname ≠ boolClass →
      cname ≠ noneClass →
      cname ≠ boundMethodClass →
      heap.alloc ⟨cname, .ordinary⟩ = (oid, heap') →
      Step ct cct
        { heap, env, control := .expr (.new cname), continuation := k }
        { heap := heap', env, control := .val (.objRef oid), continuation := k }

  | newClassNotFound :
      findGClass ct cname = none →
      Step ct cct
        { heap, env, control := .expr (.new cname), continuation := k }
        { heap, env, control := .runtimeError ("Class not found: " ++ cname), continuation := k }

  | newBuiltinError :
      findGClass ct cname = some c →
      (cname = boolClass ∨ cname = noneClass ∨ cname = boundMethodClass) →
      Step ct cct
        { heap, env, control := .expr (.new cname), continuation := k }
        { heap, env, control := .runtimeError ("Cannot instantiate builtin class: " ++ cname),
          continuation := k }

  | constNone :
      Step ct cct
        { heap, env, control := .expr .constNone, continuation := k }
        { heap, env, control := .val (.objRef noneOid), continuation := k }

  | constTrue :
      Step ct cct
        { heap, env, control := .expr .constTrue, continuation := k }
        { heap, env, control := .val (.objRef trueOid), continuation := k }

  | constFalse :
      Step ct cct
        { heap, env, control := .expr .constFalse, continuation := k }
        { heap, env, control := .val (.objRef falseOid), continuation := k }

  | isInstanceTrue :
      env.lookup varName = some (.objRef objOid) →
      heap.lookup objOid = some obj →
      findGClass ct obj.className = some c →
      GComputeMro ct c mro →
      targetClass ∈ mro →
      Step ct cct
        { heap, env, control := .expr (.isInstance varName targetClass), continuation := k }
        { heap, env, control := .val (.objRef trueOid), continuation := k }

  | isInstanceFalse :
      env.lookup varName = some (.objRef objOid) →
      heap.lookup objOid = some obj →
      findGClass ct obj.className = some c →
      GComputeMro ct c mro →
      targetClass ∉ mro →
      Step ct cct
        { heap, env, control := .expr (.isInstance varName targetClass), continuation := k }
        { heap, env, control := .val (.objRef falseOid), continuation := k }

  | isInstanceVarNotFound :
      env.lookup varName = none →
      Step ct cct
        { heap, env, control := .expr (.isInstance varName targetClass), continuation := k }
        { heap, env, control := .runtimeError ("Variable not found: " ++ varName),
          continuation := k }

  -- Return rules: attribute access

  | returnAttrAccess :
      heap.lookup objOid = some obj →
      findGClass ct obj.className = some c →
      GComputeMro ct c mro →
      findCheckedMethodInMro cct mro attrName = some cm →
      heap.alloc ⟨boundMethodClass, .boundMethod objOid cm⟩ = (bmOid, heap') →
      Step ct cct
        { heap, env, control := .val (.objRef objOid),
          continuation := .attrAccess attrName :: k }
        { heap := heap', env, control := .val (.objRef bmOid), continuation := k }

  | returnAttrAccessNotFound :
      heap.lookup objOid = some obj →
      findGClass ct obj.className = some c →
      GComputeMro ct c mro →
      findCheckedMethodInMro cct mro attrName = none →
      Step ct cct
        { heap, env, control := .val (.objRef objOid),
          continuation := .attrAccess attrName :: k }
        { heap, env, control := .runtimeError
            ("Attribute not found: " ++ attrName ++ " in class " ++ obj.className),
          continuation := k }

  -- Return rules: dynamic attribute access (blame on missing, not runtimeError)

  | returnDynAttrAccess :
      heap.lookup objOid = some obj →
      findGClass ct obj.className = some c →
      GComputeMro ct c mro →
      findCheckedMethodInMro cct mro attrName = some cm →
      heap.alloc ⟨boundMethodClass, .boundMethod objOid cm⟩ = (bmOid, heap') →
      Step ct cct
        { heap, env, control := .val (.objRef objOid),
          continuation := .dynAttrAccess attrName ℓ :: k }
        { heap := heap', env, control := .val (.objRef bmOid), continuation := k }

  | returnDynAttrAccessNotFound :
      heap.lookup objOid = some obj →
      findGClass ct obj.className = some c →
      GComputeMro ct c mro →
      findCheckedMethodInMro cct mro attrName = none →
      Step ct cct
        { heap, env, control := .val (.objRef objOid),
          continuation := .dynAttrAccess attrName ℓ :: k }
        { heap, env, control := .blame ℓ, continuation := k }

  -- Return rules: call callee evaluation

  | returnCallCalleeBound :
      heap.lookup calleeOid = some ⟨boundMethodClass, .boundMethod recvOid m⟩ →
      Step ct cct
        { heap, env, control := .val (.objRef calleeOid),
          continuation := .callCallee arg paramTy returnTy returnLabels :: k }
        { heap, env, control := .expr arg,
          continuation := .awaitArgument recvOid m returnTy returnLabels :: k }

  | returnCallCalleeNotCallable :
      heap.lookup calleeOid = some ⟨_, .ordinary⟩ →
      Step ct cct
        { heap, env, control := .val (.objRef calleeOid),
          continuation := .callCallee arg paramTy returnTy returnLabels :: k }
        { heap, env, control := .runtimeError "Cannot call non-invokable value",
          continuation := k }

  -- Return rules: argument evaluation (bare bound method)
  -- Execution order: (1) enforce arg against m.parameterContract,
  -- (2) execute body, (3) enforce result against m.returnContract.

  | returnAwaitArgumentOk :
      EnforceValue ct heap argVal (compileBoundaryTarget m.paramTy) m.parameterLabels (.ok argVal') →
      Step ct cct
        { heap, env, control := .val argVal,
          continuation := .awaitArgument recvOid m returnTy returnLabels :: k }
        { heap,
          env := [(m.param, argVal'), (m.receiverParam, .objRef recvOid)],
          control := .expr m.body,
          continuation :=
            .enforce m.returnTy m.returnLabels ::
              .enforce returnTy returnLabels ::
              .returnTo env :: k }

  | returnAwaitArgumentBlame :
      EnforceValue ct heap argVal (compileBoundaryTarget m.paramTy) m.parameterLabels
        (.blame m.parameterLabels.direct) →
      Step ct cct
        { heap, env, control := .val argVal,
          continuation := .awaitArgument recvOid m returnTy returnLabels :: k }
        { heap, env, control := .blame m.parameterLabels.direct, continuation := k }

  -- Return rules: call with pre-evaluated argument
  -- Dispatches based on the callee value: bound method enters the bare-method
  -- path and ordinary object is an error.

  | returnCallValueBound :
      heap.lookup calleeOid = some ⟨boundMethodClass, .boundMethod recvOid m⟩ →
      Step ct cct
        { heap, env, control := .val (.objRef calleeOid),
          continuation := .callValue argVal paramTy returnTy returnLabels :: k }
        { heap, env, control := .val argVal,
          continuation := .awaitArgument recvOid m returnTy returnLabels :: k }

  | returnCallValueNotCallable :
      heap.lookup calleeOid = some ⟨_, .ordinary⟩ →
      Step ct cct
        { heap, env, control := .val (.objRef calleeOid),
          continuation := .callValue argVal paramTy returnTy returnLabels :: k }
        { heap, env, control := .runtimeError "Cannot call non-invokable value",
          continuation := k }

  -- Return rules: conditionals

  | returnCondTrue :
      Step ct cct
        { heap, env, control := .val (.objRef trueOid),
          continuation := .cond thenBr elseBr :: k }
        { heap, env, control := .expr thenBr, continuation := k }

  | returnCondFalse :
      Step ct cct
        { heap, env, control := .val (.objRef falseOid),
          continuation := .cond thenBr elseBr :: k }
        { heap, env, control := .expr elseBr, continuation := k }

  | returnCondNotBool :
      condOid ≠ trueOid →
      condOid ≠ falseOid →
      Step ct cct
        { heap, env, control := .val (.objRef condOid),
          continuation := .cond thenBr elseBr :: k }
        { heap, env, control := .runtimeError "Condition must evaluate to TRUE or FALSE",
          continuation := k }

  -- Return rules: body return and enforce expression

  | returnFromBody :
      Step ct cct
        { heap, env, control := .val v, continuation := .returnTo callerEnv :: k }
        { heap, env := callerEnv, control := .val v, continuation := k }

  | returnEnforceOk :
      EnforceValue ct heap v (compileBoundaryTarget c) labels (.ok v') →
      Step ct cct
        { heap, env, control := .val v, continuation := .enforce c labels :: k }
        { heap, env, control := .val v', continuation := k }

  | returnEnforceBlame :
      EnforceValue ct heap v (compileBoundaryTarget c) labels (.blame labels.direct) →
      Step ct cct
        { heap, env, control := .val v, continuation := .enforce c labels :: k }
        { heap, env, control := .blame labels.direct, continuation := k }

  -- Blame propagation (unwinding frames)

  | blameUnwindAttrAccess :
      Step ct cct
        { heap, env, control := .blame ℓ, continuation := .attrAccess _ :: k }
        { heap, env, control := .blame ℓ, continuation := k }

  | blameUnwindCallCallee :
      Step ct cct
        { heap, env, control := .blame ℓ, continuation := .callCallee _ _ _ _ :: k }
        { heap, env, control := .blame ℓ, continuation := k }

  | blameUnwindAwaitArgument :
      Step ct cct
        { heap, env, control := .blame ℓ, continuation := .awaitArgument _ _ _ _ :: k }
        { heap, env, control := .blame ℓ, continuation := k }

  | blameUnwindCallValue :
      Step ct cct
        { heap, env, control := .blame ℓ, continuation := .callValue _ _ _ _ :: k }
        { heap, env, control := .blame ℓ, continuation := k }

  | blameUnwindCond :
      Step ct cct
        { heap, env, control := .blame ℓ, continuation := .cond _ _ :: k }
        { heap, env, control := .blame ℓ, continuation := k }

  | blameUnwindReturnTo :
      Step ct cct
        { heap, env, control := .blame ℓ, continuation := .returnTo callerEnv :: k }
        { heap, env := callerEnv, control := .blame ℓ, continuation := k }

  | blameUnwindEnforce :
      Step ct cct
        { heap, env, control := .blame ℓ, continuation := .enforce _ _ :: k }
        { heap, env, control := .blame ℓ, continuation := k }

  | blameUnwindDynAttrAccess :
      Step ct cct
        { heap, env, control := .blame ℓ, continuation := .dynAttrAccess _ _ :: k }
        { heap, env, control := .blame ℓ, continuation := k }

  -- Error propagation (unwinding frames)

  | errorUnwindAttrAccess :
      Step ct cct
        { heap, env, control := .runtimeError err, continuation := .attrAccess _ :: k }
        { heap, env, control := .runtimeError err, continuation := k }

  | errorUnwindCallCallee :
      Step ct cct
        { heap, env, control := .runtimeError err, continuation := .callCallee _ _ _ _ :: k }
        { heap, env, control := .runtimeError err, continuation := k }

  | errorUnwindAwaitArgument :
      Step ct cct
        { heap, env, control := .runtimeError err, continuation := .awaitArgument _ _ _ _ :: k }
        { heap, env, control := .runtimeError err, continuation := k }

  | errorUnwindCallValue :
      Step ct cct
        { heap, env, control := .runtimeError err, continuation := .callValue _ _ _ _ :: k }
        { heap, env, control := .runtimeError err, continuation := k }

  | errorUnwindCond :
      Step ct cct
        { heap, env, control := .runtimeError err, continuation := .cond _ _ :: k }
        { heap, env, control := .runtimeError err, continuation := k }

  | errorUnwindReturnTo :
      Step ct cct
        { heap, env, control := .runtimeError err, continuation := .returnTo callerEnv :: k }
        { heap, env := callerEnv, control := .runtimeError err, continuation := k }

  | errorUnwindEnforce :
      Step ct cct
        { heap, env, control := .runtimeError err, continuation := .enforce _ _ :: k }
        { heap, env, control := .runtimeError err, continuation := k }

  | errorUnwindDynAttrAccess :
      Step ct cct
        { heap, env, control := .runtimeError err, continuation := .dynAttrAccess _ _ :: k }
        { heap, env, control := .runtimeError err, continuation := k }

/-! ## Helper lemmas -/

theorem finalResult_none_of_nonempty_continuation
    {heap : CheckedHeap} {env : CheckedEnv} {ctrl : Control}
    {f : Frame} {k : Continuation} :
    finalResult? { heap, env, control := ctrl, continuation := f :: k } = none := by
  cases ctrl <;> simp [finalResult?]

theorem final_states_do_not_step
    (hfinal : finalResult? s = some r)
    (hstep : Checked.Step ct cct s s') : False := by
  cases hstep <;> simp [finalResult?] at hfinal

end Checked
