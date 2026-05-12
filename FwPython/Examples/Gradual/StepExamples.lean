import FwPython.Gradual.Checked.Determinism

/-! # Checked Step Regression Examples

Concrete derivations exercising representative step rules of the checked
small-step machine: focus rules, atomic evaluation, return rules for
attribute access, call dispatch, conditionals, enforcement, and blame
propagation. After the shallow-callable refactor, all callable values are
plain `objRef`s into bound-method heap objects — there is no wrapper layer
on top, so call dispatch goes directly through `awaitArgument`. -/

open Checked

variable {ct : GClassTable} {cct : CheckedClassTable} {heap heap' : CheckedHeap} {env : CheckedEnv}
variable {k : Checked.Continuation}

/-! ## Focus rules: peeling the outer constructor -/

/-- Attribute-access focus pushes an `attrAccess` frame and recurses on the base. -/
example :
    Step ct cct
      { heap, env, control := .expr (.attrAccess base attrName), continuation := k }
      { heap, env, control := .expr base,
        continuation := .attrAccess attrName :: k } :=
  .focusAttrAccess

/-- Call focus pushes a `callCallee` frame and recurses on the callee. -/
example :
    Step ct cct
      { heap, env,
        control := .expr (.call callee arg paramTy returnTy returnLabels),
        continuation := k }
      { heap, env, control := .expr callee,
        continuation := .callCallee arg paramTy returnTy returnLabels :: k } :=
  .focusCall

/-- Enforce focus pushes an `enforce` frame and recurses on the body. -/
example :
    Step ct cct
      { heap, env, control := .expr (.enforce e c labels), continuation := k }
      { heap, env, control := .expr e,
        continuation := .enforce c labels :: k } :=
  .focusEnforce

/-! ## Atomic evaluation -/

/-- Variable lookup succeeds with the bound value. -/
example
    (henv : env.lookup x = some v) :
    Step ct cct
      { heap, env, control := .expr (.var x), continuation := k }
      { heap, env, control := .val v, continuation := k } :=
  .varSuccess henv

/-- The constant `none` evaluates to the pre-allocated `noneOid`. -/
example :
    Step ct cct
      { heap, env, control := .expr .constNone, continuation := k }
      { heap, env, control := .val (.objRef noneOid), continuation := k } :=
  .constNone

/-- `isInstance` returns `true` when the variable's class MRO contains the target. -/
example
    (henv : env.lookup varName = some (.objRef objOid))
    (hlook : heap.lookup objOid = some obj)
    (hfind : findGClass ct obj.className = some c)
    (hmro : GComputeMro ct c mro)
    (hmem : targetClass ∈ mro) :
    Step ct cct
      { heap, env, control := .expr (.isInstance varName targetClass), continuation := k }
      { heap, env, control := .val (.objRef trueOid), continuation := k } :=
  .isInstanceTrue henv hlook hfind hmro hmem

/-! ## Attribute access dispatch -/

/-- Attribute access on an objRef allocates a bound-method object and returns
    its OID. -/
example
    (hlook : heap.lookup objOid = some obj)
    (hfind : findGClass ct obj.className = some c)
    (hmro : GComputeMro ct c mro)
    (hmethod : findCheckedMethodInMro cct mro attrName = some cm)
    (halloc : heap.alloc ⟨boundMethodClass, .boundMethod objOid cm⟩ =
      (bmOid, heap')) :
    Step ct cct
      { heap, env, control := .val (.objRef objOid),
        continuation := .attrAccess attrName :: k }
      { heap := heap', env, control := .val (.objRef bmOid), continuation := k } :=
  .returnAttrAccess hlook hfind hmro hmethod halloc

/-- Dynamic attribute access on a missing attribute blames its label. -/
example
    (hlook : heap.lookup objOid = some obj)
    (hfind : findGClass ct obj.className = some c)
    (hmro : GComputeMro ct c mro)
    (hmethod : findCheckedMethodInMro cct mro attrName = none) :
    Step ct cct
      { heap, env, control := .val (.objRef objOid),
        continuation := .dynAttrAccess attrName ℓ :: k }
      { heap, env, control := .blame ℓ, continuation := k } :=
  .returnDynAttrAccessNotFound hlook hfind hmro hmethod

/-! ## Call dispatch on a bound-method objRef -/

/-- The callee value, once a bound-method objRef, transitions to the argument
    expression with an `awaitArgument` frame carrying the resolved method. -/
example
    (hlook : heap.lookup calleeOid = some ⟨boundMethodClass, .boundMethod recvOid m⟩) :
    Step ct cct
      { heap, env, control := .val (.objRef calleeOid),
        continuation := .callCallee arg paramTy returnTy returnLabels :: k }
      { heap, env, control := .expr arg,
        continuation := .awaitArgument recvOid m returnTy returnLabels :: k } :=
  .returnCallCalleeBound hlook

/-- Calling an ordinary (non-bound-method) object yields a runtime error. -/
example
    (hlook : heap.lookup calleeOid = some ⟨cname, .ordinary⟩) :
    Step ct cct
      { heap, env, control := .val (.objRef calleeOid),
        continuation := .callCallee arg paramTy returnTy returnLabels :: k }
      { heap, env, control := .runtimeError "Cannot call non-invokable value",
        continuation := k } :=
  .returnCallCalleeNotCallable hlook

/-- Successful argument enforcement enters the method body with the receiver
    and parameter bound, stacking the return enforcements and the caller-env
    return frame. -/
example
    (henf : EnforceValue ct heap argVal m.parameterContract m.parameterLabels (.ok argVal')) :
    Step ct cct
      { heap, env, control := .val argVal,
        continuation := .awaitArgument recvOid m returnTy returnLabels :: k }
      { heap,
        env := [(m.param, argVal'), (m.receiverParam, .objRef recvOid)],
        control := .expr m.body,
        continuation :=
          .enforce m.returnTy m.returnLabels ::
            .enforce returnTy returnLabels ::
            .returnTo env :: k } :=
  .returnAwaitArgumentOk henf

/-! ## Conditionals -/

/-- A `true` condition selects the `then` branch. -/
example :
    Step ct cct
      { heap, env, control := .val (.objRef trueOid),
        continuation := .cond thenBr elseBr :: k }
      { heap, env, control := .expr thenBr, continuation := k } :=
  .returnCondTrue

/-- A non-bool condition produces a runtime error. -/
example
    (htrue : condOid ≠ trueOid)
    (hfalse : condOid ≠ falseOid) :
    Step ct cct
      { heap, env, control := .val (.objRef condOid),
        continuation := .cond thenBr elseBr :: k }
      { heap, env, control := .runtimeError "Condition must evaluate to TRUE or FALSE",
        continuation := k } :=
  .returnCondNotBool htrue hfalse

/-! ## Enforcement frames -/

/-- A successful enforcement on a value just unwraps the frame. -/
example
    (henf : EnforceValue ct heap v (compileBoundaryTarget c) labels (.ok v')) :
    Step ct cct
      { heap, env, control := .val v, continuation := .enforce c labels :: k }
      { heap, env, control := .val v', continuation := k } :=
  .returnEnforceOk henf

/-- A failing enforcement turns the value into a blame on the frame's direct label. -/
example
    (henf : EnforceValue ct heap v (compileBoundaryTarget c) labels (.blame labels.direct)) :
    Step ct cct
      { heap, env, control := .val v, continuation := .enforce c labels :: k }
      { heap, env, control := .blame labels.direct, continuation := k } :=
  .returnEnforceBlame henf

/-! ## Blame propagation -/

/-- Blame unwinds through an `attrAccess` frame unchanged. -/
example :
    Step ct cct
      { heap, env, control := .blame ℓ,
        continuation := .attrAccess attrName :: k }
      { heap, env, control := .blame ℓ, continuation := k } :=
  .blameUnwindAttrAccess

/-! ## Determinism still holds -/

example (h1 : Step ct cct s s₁) (h2 : Step ct cct s s₂) : s₁ = s₂ :=
  step_deterministic h1 h2
