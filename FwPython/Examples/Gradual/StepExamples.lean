import FwPython.Gradual

/-! # Checked Step Regression Examples

Concrete derivations exercising representative step rules of the checked
small-step machine.
-/

open Checked

variable {ct : GClassTable} {cct : CheckedClassTable} {heap heap' : CheckedHeap} {env : CheckedEnv}
variable {k : Checked.Continuation}
variable {obligation returnObligation : SourceObligation}

/-! ## Focus rules -/

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
        control := .expr (.call callee arg paramTy returnTy returnObligation),
        continuation := k }
      { heap, env, control := .expr callee,
        continuation := .callCallee arg paramTy returnTy returnObligation :: k } :=
  .focusCall

/-- Enforce focus pushes an `enforce` frame and recurses on the body. -/
example :
    Step ct cct
      { heap, env, control := .expr (.enforce e c obligation), continuation := k }
      { heap, env, control := .expr e,
        continuation := .enforce c obligation :: k } :=
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

/-! ## Dynamic attribute access -/

/-- Dynamic attribute access on a missing attribute reports its stored obligation. -/
example
    (hlook : heap.lookup objOid = some obj)
    (hfind : findGClass ct obj.className = some c)
    (hmro : GComputeMro ct c mro)
    (hmethod : findCheckedMethodInMro cct mro attrName = none) :
    Step ct cct
      { heap, env, control := .val (.objRef objOid),
        continuation := .dynAttrAccess attrName obligation :: k }
      { heap, env,
        control := .blame
          { obligation := obligation,
            cause := .missingAttribute (.objRef objOid) attrName },
        continuation := k } :=
  .returnDynAttrAccessNotFound hlook hfind hmro hmethod

/-! ## Call dispatch on a bound-method objRef -/

/-- The callee value, once a bound-method objRef, transitions to argument evaluation. -/
example
    (hlook : heap.lookup calleeOid = some ⟨boundMethodClass, .boundMethod recvOid m⟩) :
    Step ct cct
      { heap, env, control := .val (.objRef calleeOid),
        continuation := .callCallee arg paramTy returnTy returnObligation :: k }
      { heap, env, control := .expr arg,
        continuation := .awaitArgument recvOid m returnTy returnObligation :: k } :=
  .returnCallCalleeBound hlook

/-- Successful argument enforcement enters the method body with distinct return obligations. -/
example
    (henf : EnforceValue ct heap argVal (compileBoundaryTarget m.paramTy) .ok) :
    Step ct cct
      { heap, env, control := .val argVal,
        continuation := .awaitArgument recvOid m returnTy returnObligation :: k }
      { heap,
        env := [(m.param, argVal), (m.receiverParam, .objRef recvOid)],
        control := .expr m.body,
        continuation :=
          .enforce m.returnTy m.returnObligation ::
            .enforce returnTy returnObligation ::
            .returnTo env :: k } :=
  .returnAwaitArgumentOk henf

/-- Failing method-parameter enforcement reports the resolved method's parameter obligation. -/
example
    (henf : EnforceValue ct heap argVal (compileBoundaryTarget m.paramTy) .blame) :
    Step ct cct
      { heap, env, control := .val argVal,
        continuation := .awaitArgument recvOid m returnTy returnObligation :: k }
      { heap, env,
        control := .blame
          { obligation := m.parameterObligation,
            cause := .methodParameter argVal m },
        continuation := k } :=
  .returnAwaitArgumentBlame henf

/-! ## Enforcement frames -/

/-- A successful enforcement returns the original value. -/
example
    (henf : EnforceValue ct heap v (compileBoundaryTarget c) .ok) :
    Step ct cct
      { heap, env, control := .val v, continuation := .enforce c obligation :: k }
      { heap, env, control := .val v, continuation := k } :=
  .returnEnforceOk henf

/-- A failing enforcement reports the enforce frame's obligation. -/
example
    (henf : EnforceValue ct heap v (compileBoundaryTarget c) .blame) :
    Step ct cct
      { heap, env, control := .val v, continuation := .enforce c obligation :: k }
      { heap, env,
        control := .blame
          { obligation := obligation,
            cause := .boundary v c },
        continuation := k } :=
  .returnEnforceBlame henf

/-! ## Blame propagation -/

/-- Blame unwinds through an `attrAccess` frame unchanged. -/
example
    (info : BlameInfo) :
    Step ct cct
      { heap, env, control := .blame info,
        continuation := .attrAccess attrName :: k }
      { heap, env, control := .blame info, continuation := k } :=
  .blameUnwindAttrAccess

/-- A raised blame payload is preserved until final-result extraction. -/
example
    (info : BlameInfo) :
    Checked.Steps ct cct
      { heap, env, control := .blame info,
        continuation := .attrAccess attrName :: [] }
      { heap, env, control := .blame info, continuation := [] } ∧
    Checked.finalResult?
      { heap, env, control := .blame info, continuation := [] } =
      some (heap, CheckedResult.blame info) :=
  ⟨.step .blameUnwindAttrAccess .refl, rfl⟩

/-! ## Determinism still holds -/

example (h1 : Step ct cct s s₁) (h2 : Step ct cct s s₂) : s₁ = s₂ :=
  step_deterministic h1 h2
