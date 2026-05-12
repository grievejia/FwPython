import FwPython.Common.Env
import FwPython.Common.Heap
import FwPython.Static.MRO.Lookup

/-! # Semantics of the Mini Object-Oriented Language -/

/-- Payload carried by a heap object. Ordinary objects have no extra data;
    bound-method objects capture a receiver OID and a method definition. -/
inductive ObjectPayload : Type where
  | ordinary
  | boundMethod : Nat → Method → ObjectPayload
  deriving DecidableEq, Repr

/-- A heap object carries a class name and a payload. -/
structure HeapObject where
  className : Identifier
  payload : ObjectPayload
  deriving DecidableEq, Repr

/-- A runtime value is an object reference. -/
inductive Value : Type where
  | objRef : Nat → Value
  deriving DecidableEq, Repr

/-- Evaluation can result in either a successful value or a runtime error. -/
inductive Result : Type where
  | success : Value → Result
  | runtimeError : String → Result
  deriving DecidableEq, Repr

/-- Variable environment: maps variable names to values. -/
abbrev Env := NamedEnv Value

/-- Object heap for the static machine. -/
abbrev Heap := RuntimeHeap HeapObject

namespace Heap

abbrev heapMap (self : Heap) := RuntimeHeap.heapMap self
abbrev heapCounter (self : Heap) := RuntimeHeap.heapCounter self
abbrev alloc (self : Heap) (obj : HeapObject) : Nat × Heap := RuntimeHeap.alloc self obj
abbrev lookup (self : Heap) (oid : Nat) : Option HeapObject := RuntimeHeap.lookup self oid
abbrev IdsBounded (self : Heap) : Prop := RuntimeHeap.IdsBounded self

/-- The initial heap with pre-allocated constant objects:
    - `NONE` (oid 0, class `NoneType`)
    - `TRUE` (oid 1, class `Bool`)
    - `FALSE` (oid 2, class `Bool`) -/
def initial : Heap where
  heapMap := [(noneOid, ⟨noneClass, .ordinary⟩),
              (trueOid, ⟨boolClass, .ordinary⟩),
              (falseOid, ⟨boolClass, .ordinary⟩)]
  heapCounter := 3

end Heap


/-! # Small-Step Continuation Machine

A small-step continuation machine for the FwPython language. The machine
uses explicit control and continuation frames to decompose evaluation
into atomic steps. -/

namespace SmallStep

/-- Current control: an expression being evaluated, a returned value,
    or a runtime error. -/
inductive Control : Type where
  | expr : Expr → Control
  | val : Value → Control
  | error : String → Control
  deriving DecidableEq, Repr

/-- A continuation frame records one pending evaluation context element
    together with any runtime data needed to resume. -/
inductive Frame : Type where
  | attrAccess : Identifier → Frame
  | callCallee : Expr → Frame
  | awaitArgument : Nat → Method → Frame
  | cond : Expr → Expr → Frame
  | returnTo : Env → Frame
  deriving DecidableEq, Repr

/-- A continuation is a stack of frames. -/
abbrev Continuation := List Frame

/-- Machine state: heap, environment, control, and continuation. -/
structure State where
  heap : Heap
  env : Env
  control : Control
  continuation : Continuation
  deriving Repr

/-- Create an expression state from heap, environment, and expression. -/
def expressionState (heap : Heap) (env : Env) (expr : Expr) : State :=
  { heap, env, control := .expr expr, continuation := [] }

/-- Create an initial state for a program. -/
def initialState (program : Program) : State :=
  expressionState Heap.initial [] program.main

/-- Extract the final result from a state, if it is final (empty continuation). -/
def finalResult? : State → Option (Heap × Result)
  | { heap, control := .val v, continuation := [], .. } => some (heap, .success v)
  | { heap, control := .error err, continuation := [], .. } => some (heap, .runtimeError err)
  | _ => none

/-! ## One-Step Reduction -/

/-- One-step reduction relation for the continuation machine. -/
inductive Step (ct : ClassTable) : State → State → Prop where

  /-- Focus on the base expression of attribute access. -/
  | focusAttrAccess :
      Step ct
        { heap, env, control := .expr (.attrAccess base attrName), continuation := k }
        { heap, env, control := .expr base, continuation := .attrAccess attrName :: k }

  | focusCall :
      Step ct
        { heap, env, control := .expr (.call callee arg), continuation := k }
        { heap, env, control := .expr callee, continuation := .callCallee arg :: k }

  | focusCond :
      (∀ x C, condExpr ≠ .isInstance x C) →
      Step ct
        { heap, env, control := .expr (.cond condExpr thenBr elseBr), continuation := k }
        { heap, env, control := .expr condExpr, continuation := .cond thenBr elseBr :: k }

  /-- Conditional with isInstance condition — true branch (direct step). -/
  | condIsInstanceTrue :
      env.lookup x = some (.objRef objOid) →
      heap.lookup objOid = some obj →
      findClass ct obj.className = some c →
      ComputeMro ct c mro →
      C ∈ mro →
      Step ct
        { heap, env, control := .expr (.cond (.isInstance x C) thenBr elseBr), continuation := k }
        { heap, env, control := .expr thenBr, continuation := k }

  /-- Conditional with isInstance condition — false branch (direct step). -/
  | condIsInstanceFalse :
      env.lookup x = some (.objRef objOid) →
      heap.lookup objOid = some obj →
      findClass ct obj.className = some c →
      ComputeMro ct c mro →
      C ∉ mro →
      Step ct
        { heap, env, control := .expr (.cond (.isInstance x C) thenBr elseBr), continuation := k }
        { heap, env, control := .expr elseBr, continuation := k }

  /-- Conditional with isInstance condition — variable not found. -/
  | condIsInstanceVarNotFound :
      env.lookup x = none →
      Step ct
        { heap, env, control := .expr (.cond (.isInstance x C) thenBr elseBr), continuation := k }
        { heap, env, control := .error ("Variable not found: " ++ x), continuation := k }

  /-- Variable lookup — success. -/
  | varSuccess :
      env.lookup x = some v →
      Step ct
        { heap, env, control := .expr (.var x), continuation := k }
        { heap, env, control := .val v, continuation := k }

  | varError :
      env.lookup x = none →
      Step ct
        { heap, env, control := .expr (.var x), continuation := k }
        { heap, env, control := .error ("Variable not found: " ++ x), continuation := k }

  | newSuccess :
      findClass ct cname = some c →
      cname ≠ boolClass →
      cname ≠ noneClass →
      cname ≠ boundMethodClass →
      heap.alloc ⟨cname, .ordinary⟩ = (oid, heap') →
      Step ct
        { heap, env, control := .expr (.new cname), continuation := k }
        { heap := heap', env, control := .val (.objRef oid), continuation := k }

  | newClassNotFound :
      findClass ct cname = none →
      Step ct
        { heap, env, control := .expr (.new cname), continuation := k }
        { heap, env, control := .error ("Class not found: " ++ cname), continuation := k }

  | newBuiltinError :
      findClass ct cname = some c →
      (cname = boolClass ∨ cname = noneClass ∨ cname = boundMethodClass) →
      Step ct
        { heap, env, control := .expr (.new cname), continuation := k }
        { heap, env, control := .error ("Cannot instantiate builtin class: " ++ cname),
          continuation := k }

  | constNone :
      Step ct
        { heap, env, control := .expr .constNone, continuation := k }
        { heap, env, control := .val (.objRef noneOid), continuation := k }

  | constTrue :
      Step ct
        { heap, env, control := .expr .constTrue, continuation := k }
        { heap, env, control := .val (.objRef trueOid), continuation := k }

  | constFalse :
      Step ct
        { heap, env, control := .expr .constFalse, continuation := k }
        { heap, env, control := .val (.objRef falseOid), continuation := k }

  | isInstanceTrue :
      env.lookup varName = some (.objRef objOid) →
      heap.lookup objOid = some obj →
      findClass ct obj.className = some c →
      ComputeMro ct c mro →
      targetClass ∈ mro →
      Step ct
        { heap, env, control := .expr (.isInstance varName targetClass), continuation := k }
        { heap, env, control := .val (.objRef trueOid), continuation := k }

  | isInstanceFalse :
      env.lookup varName = some (.objRef objOid) →
      heap.lookup objOid = some obj →
      findClass ct obj.className = some c →
      ComputeMro ct c mro →
      targetClass ∉ mro →
      Step ct
        { heap, env, control := .expr (.isInstance varName targetClass), continuation := k }
        { heap, env, control := .val (.objRef falseOid), continuation := k }

  | isInstanceVarNotFound :
      env.lookup varName = none →
      Step ct
        { heap, env, control := .expr (.isInstance varName targetClass), continuation := k }
        { heap, env, control := .error ("Variable not found: " ++ varName), continuation := k }

  /-- Attribute access: method found, allocate bound method. -/
  | returnAttrAccess :
      heap.lookup objOid = some obj →
      findClass ct obj.className = some c →
      ComputeMro ct c mro →
      findMethodInMro ct mro attrName = some m →
      heap.alloc ⟨boundMethodClass, .boundMethod objOid m⟩ = (bmOid, heap') →
      Step ct
        { heap, env, control := .val (.objRef objOid), continuation := .attrAccess attrName :: k }
        { heap := heap', env, control := .val (.objRef bmOid), continuation := k }

  | returnAttrAccessNotFound :
      heap.lookup objOid = some obj →
      findClass ct obj.className = some c →
      ComputeMro ct c mro →
      findMethodInMro ct mro attrName = none →
      Step ct
        { heap, env, control := .val (.objRef objOid), continuation := .attrAccess attrName :: k }
        { heap, env, control := .error ("Attribute not found: " ++ attrName ++ " in class " ++ obj.className),
          continuation := k }

  | returnCallCallee :
      heap.lookup calleeOid = some ⟨_, .boundMethod recvOid m⟩ →
      Step ct
        { heap, env, control := .val (.objRef calleeOid), continuation := .callCallee arg :: k }
        { heap, env, control := .expr arg, continuation := .awaitArgument recvOid m :: k }

  | returnCallNotInvokable :
      heap.lookup calleeOid = some ⟨_, .ordinary⟩ →
      Step ct
        { heap, env, control := .val (.objRef calleeOid), continuation := .callCallee arg :: k }
        { heap, env, control := .error "Cannot call non-invokable value", continuation := k }

  | returnAwaitArgument :
      Step ct
        { heap, env, control := .val argVal, continuation := .awaitArgument recvOid m :: k }
        { heap,
          env := [(m.param, argVal), (m.receiverParam, .objRef recvOid)],
          control := .expr m.body,
          continuation := .returnTo env :: k }

  | returnCondTrue :
      Step ct
        { heap, env, control := .val (.objRef trueOid), continuation := .cond thenBr elseBr :: k }
        { heap, env, control := .expr thenBr, continuation := k }

  | returnCondFalse :
      Step ct
        { heap, env, control := .val (.objRef falseOid), continuation := .cond thenBr elseBr :: k }
        { heap, env, control := .expr elseBr, continuation := k }

  | returnCondNotBool :
      condOid ≠ trueOid →
      condOid ≠ falseOid →
      Step ct
        { heap, env, control := .val (.objRef condOid), continuation := .cond thenBr elseBr :: k }
        { heap, env, control := .error "Condition must evaluate to TRUE or FALSE",
          continuation := k }

  | returnFromBody :
      Step ct
        { heap, env, control := .val v, continuation := .returnTo callerEnv :: k }
        { heap, env := callerEnv, control := .val v, continuation := k }

  /-- Error unwind: pop attrAccess frame. -/
  | errorUnwindAttrAccess :
      Step ct
        { heap, env, control := .error err, continuation := .attrAccess _ :: k }
        { heap, env, control := .error err, continuation := k }

  | errorUnwindCallCallee :
      Step ct
        { heap, env, control := .error err, continuation := .callCallee _ :: k }
        { heap, env, control := .error err, continuation := k }

  | errorUnwindAwaitArgument :
      Step ct
        { heap, env, control := .error err, continuation := .awaitArgument _ _ :: k }
        { heap, env, control := .error err, continuation := k }

  | errorUnwindCond :
      Step ct
        { heap, env, control := .error err, continuation := .cond _ _ :: k }
        { heap, env, control := .error err, continuation := k }

  | errorUnwindReturnTo :
      Step ct
        { heap, env, control := .error err, continuation := .returnTo callerEnv :: k }
        { heap, env := callerEnv, control := .error err, continuation := k }

/-! ## Helper lemmas -/

theorem finalResult_none_of_nonempty_continuation
    {heap : Heap} {env : Env} {ctrl : Control}
    {f : Frame} {k : Continuation} :
    finalResult? { heap, env, control := ctrl, continuation := f :: k } = none := by
  cases ctrl <;> simp [finalResult?]

theorem final_states_do_not_step
    (hfinal : finalResult? s = some r)
    (hstep : Step ct s s') : False := by
  cases hstep <;> simp [finalResult?] at hfinal

end SmallStep
