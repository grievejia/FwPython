import FwPython.Static.Semantics.Core
import FwPython.Static.TypeSystem.MethodLookup
import FwPython.Static.TypeSystem.Context
import FwPython.Static.TypeSystem.Typing
import FwPython.Static.TypeSystem.Value.Typing
import FwPython.Static.TypeSystem.Invariants

/-! # Typed Continuations and Safe States

Proof-only judgments for typed machine states. No typing certificates
belong in the runtime semantics. -/

namespace SmallStep

/-- A control has type `T` under class table `ct`, heap `h`, and
    environment `Γ`. Only expressions and values get typing constructors;
    runtime errors are ruled out by the safety theorem. -/
inductive ControlHasType (ct : ClassTable) (h : Heap) (Γ : TyEnv) :
    Control → Ty → Prop where
  | expr :
      HasType ct Γ e T →
      ControlHasType ct h Γ (.expr e) T
  | val :
      ValueHasType ct h v T →
      ControlHasType ct h Γ (.val v) T

/-- A frame has a compatible input type and environment, and produces a
    compatible output type and environment. The threading encodes what
    each frame expects and what it delivers to the rest of the
    continuation.

    Parameters:
    - `ct` : class table
    - `h` : current heap
    - `inEnv` : the typing environment active when the frame's input arrives
    - `inTy` : the type of the value the frame consumes
    - `outEnv` : the typing environment active after the frame produces its result
    - `outTy` : the type of the value the frame produces -/
inductive FrameHasType (ct : ClassTable) (h : Heap) :
    TyEnv → Ty → TyEnv → Ty → Frame → Prop where
  /-- Attribute access frame: consumes a class-typed value, produces a
      callable-typed value (via method lookup). -/
  | attrAccess :
      FindMethodType ct cname attrName paramTy returnTy →
      IsSubtype ct (.callable paramTy returnTy) outTy →
      WellFormedTy ct outTy →
      FrameHasType ct h Γ (.class_ cname) Γ outTy (.attrAccess attrName)
  /-- Attribute access on union receiver. -/
  | attrAccessUnion :
      FindMethodType ct c1 attrName p1 r1 →
      FindMethodType ct c2 attrName p2 r2 →
      IsSubtype ct (.union (.callable p1 r1) (.callable p2 r2)) outTy →
      WellFormedTy ct outTy →
      FrameHasType ct h Γ (.union (.class_ c1) (.class_ c2)) Γ outTy (.attrAccess attrName)
  /-- Call-callee frame: consumes a callable value, eventually produces
      the return type. The argument expression must be well-typed. -/
  | callCallee :
      HasType ct Γ arg paramTy →
      IsSubtype ct returnTy outTy →
      WellFormedTy ct outTy →
      FrameHasType ct h Γ (.callable paramTy returnTy) Γ outTy (.callCallee arg)
  /-- Await-argument frame: consumes the argument value, produces the
      method body's return type. -/
  | awaitArgument :
      h.lookup recvOid = some recvObj →
      MethodInReceiverMro ct recvObj.className m →
      IsSubtype ct m.returnTy outTy →
      WellFormedTy ct outTy →
      FrameHasType ct h Γ m.paramTy Γ outTy (.awaitArgument recvOid m)
  /-- Conditional frame: consumes a boolean value, produces the result
      type of whichever branch is taken. -/
  | cond :
      HasType ct Γ thenBr R →
      HasType ct Γ elseBr R →
      IsSubtype ct R outTy →
      WellFormedTy ct outTy →
      FrameHasType ct h Γ (.class_ boolClass) Γ outTy (.cond thenBr elseBr)
  /-- Return-to frame: restores the caller environment without changing
      the type. -/
  | returnTo :
      EnvHasType ct h callerEnv callerΓ →
      FrameHasType ct h bodyΓ T callerΓ T (.returnTo callerEnv)
  /-- Intersection threading: if a frame can produce `outTy₁` from `inTy₁`
      and `outTy₂` from `inTy₂`, then it can produce `outTy₁ ∩ outTy₂` from
      `inTy₁ ∩ inTy₂`. This is sound because the runtime value has both
      types simultaneously. -/
  | interIntro :
      FrameHasType ct h Γ inTy₁ Γ' outTy₁ f →
      FrameHasType ct h Γ inTy₂ Γ' outTy₂ f →
      WellFormedTy ct inTy₁ →
      WellFormedTy ct inTy₂ →
      FrameHasType ct h Γ (.intersection inTy₁ inTy₂) Γ' (.intersection outTy₁ outTy₂) f
  /-- Output subsumption: if a frame produces `outTy` and `outTy <: outTy'`,
      then the frame produces `outTy'`. -/
  | sub :
      FrameHasType ct h Γ inTy Γ' outTy f →
      IsSubtype ct outTy outTy' →
      WellFormedTy ct outTy' →
      FrameHasType ct h Γ inTy Γ' outTy' f

/-- A continuation is well-typed when its frames thread types from top
    to bottom: the top frame consumes the current control's type and
    environment, produces the type/environment expected by the next
    frame, and so on until the outermost output matches the expected
    result type. -/
inductive ContinuationHasType (ct : ClassTable) (h : Heap) :
    TyEnv → Ty → TyEnv → Ty → Continuation → Prop where
  | nil :
      ContinuationHasType ct h Γ T Γ T []
  | cons :
      FrameHasType ct h inΓ inTy midΓ midTy f →
      ContinuationHasType ct h midΓ midTy outΓ outTy k →
      ContinuationHasType ct h inΓ inTy outΓ outTy (f :: k)

/-- A machine state is safe when:
    - the heap is well-formed
    - the current environment is well-typed
    - the current control has a type
    - the continuation threads that type to the expected output type -/
def StateSafe (ct : ClassTable) (heap : Heap) (env : Env)
    (ctrl : Control) (cont : Continuation) (expectedType : Ty) : Prop :=
  ∃ (Γ outΓ : TyEnv) (T : Ty),
    HeapWellFormed ct heap ∧
    EnvHasType ct heap env Γ ∧
    ControlHasType ct heap Γ ctrl T ∧
    ContinuationHasType ct heap Γ T outΓ expectedType cont

end SmallStep
