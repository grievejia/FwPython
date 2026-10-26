import FwPython.Static.Semantics.Core
import FwPython.Static.TypeSystem.MethodLookup
import FwPython.Static.TypeSystem.Context
import FwPython.Static.TypeSystem.Typing
import FwPython.Static.TypeSystem.Value.Typing
import FwPython.Static.TypeSystem.Invariants

/-! # Typed Continuations and Safe States

Proof-only judgments for typed machine states. No typing certificates
belong in the runtime semantics. -/

variable {ct : ClassTable} {structural : WellFormedClassHierarchy ct}

namespace SmallStep

/-- A control has type `T` under the supplied hierarchy, heap `h`, and
    environment `Γ`. Only expressions and values get typing constructors;
    runtime errors are ruled out by the safety theorem. -/
inductive ControlHasType {ct : ClassTable} (structural : WellFormedClassHierarchy ct) (h : Heap) (Γ : TyEnv) :
    Control → Ty → Prop where
  | expr :
      HasType structural Γ e T →
      ControlHasType structural h Γ (.expr e) T
  | val :
      ValueHasType structural h v T →
      ControlHasType structural h Γ (.val v) T

/-- A frame has a compatible input type and environment, and produces a
    compatible output type and environment. The threading encodes what
    each frame expects and what it delivers to the rest of the
    continuation.

    Parameters:
    - `structural` : the class table and computed MROs used by all typing and subtype premises
    - `h` : current heap
    - `inEnv` : the typing environment active when the frame's input arrives
    - `inTy` : the type of the value the frame consumes
    - `outEnv` : the typing environment active after the frame produces its result
    - `outTy` : the type of the value the frame produces -/
inductive FrameHasType (structural : WellFormedClassHierarchy ct) (h : Heap) :
    TyEnv → Ty → TyEnv → Ty → Frame → Prop where
  /-- Attribute access frame: consumes a class-typed value, produces a
      callable-typed value (via method lookup). -/
  | attrAccess :
      FindMethodType ct cname attrName paramTy returnTy →
      IsSubtype structural (.callable paramTy returnTy) outTy →
      FrameHasType structural h Γ (.class_ cname) Γ outTy (.attrAccess attrName)
  /-- Attribute access on union receiver. -/
  | attrAccessUnion :
      FindMethodType ct c1 attrName p1 r1 →
      FindMethodType ct c2 attrName p2 r2 →
      IsSubtype structural (.union (.callable p1 r1) (.callable p2 r2)) outTy →
      FrameHasType structural h Γ (.union (.class_ c1) (.class_ c2)) Γ outTy (.attrAccess attrName)
  /-- Call-callee frame: consumes a callable value, eventually produces
      the return type. The argument expression must be well-typed. -/
  | callCallee :
      HasType structural Γ arg paramTy →
      IsSubtype structural returnTy outTy →
      FrameHasType structural h Γ (.callable paramTy returnTy) Γ outTy (.callCallee arg)
  /-- The pending call consumes the input type required by its caller. The selected
      method's declared function type is below the caller's function type.
      When the argument returns, its typing proves that the required input is
      not below bottom, which permits result inversion. -/
  | awaitArgument :
      h.lookup recvOid = some recvObj →
      MethodInReceiverMro ct recvObj.className m →
      IsSubtype structural (.callable m.paramTy m.returnTy) (.callable requiredInput outTy) →
      FrameHasType structural h Γ requiredInput Γ outTy (.awaitArgument recvOid m)
  /-- Conditional frame: consumes a boolean value, produces the result
      type of whichever branch is taken. -/
  | cond :
      HasType structural Γ thenBr R →
      HasType structural Γ elseBr R →
      IsSubtype structural R outTy →
      FrameHasType structural h Γ (.class_ boolClass) Γ outTy (.cond thenBr elseBr)
  /-- Return-to frame: restores the caller environment without changing
      the type. -/
  | returnTo :
      EnvHasType structural h callerEnv callerΓ →
      FrameHasType structural h bodyΓ T callerΓ T (.returnTo callerEnv)
  /-- Intersection threading: if a frame can produce `outTy₁` from `inTy₁`
      and `outTy₂` from `inTy₂`, then it can produce `outTy₁ ∩ outTy₂` from
      `inTy₁ ∩ inTy₂`. This is sound because the runtime value has both
      types simultaneously. -/
  | interIntro :
      FrameHasType structural h Γ inTy₁ Γ' outTy₁ f →
      FrameHasType structural h Γ inTy₂ Γ' outTy₂ f →
      WellFormedTy ct inTy₁ →
      WellFormedTy ct inTy₂ →
      FrameHasType structural h Γ (.intersection inTy₁ inTy₂) Γ' (.intersection outTy₁ outTy₂) f
  /-- Output subsumption: if a frame produces `outTy` and `outTy <: outTy'`,
      then the frame produces `outTy'`. -/
  | sub :
      FrameHasType structural h Γ inTy Γ' outTy f →
      IsSubtype structural outTy outTy' →
      FrameHasType structural h Γ inTy Γ' outTy' f

/-- A continuation is well-typed when its frames thread types from top
    to bottom: the top frame consumes the current control's type and
    environment, produces the type/environment expected by the next
    frame, and so on until the outermost output matches the expected
    result type. -/
inductive ContinuationHasType (structural : WellFormedClassHierarchy ct) (h : Heap) :
    TyEnv → Ty → TyEnv → Ty → Continuation → Prop where
  | nil :
      ContinuationHasType structural h Γ T Γ T []
  | cons :
      FrameHasType structural h inΓ inTy midΓ midTy f →
      ContinuationHasType structural h midΓ midTy outΓ outTy k →
      ContinuationHasType structural h inΓ inTy outΓ outTy (f :: k)

/-- A machine state is safe when:
    - the heap is well-formed
    - the current environment is well-typed
    - the current control has a type
    - the continuation threads that type to the expected output type -/
def StateSafe (structural : WellFormedClassHierarchy ct) (heap : Heap) (env : Env)
    (ctrl : Control) (cont : Continuation) (expectedType : Ty) : Prop :=
  ∃ (Γ outΓ : TyEnv) (T : Ty),
    HeapWellFormed ct heap ∧
    EnvHasType structural heap env Γ ∧
    ControlHasType structural heap Γ ctrl T ∧
    ContinuationHasType structural heap Γ T outΓ expectedType cont

end SmallStep
