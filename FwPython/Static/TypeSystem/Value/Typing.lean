import FwPython.Static.TypeSystem.Context
import FwPython.Static.Subtyping.Core
import FwPython.Static.Semantics.Core

/-! ## Value typing -/

/-- `ValueHasType ct h v T` — runtime value `v` has type `T` under
    class table `ct` and heap `h`. -/
inductive ValueHasType : ClassTable → Heap → Value → Ty → Prop where
  /-- An object reference has class type when the heap maps its OID to
      a class that is a subtype of the target class. -/
  | objRef :
      h.lookup oid = some obj →
      IsSubtype ct (.class_ obj.className) (.class_ cname) →
      ValueHasType ct h (.objRef oid) (.class_ cname)
  /-- An object reference has callable type when its heap payload is a
      bound method with compatible signature. -/
  | objRefCallable :
      h.lookup oid = some ⟨bmClass, .boundMethod recvOid m⟩ →
      h.lookup recvOid = some recvObj →
      MethodInReceiverMro ct recvObj.className m →
      ValueHasType ct h (.objRef oid) (.callable m.paramTy m.returnTy)
  /-- Subsumption: a value of type T also has type U when T <: U
      (target must be well-formed). -/
  | sub :
      ValueHasType ct h v T →
      IsSubtype ct T U →
      WellFormedTy ct U →
      ValueHasType ct h v U
  /-- Runtime intersection introduction: a value that has both types
      has the intersection type. -/
  | interIntro :
      ValueHasType ct h v T →
      ValueHasType ct h v U →
      WellFormedTy ct (.intersection T U) →
      ValueHasType ct h v (.intersection T U)
  /-- An object reference has `negClass C` when its runtime class has a
      deterministic MRO that excludes `C`. The `WellFormedTy` premise
      certifies the target class atom; well-formedness of the runtime
      class is recovered from the lookup pair. -/
  | objRefNegClass :
      h.lookup oid = some obj →
      WellFormedTy ct (.negClass C) →
      findClass ct obj.className = some cls →
      ComputeMro ct cls mro →
      C ∉ mro →
      ValueHasType ct h (.objRef oid) (.negClass C)

/-! ## Environment typing -/

/-- The runtime environment is well-typed w.r.t. the type environment. -/
def EnvHasType (ct : ClassTable) (h : Heap) (env : Env) (Γ : TyEnv) : Prop :=
  ∀ x T, Γ.lookup x = some T →
    ∃ v, env.lookup x = some v ∧ ValueHasType ct h v T

/-- Every type in the environment is well-formed. -/
def WellFormedTyEnv (ct : ClassTable) (Γ : TyEnv) : Prop :=
  ∀ x T, Γ.lookup x = some T → WellFormedTy ct T
