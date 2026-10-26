import FwPython.Static.TypeSystem.Context
import FwPython.Static.Subtyping.Core
import FwPython.Static.Semantics.Core

/-! ## Value typing -/

/-- Runtime value `v` has type `T` in heap `h`.
All subtype comparisons use the supplied hierarchy. -/
inductive ValueHasType {ct : ClassTable} (structural : WellFormedClassHierarchy ct) : Heap → Value → Ty → Prop where
  /-- An object reference has class type when the heap maps its OID to
      a class that is a subtype of the target class. -/
  | objRef :
      h.lookup oid = some obj →
      IsSubtype structural (.class_ obj.className) (.class_ cname) →
      ValueHasType structural h (.objRef oid) (.class_ cname)
  /-- An object reference has callable type when its heap payload is a
      bound method with its declared signature. The heap invariant supplies
      the receiver lookup and method origin. -/
  | objRefCallable :
      h.lookup oid = some ⟨bmClass, .boundMethod recvOid m⟩ →
      ValueHasType structural h (.objRef oid) (.callable m.paramTy m.returnTy)
  /-- A value retains its typing at a supertype.
      The subtype proof establishes validity of both types. -/
  | sub :
      ValueHasType structural h v T →
      IsSubtype structural T U →
      ValueHasType structural h v U
  /-- Runtime intersection introduction: a value that has both types
      has the intersection type. -/
  | interIntro :
      ValueHasType structural h v T →
      ValueHasType structural h v U →
      WellFormedTy ct (.intersection T U) →
      ValueHasType structural h v (.intersection T U)
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
      ValueHasType structural h (.objRef oid) (.negClass C)

/-! ## Environment typing -/

/-- Each variable in the type environment names a runtime value with that type.
The value typings use the same hierarchy and heap. -/
def EnvHasType {ct : ClassTable} (structural : WellFormedClassHierarchy ct) (h : Heap) (env : Env) (Γ : TyEnv) : Prop :=
  ∀ x T, Γ.lookup x = some T →
    ∃ v, env.lookup x = some v ∧ ValueHasType structural h v T

/-- Every type in the environment is well-formed. -/
def WellFormedTyEnv (ct : ClassTable) (Γ : TyEnv) : Prop :=
  ∀ x T, Γ.lookup x = some T → WellFormedTy ct T
