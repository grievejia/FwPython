import FwPython.Common.Env
import FwPython.Static.Types

/-! ## Type environment -/

/-- Type environment: maps variable names to types. -/
abbrev TyEnv := NamedEnv Ty

abbrev TyEnv.update (self : TyEnv) (x : Identifier) (S : Ty) :=
  NamedEnv.update self x S
