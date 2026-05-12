import FwPython.Common.Env
import FwPython.Gradual.Types

/-! ## Gradual type environment -/

/-- Gradual type environment: maps variable names to gradual types. -/
abbrev GTyEnv := NamedEnv GTy

abbrev GTyEnv.update (self : GTyEnv) (x : Identifier) (S : GTy) :=
  NamedEnv.update self x S
