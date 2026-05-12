import FwPython.Static.Semantics.Core
import FwPython.Common.Steps

/-! # Multi-Step Execution

Defines multi-step execution as the reflexive-transitive closure of `Step`,
along with expression-level and program-level execution predicates. -/

namespace SmallStep

/-- Reflexive-transitive closure of the one-step relation. -/
abbrev Steps (ct : ClassTable) : State → State → Prop := RuntimeSteps (Step ct)

/-- Expression-level execution from a given heap and environment. -/
def evaluatesFrom
    (ct : ClassTable) (heap : Heap) (env : Env) (expr : Expr)
    (heap' : Heap) (result : Result) : Prop :=
  ∃ state,
    Steps ct (expressionState heap env expr) state ∧
    finalResult? state = some (heap', result)

/-- Program-level execution. -/
def programExecute (program : Program) (result : Result) : Prop :=
  ∃ state heap,
    Steps program.classes (initialState program) state ∧
    finalResult? state = some (heap, result)

end SmallStep
