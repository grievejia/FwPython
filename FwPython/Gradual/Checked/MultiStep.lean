import FwPython.Gradual.Checked.Core
import FwPython.Common.Steps

/-! # Multi-Step Execution for the Checked Machine

Defines multi-step execution as the reflexive-transitive closure of `Checked.Step`,
along with expression-level and program-level execution predicates. -/

namespace Checked

/-- Reflexive-transitive closure of the one-step relation. -/
abbrev Steps (ct : GClassTable) (cct : CheckedClassTable) : State → State → Prop :=
  RuntimeSteps (Step ct cct)

/-- Expression-level execution from a given heap and environment. -/
def evaluatesFrom
    (ct : GClassTable) (cct : CheckedClassTable) (heap : CheckedHeap) (env : CheckedEnv)
    (expr : CheckedExpr) (heap' : CheckedHeap) (result : CheckedResult) : Prop :=
  ∃ state,
    Steps ct cct (expressionState heap env expr) state ∧
    finalResult? state = some (heap', result)

end Checked
