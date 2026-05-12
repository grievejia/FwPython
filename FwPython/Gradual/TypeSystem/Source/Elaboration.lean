import FwPython.Gradual.TypeSystem.Source.Compile.Core

/-! # Proof-level elaboration graph for `compileCheck`

`ElabCheck` is a thin relational wrapper around the executable compiler.
It records no extra structure beyond the exact checked expression and the
final fresh-label counter produced by `compileCheck`.
-/

def ElabCheck
    (scope : LabelScope)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy)
    (Δ : GTyEnv)
    (P : GTy)
    (n : Nat)
    (e' : CheckedExpr)
    (n' : Nat) : Prop :=
  (e', n') = ((compileCheck scope hsrc Δ P n).1, (compileCheck scope hsrc Δ P n).2)

theorem compileCheck_elaborates :
    ElabCheck scope hsrc Δ P n
      (compileCheck scope hsrc Δ P n).1
      (compileCheck scope hsrc Δ P n).2 :=
  rfl

theorem elabCheck_eq_compileCheck
    (helab : ElabCheck scope hsrc Δ P n e' n') :
    e' = (compileCheck scope hsrc Δ P n).1 ∧
      n' = (compileCheck scope hsrc Δ P n).2 := by
  cases helab; exact ⟨rfl, rfl⟩

theorem elabCheck_functional
    (helab₁ : ElabCheck scope hsrc Δ P n e₁ n₁)
    (helab₂ : ElabCheck scope hsrc Δ P n e₂ n₂) :
    e₁ = e₂ ∧ n₁ = n₂ := by
  cases helab₁; cases helab₂; exact ⟨rfl, rfl⟩

theorem elabCheck_checked
    {hwfct : WellFormedGClassTableCore gct}
    (scope : LabelScope)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy)
    (henv : SourceEnvOk gct Γ)
    (helab : ElabEnvOk gct Γ Δ)
    (hPruntime : RuntimePublicAnnotation gct P)
    (hPwf : WellFormedGTy gct P)
    (hcheck : ElabCheck scope hsrc Δ P n e' n') :
    CheckedHasType gct Δ e' (runtimePublicTy P) := by
  cases hcheck
  exact compileCheck_checked scope henv helab hwfct hPruntime hPwf hsrc
