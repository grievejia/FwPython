import FwPython.Gradual.TypeSystem.Source.Compile
import FwPython.Gradual.TypeSystem.Safety
import FwPython.Gradual.TypeSystem.ClassTable.Compile

/-! # runtimePublicTy Regression Examples

Verifies computation, structural preservation, and compilation integration
of `runtimePublicTy`, the machine-facing type projection. With `negClass`
as the only gradual negation, `runtimePublicTy` is now structural through
every constructor. -/

/-! ## Computation: projection through positive constructors, atomic on negClass -/

example : runtimePublicTy (.negClass "Dog") = .negClass "Dog" := rfl
example : runtimePublicTy (.callable (.negClass "Dog") (.class_ "Cat")) =
    .callable (.negClass "Dog") (.class_ "Cat") := rfl
example : runtimePublicTy (.union (.negClass "Dog") (.class_ "Cat")) =
    .union (.negClass "Dog") (.class_ "Cat") := rfl
example : runtimePublicTy (.intersection (.negClass "Dog") (.class_ "Cat")) =
    .intersection (.negClass "Dog") (.class_ "Cat") := rfl

/-! ## Idempotence -/

example (G : GTy) : runtimePublicTy (runtimePublicTy G) = runtimePublicTy G :=
  runtimePublicTy_idempotent G

/-! ## Structural preservation -/

example (h : FormulaGTy G) : FormulaGTy (runtimePublicTy G) :=
  formulaGTy_runtimePublicTy h
example (h : RuntimePublicAnnotation gct G) :
    RuntimePublicAnnotation gct (runtimePublicTy G) := by
  simpa [runtimePublicTy_id] using h
example (h : WellFormedGTy gct G) : WellFormedGTy gct (runtimePublicTy G) :=
  wellFormedGTy_runtimePublicTy h
example (h : AnnotationTargetPrecision G₁ G₂) :
    AnnotationTargetPrecision (runtimePublicTy G₁) (runtimePublicTy G₂) := by
  simpa [runtimePublicTy_id] using h
example (h : ProgramRootTargetInputPrecision G₁ G₂) :
    ProgramRootTargetInputPrecision (runtimePublicTy G₁) (runtimePublicTy G₂) := by
  simpa [ProgramRootTargetInputPrecision, runtimePublicTy_id] using h

/-! ## Checked compilation uses explicit elaboration targets -/

example
    (scope : LabelScope)
    (hsrcEnv : SourceEnvOk gct Γ)
    (helab : ElabEnvOk gct Γ Δ)
    (hwfct : WellFormedGClassTableCore gct)
    (hPruntime : RuntimePublicAnnotation gct P)
    (hPwf : WellFormedGTy gct P)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy)
    (n : Nat) :
    CheckedHasType gct Δ (compileCheck scope hsrc Δ P n).1 (runtimePublicTy P) :=
  compileCheck_checked scope hsrcEnv helab hwfct hPruntime hPwf hsrc

/-! ## Gradual negClass annotations stay definitional -/

def runtimePublicTyNegMethod : GMethod where
  name := "f"
  receiverParam := "self"
  param := "arg"
  paramTy := .negClass "Dog"
  returnTy := .negClass "Cat"
  body := .constTrue

example : runtimePublicTyNegMethod.paramTy = .negClass "Dog" := rfl
example : runtimePublicTyNegMethod.returnTy = .negClass "Cat" := rfl
example : compileBoundaryRaw runtimePublicTyNegMethod.paramTy = .negClass "Dog" := rfl
example : compileBoundaryRaw runtimePublicTyNegMethod.returnTy = .negClass "Cat" := rfl

/-! ## Compiled checked methods use gradual annotations directly -/

example (h : Checked.IsCompiledMethodAt gct cname gm cm) :
    cm.paramTy = gm.paramTy :=
  h.paramTy_eq
example (h : Checked.IsCompiledMethodAt gct cname gm cm) :
    cm.returnTy = gm.returnTy :=
  h.returnTy_eq
example (h : Checked.IsCompiledMethodAt gct cname gm cm) :
    cm.parameterContract = compileBoundaryRaw gm.paramTy := by
  simpa [h.paramTy_eq] using h.paramContract_eq
example (h : Checked.IsCompiledMethodAt gct cname gm cm) :
    cm.returnContract = compileBoundaryRaw gm.returnTy := by
  simpa [h.returnTy_eq] using h.returnContract_eq

/-! ## AlignedCheckedClassTable uses gradual annotations directly -/

example
    (halign : Checked.AlignedCheckedClassTable gct cct)
    (hfc : findGClass gct cname = some gc)
    (hfcc : findCheckedClass cct cname = some cc)
    (hmro : GComputeMro gct gc mro)
    (hfm : findGMethodInMro gct mro gm.name = some gm) :
    ∃ cm, findCheckedMethodInMro cct mro gm.name = some cm ∧
      cm.paramTy = gm.paramTy ∧
      cm.returnTy = gm.returnTy ∧
      cm.parameterContract = compileBoundaryRaw cm.paramTy ∧
      cm.returnContract = compileBoundaryRaw cm.returnTy :=
  halign.methodLookupAgree cname gc cc mro gm hfc hfcc hmro hfm
