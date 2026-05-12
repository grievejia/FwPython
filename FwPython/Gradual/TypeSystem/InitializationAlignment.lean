import FwPython.Gradual.TypeSystem.RuntimePrecision
import FwPython.Gradual.TypeSystem.Blame.Provenance

/-! ## Initialization alignment package -/

namespace Checked

structure InitialElaboratedStateAlignmentPackage
    (gp₁ gp₂ : GProgram)
    (P₁ P₂ : GTy)
    (cp₁ cp₂ : CheckedProgram)
    (helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁)
    (helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂) : Prop where
  rootTarget_prec :
    CompileTargetPrecision
      (checkedTargetOfRuntimePublicTy P₁)
      (checkedTargetOfRuntimePublicTy P₂)
  program_prec :
    CheckedProgramPrecision gp₁.classes cp₁ cp₂
  main_moreStatic :
    MoreStatic gp₂.classes helab₁.main_srcTy helab₂.main_srcTy
  elaborated_prec :
    ElaboratedStatePrecision helab₁ helab₂
      (initialState cp₁)
      (initialState cp₂)

theorem initial_elaborated_state_precision
    (hgp : ProgramTargetPrecision gp₁ gp₂)
    (helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁)
    (helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂)
    (hRoot : ProgramRootTargetInputPrecision P₁ P₂) :
    InitialElaboratedStateAlignmentPackage gp₁ gp₂ P₁ P₂ cp₁ cp₂ helab₁ helab₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact compileTargetPrecision_of_checkedTargetPrecision hRoot
  · exact static_gradual_guarantee hgp helab₁ helab₂ hRoot
  · exact (static_gradual_guarantee_main_moreStatic hgp helab₁ helab₂ hRoot).1
  · exact initial_state_elaborated_precision hgp helab₁ helab₂ hRoot

end Checked
