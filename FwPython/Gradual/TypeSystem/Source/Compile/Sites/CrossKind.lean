import FwPython.Gradual.TypeSystem.Source.Compile.Sites.Intervals

theorem compileCheck_enforce_callReturn_disjoint
    (scope : LabelScope) (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    ∀ {Δ P n exprPathE exprPathC eE c labelsE pE
       calleeC argC}
      {paramTyC returnTyC : CheckedTarget}
      {labelsC : BoundaryLabels (compileBoundaryTarget returnTyC)}
      {pC : BoundaryPath (compileBoundaryTarget returnTyC)},
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPathE =
        some (.enforce eE c labelsE) →
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPathC =
        some (.call calleeC argC paramTyC returnTyC labelsC) →
      (labelsE.at pE).site ≠ (labelsC.at pC).site := by
  intro Δ P n exprPathE exprPathC eE c labelsE pE calleeC argC paramTyC returnTyC labelsC pC
  induction hsrc generalizing scope Δ P n exprPathE exprPathC eE c labelsE pE
      calleeC argC paramTyC returnTyC labelsC pC with
  | var | constNone | constTrue | constFalse | new | isInstance =>
      cases exprPathC with
      | nil =>
          intro hnodeE hnodeC
          simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
      | cons childC restC =>
          intro hnodeE hnodeC
          cases childC <;> simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
          case enforceBody =>
            cases restC <;> simp [CheckedExpr.nodeAt] at hnodeC
  | attrAccess hbase _ ih =>
      cases exprPathE with
      | nil =>
          intro hnodeE hnodeC
          simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
          rcases hnodeE with ⟨_, rfl, hlabelsE⟩
          cases hlabelsE
          cases exprPathC with
          | nil =>
              simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
          | cons childC restC =>
              cases childC with
              | attrBase => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
              | callCallee => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
              | callArg => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
              | condTest => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
              | condThen => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
              | condElse => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
              | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
              | enforceBody =>
                  cases restC with
                  | nil =>
                      simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                  | cons childC' tailC =>
                      cases childC' <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                      case dynAttrBase =>
                          have hrootLo :=
                            (mkBoundaryLabels_interval
                              (scope := scope)
                              (pol := .positive)
                              (c := compileBoundaryTarget (checkedTargetOfRuntimePublicTy P))
                              (n := (compileCheck scope hbase Δ .any n).2 + 1)
                              (p := pE)).1
                          obtain ⟨_, hbaseHi⟩ :=
                            compileCheck_call_return_site_interval
                              (scope := scope)
                              (hsrc := hbase)
                              (Δ := Δ)
                              (P := .any)
                              (n := n)
                              (exprPath := tailC)
                              (callee := calleeC)
                              (arg := argC)
                              (paramTy := paramTyC)
                              (returnTy := returnTyC)
                              (labels := labelsC)
                              pC
                              hnodeC
                          intro hsite
                          rw [hsite] at hrootLo
                          omega
      | cons childE restE =>
          intro hnodeE hnodeC
          cases childE with
          | attrBase => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
          | callCallee => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
          | callArg => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
          | condTest => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
          | condThen => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
          | condElse => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
          | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
          | enforceBody =>
              cases restE with
              | nil =>
                  simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
              | cons childE' tailE =>
                  cases childE' with
                  | attrBase => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
                  | callCallee => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
                  | callArg => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
                  | condTest => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
                  | condThen => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
                  | condElse => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
                  | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
                  | dynAttrBase =>
                      cases exprPathC with
                      | nil =>
                          simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                      | cons childC restC =>
                          cases childC with
                          | attrBase => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                          | callCallee => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                          | callArg => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                          | condTest => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                          | condThen => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                          | condElse => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                          | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                          | enforceBody =>
                              cases restC with
                              | nil =>
                                  simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                              | cons childC' tailC =>
                                  cases childC' <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                                  case dynAttrBase =>
                                      exact ih
                                        (scope := scope)
                                        (Δ := Δ)
                                        (P := .any)
                                        (n := n)
                                        (exprPathE := tailE)
                                        (exprPathC := tailC)
                                        (eE := eE)
                                        (c := c)
                                        (labelsE := labelsE)
                                        (pE := pE)
                                        (calleeC := calleeC)
                                        (argC := argC)
                                        (paramTyC := paramTyC)
                                        (returnTyC := returnTyC)
                                        (labelsC := labelsC)
                                        (pC := pC)
                                        hnodeE hnodeC
  | call hcallee harg _ _ _ _ ihC ihA =>
      rename_i Γ' calleeExpr calleeSrcTy argExpr argSrcTy R hcallee_callable hcallee_wf harg_wf hcall
      let D : GTy := callParamTarget gct argSrcTy
      cases exprPathE with
      | nil =>
          intro hnodeE
          simp [compileCheck, CheckedExpr.nodeAt] at hnodeE
      | cons childE restE =>
          intro hnodeE hnodeC
          cases childE with
          | attrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnodeE
          | condTest => simp [compileCheck, CheckedExpr.nodeAt] at hnodeE
          | condThen => simp [compileCheck, CheckedExpr.nodeAt] at hnodeE
          | condElse => simp [compileCheck, CheckedExpr.nodeAt] at hnodeE
          | enforceBody => simp [compileCheck, CheckedExpr.nodeAt] at hnodeE
          | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnodeE
          | callCallee =>
              cases exprPathC with
              | nil =>
                  obtain ⟨_, hcalleeHi⟩ :=
                    compileCheck_enforce_site_interval
                      (scope := scope)
                      (hsrc := hcallee)
                      (Δ := Δ)
                      (P := .callable D P)
                      (n := n)
                      (exprPath := restE)
                      (e' := eE)
                      (c := c)
                      (labels := labelsE)
                      pE
                      hnodeE
                  have hargMono :
                      (compileCheck scope hcallee Δ (.callable D P) n).2 ≤
                        (compileCheck scope harg Δ D
                          (compileCheck scope hcallee Δ (.callable D P) n).2).2 :=
                    compileCheck_counter_monotone
                      (scope := scope)
                      (hsrc := harg)
                      (Δ := Δ)
                      (P := D)
                      (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
                  have hrootLo :=
                    compileCheck_call_root_site_lower_bound
                      (scope := scope)
                      (hcallee := hcallee)
                      (harg := harg)
                      (hcallee_callable := hcallee_callable)
                      (hcallee_wf := hcallee_wf)
                      (harg_wf := harg_wf)
                      (hcall := hcall)
                      (Δ := Δ)
                      (P := P)
                      (n := n)
                      (callee := calleeC)
                      (arg := argC)
                      (paramTy := paramTyC)
                      (returnTy := returnTyC)
                      (labels := labelsC)
                      pC
                      hnodeC
                  have hrootLo' :
                      (compileCheck scope harg Δ D
                        (compileCheck scope hcallee Δ (.callable D P) n).2).2 ≤
                        (labelsC.at pC).site := by
                    simpa [D] using hrootLo
                  intro hsite
                  rw [hsite] at hcalleeHi
                  have hrootLo := hrootLo'
                  omega
              | cons childC restC =>
                  cases childC with
                  | attrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | condTest => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | condThen => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | condElse => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | enforceBody => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | callCallee =>
                      simp [compileCheck, CheckedExpr.nodeAt] at hnodeE hnodeC
                      exact ihC
                        (scope := scope)
                        (Δ := Δ)
                        (P := .callable D P)
                        (n := n)
                        (exprPathE := restE)
                        (exprPathC := restC)
                        (eE := eE)
                        (c := c)
                        (labelsE := labelsE)
                        (pE := pE)
                        (calleeC := calleeC)
                        (argC := argC)
                        (paramTyC := paramTyC)
                        (returnTyC := returnTyC)
                        (labelsC := labelsC)
                        (pC := pC)
                        hnodeE hnodeC
                  | callArg =>
                      simp [compileCheck, CheckedExpr.nodeAt] at hnodeE hnodeC
                      exact compileCheck_enforce_callReturn_intervals_disjoint
                        (scope := scope)
                        (hsrc₁ := hcallee)
                        (hsrc₂ := harg)
                        (Δ₁ := Δ)
                        (Δ₂ := Δ)
                        (P₁ := .callable D P)
                        (P₂ := D)
                        (n₁ := n)
                        (n₂ := (compileCheck scope hcallee Δ (.callable D P) n).2)
                        (hdisjoint := Nat.le_refl _)
                        hnodeE hnodeC
          | callArg =>
              cases exprPathC with
              | nil =>
                  obtain ⟨_, hargHi⟩ :=
                    compileCheck_enforce_site_interval
                      (scope := scope)
                      (hsrc := harg)
                      (Δ := Δ)
                      (P := D)
                      (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
                      (exprPath := restE)
                      (e' := eE)
                      (c := c)
                      (labels := labelsE)
                      pE
                      hnodeE
                  have hrootLo :=
                    compileCheck_call_root_site_lower_bound
                      (scope := scope)
                      (hcallee := hcallee)
                      (harg := harg)
                      (hcallee_callable := hcallee_callable)
                      (hcallee_wf := hcallee_wf)
                      (harg_wf := harg_wf)
                      (hcall := hcall)
                      (Δ := Δ)
                      (P := P)
                      (n := n)
                      (callee := calleeC)
                      (arg := argC)
                      (paramTy := paramTyC)
                      (returnTy := returnTyC)
                      (labels := labelsC)
                      pC
                      hnodeC
                  have hrootLo' :
                      (compileCheck scope harg Δ D
                        (compileCheck scope hcallee Δ (.callable D P) n).2).2 ≤
                        (labelsC.at pC).site := by
                    simpa [D] using hrootLo
                  intro hsite
                  rw [hsite] at hargHi
                  have hrootLo := hrootLo'
                  omega
              | cons childC restC =>
                  cases childC with
                  | attrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | condTest => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | condThen => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | condElse => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | enforceBody => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | callCallee =>
                      simp [compileCheck, CheckedExpr.nodeAt] at hnodeE hnodeC
                      have hneq :=
                        compileCheck_callReturn_enforce_intervals_disjoint
                          (scope := scope)
                          (hsrc₁ := hcallee)
                          (hsrc₂ := harg)
                          (Δ₁ := Δ)
                          (Δ₂ := Δ)
                          (P₁ := .callable D P)
                          (P₂ := D)
                          (n₁ := n)
                          (n₂ := (compileCheck scope hcallee Δ (.callable D P) n).2)
                          (hdisjoint := Nat.le_refl _)
                          (exprPathC := restC)
                          (exprPathE := restE)
                          (calleeC := calleeC)
                          (argC := argC)
                          (paramTyC := paramTyC)
                          (returnTyC := returnTyC)
                          (labelsC := labelsC)
                          (pC := pC)
                          (eE := eE)
                          (c := c)
                          (labelsE := labelsE)
                          (pE := pE)
                          hnodeC hnodeE
                      intro hsite
                      exact hneq hsite.symm
                  | callArg =>
                      simp [compileCheck, CheckedExpr.nodeAt] at hnodeE hnodeC
                      exact ihA
                        (scope := scope)
                        (Δ := Δ)
                        (P := D)
                        (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
                        (exprPathE := restE)
                        (exprPathC := restC)
                        (eE := eE)
                        (c := c)
                        (labelsE := labelsE)
                        (pE := pE)
                        (calleeC := calleeC)
                        (argC := argC)
                        (paramTyC := paramTyC)
                        (returnTyC := returnTyC)
                        (labelsC := labelsC)
                        (pC := pC)
                        hnodeE hnodeC
  | cond _ htest _ hthen helse ihTest ihThen ihElse =>
      cases exprPathE with
      | nil =>
          intro hnodeE
          simp [compileCheck, CheckedExpr.nodeAt] at hnodeE
      | cons childE restE =>
          intro hnodeE hnodeC
          cases exprPathC with
          | nil =>
              simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
          | cons childC restC =>
              cases childE <;> cases childC <;> simp [compileCheck, CheckedExpr.nodeAt] at hnodeE hnodeC
              case condTest.condTest =>
                  exact ihTest
                    (scope := scope)
                    (Δ := Δ)
                    (P := .class_ boolClass)
                    (n := n)
                    (exprPathE := restE)
                    (exprPathC := restC)
                    (eE := eE)
                    (c := c)
                    (labelsE := labelsE)
                    (pE := pE)
                    (calleeC := calleeC)
                    (argC := argC)
                    (paramTyC := paramTyC)
                    (returnTyC := returnTyC)
                    (labelsC := labelsC)
                    (pC := pC)
                    hnodeE hnodeC
              case condTest.condThen =>
                  exact compileCheck_enforce_callReturn_intervals_disjoint
                    (scope := scope)
                    (hsrc₁ := htest)
                    (hsrc₂ := hthen)
                    (Δ₁ := Δ)
                    (Δ₂ := Δ)
                    (P₁ := .class_ boolClass)
                    (P₂ := P)
                    (n₁ := n)
                    (n₂ := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                    (hdisjoint := Nat.le_refl _)
                    hnodeE hnodeC
              case condTest.condElse =>
                  have hthenMono :
                      (compileCheck scope htest Δ (.class_ boolClass) n).2 ≤
                        (compileCheck scope hthen Δ P
                          (compileCheck scope htest Δ (.class_ boolClass) n).2).2 :=
                    compileCheck_counter_monotone
                      (scope := scope)
                      (hsrc := hthen)
                      (Δ := Δ)
                      (P := P)
                      (n := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                  exact compileCheck_enforce_callReturn_intervals_disjoint
                    (scope := scope)
                    (hsrc₁ := htest)
                    (hsrc₂ := helse)
                    (Δ₁ := Δ)
                    (Δ₂ := Δ)
                    (P₁ := .class_ boolClass)
                    (P₂ := P)
                    (n₁ := n)
                    (n₂ := (compileCheck scope hthen Δ P
                      (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                    (hdisjoint := hthenMono)
                    hnodeE hnodeC
              case condThen.condTest =>
                  have hneq :=
                    compileCheck_callReturn_enforce_intervals_disjoint
                      (scope := scope)
                      (hsrc₁ := htest)
                      (hsrc₂ := hthen)
                      (Δ₁ := Δ)
                      (Δ₂ := Δ)
                      (P₁ := .class_ boolClass)
                      (P₂ := P)
                      (n₁ := n)
                      (n₂ := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                      (hdisjoint := Nat.le_refl _)
                      (exprPathC := restC)
                      (exprPathE := restE)
                      (calleeC := calleeC)
                      (argC := argC)
                      (paramTyC := paramTyC)
                      (returnTyC := returnTyC)
                      (labelsC := labelsC)
                      (pC := pC)
                      (eE := eE)
                      (c := c)
                      (labelsE := labelsE)
                      (pE := pE)
                      hnodeC hnodeE
                  intro hsite
                  exact hneq hsite.symm
              case condThen.condThen =>
                  exact ihThen
                    (scope := scope)
                    (Δ := Δ)
                    (P := P)
                    (n := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                    (exprPathE := restE)
                    (exprPathC := restC)
                    (eE := eE)
                    (c := c)
                    (labelsE := labelsE)
                    (pE := pE)
                    (calleeC := calleeC)
                    (argC := argC)
                    (paramTyC := paramTyC)
                    (returnTyC := returnTyC)
                    (labelsC := labelsC)
                    (pC := pC)
                    hnodeE hnodeC
              case condThen.condElse =>
                  exact compileCheck_enforce_callReturn_intervals_disjoint
                    (scope := scope)
                    (hsrc₁ := hthen)
                    (hsrc₂ := helse)
                    (Δ₁ := Δ)
                    (Δ₂ := Δ)
                    (P₁ := P)
                    (P₂ := P)
                    (n₁ := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                    (n₂ := (compileCheck scope hthen Δ P
                      (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                    (hdisjoint := Nat.le_refl _)
                    hnodeE hnodeC
              case condElse.condTest =>
                  have hthenMono :
                      (compileCheck scope htest Δ (.class_ boolClass) n).2 ≤
                        (compileCheck scope hthen Δ P
                          (compileCheck scope htest Δ (.class_ boolClass) n).2).2 :=
                    compileCheck_counter_monotone
                      (scope := scope)
                      (hsrc := hthen)
                      (Δ := Δ)
                      (P := P)
                      (n := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                  have hneq :=
                    compileCheck_callReturn_enforce_intervals_disjoint
                      (scope := scope)
                      (hsrc₁ := htest)
                      (hsrc₂ := helse)
                      (Δ₁ := Δ)
                      (Δ₂ := Δ)
                      (P₁ := .class_ boolClass)
                      (P₂ := P)
                      (n₁ := n)
                      (n₂ := (compileCheck scope hthen Δ P
                        (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                      (hdisjoint := hthenMono)
                      (exprPathC := restC)
                      (exprPathE := restE)
                      (calleeC := calleeC)
                      (argC := argC)
                      (paramTyC := paramTyC)
                      (returnTyC := returnTyC)
                      (labelsC := labelsC)
                      (pC := pC)
                      (eE := eE)
                      (c := c)
                      (labelsE := labelsE)
                      (pE := pE)
                      hnodeC hnodeE
                  intro hsite
                  exact hneq hsite.symm
              case condElse.condThen =>
                  have hneq :=
                    compileCheck_callReturn_enforce_intervals_disjoint
                      (scope := scope)
                      (hsrc₁ := hthen)
                      (hsrc₂ := helse)
                      (Δ₁ := Δ)
                      (Δ₂ := Δ)
                      (P₁ := P)
                      (P₂ := P)
                      (n₁ := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                      (n₂ := (compileCheck scope hthen Δ P
                        (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                      (hdisjoint := Nat.le_refl _)
                      (exprPathC := restC)
                      (exprPathE := restE)
                      (calleeC := calleeC)
                      (argC := argC)
                      (paramTyC := paramTyC)
                      (returnTyC := returnTyC)
                      (labelsC := labelsC)
                      (pC := pC)
                      (eE := eE)
                      (c := c)
                      (labelsE := labelsE)
                      (pE := pE)
                      hnodeC hnodeE
                  intro hsite
                  exact hneq hsite.symm
              case condElse.condElse =>
                  exact ihElse
                    (scope := scope)
                    (Δ := Δ)
                    (P := P)
                    (n := (compileCheck scope hthen Δ P
                      (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                    (exprPathE := restE)
                    (exprPathC := restC)
                    (eE := eE)
                    (c := c)
                    (labelsE := labelsE)
                    (pE := pE)
                    (calleeC := calleeC)
                    (argC := argC)
                    (paramTyC := paramTyC)
                    (returnTyC := returnTyC)
                    (labelsC := labelsC)
                    (pC := pC)
                    hnodeE hnodeC
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
      rename_i b C cls thenBranch thenSrcTy elseBranch elseSrcTy Γ' x
      cases hΔ : Δ.lookup x with
      | none =>
          cases exprPathE with
          | nil =>
              intro hnodeE
              simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeE
          | cons childE restE =>
              intro hnodeE hnodeC
              cases childE with
              | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeE
              | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeE
              | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeE
              | condTest =>
                  simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeE
                  cases restE <;> simp [CheckedExpr.nodeAt] at hnodeE
              | condThen =>
                  cases exprPathC with
                  | nil =>
                      simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                  | cons childC restC =>
                      cases childC with
                      | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | condTest =>
                          simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                          cases restC <;> simp [CheckedExpr.nodeAt] at hnodeC
                      | condThen =>
                          simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeE hnodeC
                          exact ihThen
                            (scope := scope)
                            (Δ := Δ)
                            (P := P)
                            (n := n)
                            (exprPathE := restE)
                            (exprPathC := restC)
                            (eE := eE)
                            (c := c)
                            (labelsE := labelsE)
                            (pE := pE)
                            (calleeC := calleeC)
                            (argC := argC)
                            (paramTyC := paramTyC)
                            (returnTyC := returnTyC)
                            (labelsC := labelsC)
                            (pC := pC)
                            hnodeE hnodeC
                      | condElse =>
                          simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeE hnodeC
                          exact compileCheck_enforce_callReturn_intervals_disjoint
                            (scope := scope)
                            (hsrc₁ := hthen)
                            (hsrc₂ := helse)
                            (Δ₁ := Δ)
                            (Δ₂ := Δ)
                            (P₁ := P)
                            (P₂ := P)
                            (n₁ := n)
                            (n₂ := (compileCheck scope hthen Δ P n).2)
                            (pE := pE)
                            (hdisjoint := Nat.le_refl _)
                            hnodeE hnodeC
                      | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
              | condElse =>
                  cases exprPathC with
                  | nil =>
                      simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                  | cons childC restC =>
                      cases childC with
                      | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | condTest =>
                          simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                          cases restC <;> simp [CheckedExpr.nodeAt] at hnodeC
                      | condThen =>
                          simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeE hnodeC
                          have hneq :=
                            compileCheck_callReturn_enforce_intervals_disjoint
                              (scope := scope)
                              (hsrc₁ := hthen)
                              (hsrc₂ := helse)
                              (Δ₁ := Δ)
                              (Δ₂ := Δ)
                              (P₁ := P)
                              (P₂ := P)
                              (n₁ := n)
                              (n₂ := (compileCheck scope hthen Δ P n).2)
                              (hdisjoint := Nat.le_refl _)
                              (exprPathC := restC)
                              (exprPathE := restE)
                              (calleeC := calleeC)
                              (argC := argC)
                              (paramTyC := paramTyC)
                              (returnTyC := returnTyC)
                              (labelsC := labelsC)
                              (pC := pC)
                              (eE := eE)
                              (c := c)
                              (labelsE := labelsE)
                              (pE := pE)
                              hnodeC hnodeE
                          intro hsite
                          exact hneq hsite.symm
                      | condElse =>
                          simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeE hnodeC
                          exact ihElse
                            (scope := scope)
                            (Δ := Δ)
                            (P := P)
                            (n := (compileCheck scope hthen Δ P n).2)
                            (exprPathE := restE)
                            (exprPathC := restC)
                            (eE := eE)
                            (c := c)
                            (labelsE := labelsE)
                            (pE := pE)
                            (calleeC := calleeC)
                            (argC := argC)
                            (paramTyC := paramTyC)
                            (returnTyC := returnTyC)
                            (labelsC := labelsC)
                            (pC := pC)
                            hnodeE hnodeC
                      | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
              | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeE
              | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeE
      | some T =>
          by_cases href : CheckedBranchRefineOk gct T C
          · cases exprPathE with
            | nil =>
                intro hnodeE
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
            | cons childE restE =>
                intro hnodeE hnodeC
                cases childE with
                | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
                | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
                | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
                | condTest =>
                    simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
                    cases restE <;> simp [CheckedExpr.nodeAt] at hnodeE
                | condThen =>
                    cases exprPathC with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                    | cons childC restC =>
                        cases childC with
                        | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | condTest =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                            cases restC <;> simp [CheckedExpr.nodeAt] at hnodeC
                        | condThen =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE hnodeC
                            exact ihThen
                              (scope := scope)
                              (Δ := Δ.update x (.intersection T (.class_ C)))
                              (P := P)
                              (n := n)
                              (exprPathE := restE)
                              (exprPathC := restC)
                              (eE := eE)
                              (c := c)
                              (labelsE := labelsE)
                              (pE := pE)
                              (calleeC := calleeC)
                              (argC := argC)
                              (paramTyC := paramTyC)
                              (returnTyC := returnTyC)
                              (labelsC := labelsC)
                              (pC := pC)
                              hnodeE hnodeC
                        | condElse =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE hnodeC
                            exact compileCheck_enforce_callReturn_intervals_disjoint
                              (scope := scope)
                              (hsrc₁ := hthen)
                              (hsrc₂ := helse)
                              (Δ₁ := Δ.update x (.intersection T (.class_ C)))
                              (Δ₂ := Δ.update x (.intersection T (.negClass C)))
                              (P₁ := P)
                              (P₂ := P)
                              (n₁ := n)
                              (n₂ := (compileCheck scope hthen
                                (Δ.update x (.intersection T (.class_ C))) P n).2)
                              (pE := pE)
                              (hdisjoint := Nat.le_refl _)
                              hnodeE hnodeC
                        | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                | condElse =>
                    cases exprPathC with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                    | cons childC restC =>
                        cases childC with
                        | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | condTest =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                            cases restC <;> simp [CheckedExpr.nodeAt] at hnodeC
                        | condThen =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE hnodeC
                            have hneq :=
                              compileCheck_callReturn_enforce_intervals_disjoint
                                (scope := scope)
                                (hsrc₁ := hthen)
                                (hsrc₂ := helse)
                                (Δ₁ := Δ.update x (.intersection T (.class_ C)))
                                (Δ₂ := Δ.update x (.intersection T (.negClass C)))
                                (P₁ := P)
                                (P₂ := P)
                                (n₁ := n)
                                (n₂ := (compileCheck scope hthen
                                  (Δ.update x (.intersection T (.class_ C))) P n).2)
                                (hdisjoint := Nat.le_refl _)
                                (exprPathC := restC)
                                (exprPathE := restE)
                                (calleeC := calleeC)
                                (argC := argC)
                                (paramTyC := paramTyC)
                                (returnTyC := returnTyC)
                                (labelsC := labelsC)
                                (pC := pC)
                                (eE := eE)
                                (c := c)
                                (labelsE := labelsE)
                                (pE := pE)
                                hnodeC hnodeE
                            intro hsite
                            exact hneq hsite.symm
                        | condElse =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE hnodeC
                            exact ihElse
                              (scope := scope)
                              (Δ := Δ.update x (.intersection T (.negClass C)))
                              (P := P)
                              (n := (compileCheck scope hthen
                                (Δ.update x (.intersection T (.class_ C))) P n).2)
                              (exprPathE := restE)
                              (exprPathC := restC)
                              (eE := eE)
                              (c := c)
                              (labelsE := labelsE)
                              (pE := pE)
                              (calleeC := calleeC)
                              (argC := argC)
                              (paramTyC := paramTyC)
                              (returnTyC := returnTyC)
                              (labelsC := labelsC)
                              (pC := pC)
                              hnodeE hnodeC
                        | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
                | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
          · cases exprPathE with
            | nil =>
                intro hnodeE
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
            | cons childE restE =>
                intro hnodeE hnodeC
                cases childE with
                | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
                | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
                | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
                | condTest =>
                    simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
                    cases restE <;> simp [CheckedExpr.nodeAt] at hnodeE
                | condThen =>
                    cases exprPathC with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                    | cons childC restC =>
                        cases childC with
                        | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | condTest =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                            cases restC <;> simp [CheckedExpr.nodeAt] at hnodeC
                        | condThen =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE hnodeC
                            exact ihThen
                              (scope := scope)
                              (Δ := Δ)
                              (P := P)
                              (n := n)
                              (exprPathE := restE)
                              (exprPathC := restC)
                              (eE := eE)
                              (c := c)
                              (labelsE := labelsE)
                              (pE := pE)
                              (calleeC := calleeC)
                              (argC := argC)
                              (paramTyC := paramTyC)
                              (returnTyC := returnTyC)
                              (labelsC := labelsC)
                              (pC := pC)
                              hnodeE hnodeC
                        | condElse =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE hnodeC
                            exact compileCheck_enforce_callReturn_intervals_disjoint
                              (scope := scope)
                              (hsrc₁ := hthen)
                              (hsrc₂ := helse)
                              (Δ₁ := Δ)
                              (Δ₂ := Δ)
                              (P₁ := P)
                              (P₂ := P)
                              (n₁ := n)
                              (n₂ := (compileCheck scope hthen Δ P n).2)
                              (pE := pE)
                              (hdisjoint := Nat.le_refl _)
                              hnodeE hnodeC
                        | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                | condElse =>
                    cases exprPathC with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                    | cons childC restC =>
                        cases childC with
                        | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | condTest =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                            cases restC <;> simp [CheckedExpr.nodeAt] at hnodeC
                        | condThen =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE hnodeC
                            have hneq :=
                              compileCheck_callReturn_enforce_intervals_disjoint
                                (scope := scope)
                                (hsrc₁ := hthen)
                                (hsrc₂ := helse)
                                (Δ₁ := Δ)
                                (Δ₂ := Δ)
                                (P₁ := P)
                                (P₂ := P)
                                (n₁ := n)
                                (n₂ := (compileCheck scope hthen Δ P n).2)
                                (hdisjoint := Nat.le_refl _)
                                (exprPathC := restC)
                                (exprPathE := restE)
                                (calleeC := calleeC)
                                (argC := argC)
                                (paramTyC := paramTyC)
                                (returnTyC := returnTyC)
                                (labelsC := labelsC)
                                (pC := pC)
                                (eE := eE)
                                (c := c)
                                (labelsE := labelsE)
                                (pE := pE)
                                hnodeC hnodeE
                            intro hsite
                            exact hneq hsite.symm
                        | condElse =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE hnodeC
                            exact ihElse
                              (scope := scope)
                              (Δ := Δ)
                              (P := P)
                              (n := (compileCheck scope hthen Δ P n).2)
                              (exprPathE := restE)
                              (exprPathC := restC)
                              (eE := eE)
                              (c := c)
                              (labelsE := labelsE)
                              (pE := pE)
                              (calleeC := calleeC)
                              (argC := argC)
                              (paramTyC := paramTyC)
                              (returnTyC := returnTyC)
                              (labelsC := labelsC)
                              (pC := pC)
                              hnodeE hnodeC
                        | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
                | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE

theorem compileCheck_dynAttr_callReturn_disjoint
    (scope : LabelScope) (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    ∀ {Δ P n exprPathD exprPathC eD attr ℓD
       calleeC argC}
      {paramTyC returnTyC : CheckedTarget}
      {labelsC : BoundaryLabels (compileBoundaryTarget returnTyC)}
      {pC : BoundaryPath (compileBoundaryTarget returnTyC)},
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPathD =
        some (.dynAttrAccess eD attr ℓD) →
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPathC =
        some (.call calleeC argC paramTyC returnTyC labelsC) →
      ℓD.site ≠ (labelsC.at pC).site := by
  intro Δ P n exprPathD exprPathC eD attr ℓD calleeC argC paramTyC returnTyC labelsC pC
  induction hsrc generalizing scope Δ P n exprPathD exprPathC eD attr ℓD
      calleeC argC paramTyC returnTyC labelsC pC with
  | var | constNone | constTrue | constFalse | new | isInstance =>
      cases exprPathD with
      | nil =>
          intro hnodeD
          simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
      | cons childD restD =>
          intro hnodeD hnodeC
          cases childD <;> simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
          case enforceBody =>
            cases restD <;> simp [CheckedExpr.nodeAt] at hnodeD
  | attrAccess hbase _ ih =>
      cases exprPathD with
      | nil =>
          intro hnodeD
          simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
      | cons childD restD =>
          intro hnodeD hnodeC
          cases childD with
          | attrBase => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
          | callCallee => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
          | callArg => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
          | condTest => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
          | condThen => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
          | condElse => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
          | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
          | enforceBody =>
              cases restD with
              | nil =>
                  simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
                  rcases hnodeD with ⟨rfl, rfl, rfl⟩
                  cases exprPathC with
                  | nil =>
                      simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | cons childC restC =>
                      cases childC with
                      | attrBase => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                      | callCallee => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                      | callArg => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                      | condTest => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                      | condThen => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                      | condElse => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                      | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                      | enforceBody =>
                          cases restC with
                          | nil =>
                              simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                          | cons childC' tailC =>
                              cases childC' <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                              case dynAttrBase =>
                                  obtain ⟨_, hbaseHi⟩ :=
                                    compileCheck_call_return_site_interval
                                      (scope := scope)
                                      (hsrc := hbase)
                                      (Δ := Δ)
                                      (P := .any)
                                      (n := n)
                                      (exprPath := tailC)
                                      (callee := calleeC)
                                      (arg := argC)
                                      (paramTy := paramTyC)
                                      (returnTy := returnTyC)
                                      (labels := labelsC)
                                      pC
                                      hnodeC
                                  intro hsite
                                  simp at hsite
                                  omega
              | cons childD' tailD =>
                  cases childD' with
                  | attrBase => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
                  | callCallee => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
                  | callArg => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
                  | condTest => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
                  | condThen => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
                  | condElse => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
                  | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
                  | dynAttrBase =>
                      cases exprPathC with
                      | nil =>
                          simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                      | cons childC restC =>
                          cases childC with
                          | attrBase => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                          | callCallee => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                          | callArg => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                          | condTest => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                          | condThen => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                          | condElse => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                          | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                          | enforceBody =>
                              cases restC with
                              | nil =>
                                  simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                              | cons childC' tailC =>
                                  cases childC' <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeC
                                  case dynAttrBase =>
                                      exact ih
                                        (scope := scope)
                                        (Δ := Δ)
                                        (P := .any)
                                        (n := n)
                                        (exprPathD := tailD)
                                        (exprPathC := tailC)
                                        (eD := eD)
                                        (attr := attr)
                                        (ℓD := ℓD)
                                        (calleeC := calleeC)
                                        (argC := argC)
                                        (paramTyC := paramTyC)
                                        (returnTyC := returnTyC)
                                        (labelsC := labelsC)
                                        (pC := pC)
                                        hnodeD hnodeC
  | call hcallee harg _ _ _ _ ihC ihA =>
      rename_i Γ' calleeExpr calleeSrcTy argExpr argSrcTy R hcallee_callable hcallee_wf harg_wf hcall
      let D : GTy := callParamTarget gct argSrcTy
      cases exprPathD with
      | nil =>
          intro hnodeD
          simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
      | cons childD restD =>
          intro hnodeD hnodeC
          cases childD with
          | attrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
          | condTest => simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
          | condThen => simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
          | condElse => simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
          | enforceBody => simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
          | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
          | callCallee =>
              cases exprPathC with
              | nil =>
                  obtain ⟨_, hcalleeHi⟩ :=
                    compileCheck_dynAttr_site_interval
                      (scope := scope)
                      (hsrc := hcallee)
                      (Δ := Δ)
                      (P := .callable D P)
                      (n := n)
                      (exprPath := restD)
                      (e' := eD)
                      (attr := attr)
                      (ℓ := ℓD)
                      hnodeD
                  have hargMono :
                      (compileCheck scope hcallee Δ (.callable D P) n).2 ≤
                        (compileCheck scope harg Δ D
                          (compileCheck scope hcallee Δ (.callable D P) n).2).2 :=
                    compileCheck_counter_monotone
                      (scope := scope)
                      (hsrc := harg)
                      (Δ := Δ)
                      (P := D)
                      (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
                  have hrootLo :=
                    compileCheck_call_root_site_lower_bound
                      (scope := scope)
                      (hcallee := hcallee)
                      (harg := harg)
                      (hcallee_callable := hcallee_callable)
                      (hcallee_wf := hcallee_wf)
                      (harg_wf := harg_wf)
                      (hcall := hcall)
                      (Δ := Δ)
                      (P := P)
                      (n := n)
                      (callee := calleeC)
                      (arg := argC)
                      (paramTy := paramTyC)
                      (returnTy := returnTyC)
                      (labels := labelsC)
                      pC
                      hnodeC
                  have hrootLo' :
                      (compileCheck scope harg Δ D
                        (compileCheck scope hcallee Δ (.callable D P) n).2).2 ≤
                        (labelsC.at pC).site := by
                    simpa [D] using hrootLo
                  intro hsite
                  rw [← hsite] at hrootLo'
                  omega
              | cons childC restC =>
                  cases childC with
                  | attrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | condTest => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | condThen => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | condElse => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | enforceBody => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | callCallee =>
                      simp [compileCheck, CheckedExpr.nodeAt] at hnodeD hnodeC
                      exact ihC
                        (scope := scope)
                        (Δ := Δ)
                        (P := .callable D P)
                        (n := n)
                        (exprPathD := restD)
                        (exprPathC := restC)
                        (eD := eD)
                        (attr := attr)
                        (ℓD := ℓD)
                        (calleeC := calleeC)
                        (argC := argC)
                        (paramTyC := paramTyC)
                        (returnTyC := returnTyC)
                        (labelsC := labelsC)
                        (pC := pC)
                        hnodeD hnodeC
                  | callArg =>
                      simp [compileCheck, CheckedExpr.nodeAt] at hnodeD hnodeC
                      exact compileCheck_dynAttr_callReturn_intervals_disjoint
                        (scope := scope)
                        (hsrc₁ := hcallee)
                        (hsrc₂ := harg)
                        (Δ₁ := Δ)
                        (Δ₂ := Δ)
                        (P₁ := .callable D P)
                        (P₂ := D)
                        (n₁ := n)
                        (n₂ := (compileCheck scope hcallee Δ (.callable D P) n).2)
                        (hdisjoint := Nat.le_refl _)
                        hnodeD hnodeC
          | callArg =>
              cases exprPathC with
              | nil =>
                  obtain ⟨_, hargHi⟩ :=
                    compileCheck_dynAttr_site_interval
                      (scope := scope)
                      (hsrc := harg)
                      (Δ := Δ)
                      (P := D)
                      (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
                      (exprPath := restD)
                      (e' := eD)
                      (attr := attr)
                      (ℓ := ℓD)
                      hnodeD
                  have hrootLo :=
                    compileCheck_call_root_site_lower_bound
                      (scope := scope)
                      (hcallee := hcallee)
                      (harg := harg)
                      (hcallee_callable := hcallee_callable)
                      (hcallee_wf := hcallee_wf)
                      (harg_wf := harg_wf)
                      (hcall := hcall)
                      (Δ := Δ)
                      (P := P)
                      (n := n)
                      (callee := calleeC)
                      (arg := argC)
                      (paramTy := paramTyC)
                      (returnTy := returnTyC)
                      (labels := labelsC)
                      pC
                      hnodeC
                  have hrootLo' :
                      (compileCheck scope harg Δ D
                        (compileCheck scope hcallee Δ (.callable D P) n).2).2 ≤
                        (labelsC.at pC).site := by
                    simpa [D] using hrootLo
                  intro hsite
                  rw [← hsite] at hrootLo'
                  omega
              | cons childC restC =>
                  cases childC with
                  | attrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | condTest => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | condThen => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | condElse => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | enforceBody => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
                  | callCallee =>
                      simp [compileCheck, CheckedExpr.nodeAt] at hnodeD hnodeC
                      have hneq :=
                        compileCheck_callReturn_dynAttr_intervals_disjoint
                          (scope := scope)
                          (hsrc₁ := hcallee)
                          (hsrc₂ := harg)
                          (Δ₁ := Δ)
                          (Δ₂ := Δ)
                          (P₁ := .callable D P)
                          (P₂ := D)
                          (n₁ := n)
                          (n₂ := (compileCheck scope hcallee Δ (.callable D P) n).2)
                          (hdisjoint := Nat.le_refl _)
                          (exprPathC := restC)
                          (exprPathD := restD)
                          (calleeC := calleeC)
                          (argC := argC)
                          (paramTyC := paramTyC)
                          (returnTyC := returnTyC)
                          (labelsC := labelsC)
                          (pC := pC)
                          (eD := eD)
                          (attr := attr)
                          (ℓ := ℓD)
                          hnodeC hnodeD
                      intro hsite
                      exact hneq hsite.symm
                  | callArg =>
                      simp [compileCheck, CheckedExpr.nodeAt] at hnodeD hnodeC
                      exact ihA
                        (scope := scope)
                        (Δ := Δ)
                        (P := D)
                        (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
                        (exprPathD := restD)
                        (exprPathC := restC)
                        (eD := eD)
                        (attr := attr)
                        (ℓD := ℓD)
                        (calleeC := calleeC)
                        (argC := argC)
                        (paramTyC := paramTyC)
                        (returnTyC := returnTyC)
                        (labelsC := labelsC)
                        (pC := pC)
                        hnodeD hnodeC
  | cond _ htest _ hthen helse ihTest ihThen ihElse =>
      cases exprPathD with
      | nil =>
          intro hnodeD
          simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
      | cons childD restD =>
          intro hnodeD hnodeC
          cases exprPathC with
          | nil =>
              simp [compileCheck, CheckedExpr.nodeAt] at hnodeC
          | cons childC restC =>
              cases childD <;> cases childC <;> simp [compileCheck, CheckedExpr.nodeAt] at hnodeD hnodeC
              case condTest.condTest =>
                  exact ihTest
                    (scope := scope)
                    (Δ := Δ)
                    (P := .class_ boolClass)
                    (n := n)
                    (exprPathD := restD)
                    (exprPathC := restC)
                    (eD := eD)
                    (attr := attr)
                    (ℓD := ℓD)
                    (calleeC := calleeC)
                    (argC := argC)
                    (paramTyC := paramTyC)
                    (returnTyC := returnTyC)
                    (labelsC := labelsC)
                    (pC := pC)
                    hnodeD hnodeC
              case condTest.condThen =>
                  exact compileCheck_dynAttr_callReturn_intervals_disjoint
                    (scope := scope)
                    (hsrc₁ := htest)
                    (hsrc₂ := hthen)
                    (Δ₁ := Δ)
                    (Δ₂ := Δ)
                    (P₁ := .class_ boolClass)
                    (P₂ := P)
                    (n₁ := n)
                    (n₂ := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                    (hdisjoint := Nat.le_refl _)
                    hnodeD hnodeC
              case condTest.condElse =>
                  have hthenMono :
                      (compileCheck scope htest Δ (.class_ boolClass) n).2 ≤
                        (compileCheck scope hthen Δ P
                          (compileCheck scope htest Δ (.class_ boolClass) n).2).2 :=
                    compileCheck_counter_monotone
                      (scope := scope)
                      (hsrc := hthen)
                      (Δ := Δ)
                      (P := P)
                      (n := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                  exact compileCheck_dynAttr_callReturn_intervals_disjoint
                    (scope := scope)
                    (hsrc₁ := htest)
                    (hsrc₂ := helse)
                    (Δ₁ := Δ)
                    (Δ₂ := Δ)
                    (P₁ := .class_ boolClass)
                    (P₂ := P)
                    (n₁ := n)
                    (n₂ := (compileCheck scope hthen Δ P
                      (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                    (hdisjoint := hthenMono)
                    hnodeD hnodeC
              case condThen.condTest =>
                  have hneq :=
                    compileCheck_callReturn_dynAttr_intervals_disjoint
                      (scope := scope)
                      (hsrc₁ := htest)
                      (hsrc₂ := hthen)
                      (Δ₁ := Δ)
                      (Δ₂ := Δ)
                      (P₁ := .class_ boolClass)
                      (P₂ := P)
                      (n₁ := n)
                      (n₂ := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                      (hdisjoint := Nat.le_refl _)
                      (exprPathC := restC)
                      (exprPathD := restD)
                      (calleeC := calleeC)
                      (argC := argC)
                      (paramTyC := paramTyC)
                      (returnTyC := returnTyC)
                      (labelsC := labelsC)
                      (pC := pC)
                      (eD := eD)
                      (attr := attr)
                      (ℓ := ℓD)
                      hnodeC hnodeD
                  intro hsite
                  exact hneq hsite.symm
              case condThen.condThen =>
                  exact ihThen
                    (scope := scope)
                    (Δ := Δ)
                    (P := P)
                    (n := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                    (exprPathD := restD)
                    (exprPathC := restC)
                    (eD := eD)
                    (attr := attr)
                    (ℓD := ℓD)
                    (calleeC := calleeC)
                    (argC := argC)
                    (paramTyC := paramTyC)
                    (returnTyC := returnTyC)
                    (labelsC := labelsC)
                    (pC := pC)
                    hnodeD hnodeC
              case condThen.condElse =>
                  exact compileCheck_dynAttr_callReturn_intervals_disjoint
                    (scope := scope)
                    (hsrc₁ := hthen)
                    (hsrc₂ := helse)
                    (Δ₁ := Δ)
                    (Δ₂ := Δ)
                    (P₁ := P)
                    (P₂ := P)
                    (n₁ := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                    (n₂ := (compileCheck scope hthen Δ P
                      (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                    (hdisjoint := Nat.le_refl _)
                    hnodeD hnodeC
              case condElse.condTest =>
                  have hthenMono :
                      (compileCheck scope htest Δ (.class_ boolClass) n).2 ≤
                        (compileCheck scope hthen Δ P
                          (compileCheck scope htest Δ (.class_ boolClass) n).2).2 :=
                    compileCheck_counter_monotone
                      (scope := scope)
                      (hsrc := hthen)
                      (Δ := Δ)
                      (P := P)
                      (n := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                  have hneq :=
                    compileCheck_callReturn_dynAttr_intervals_disjoint
                      (scope := scope)
                      (hsrc₁ := htest)
                      (hsrc₂ := helse)
                      (Δ₁ := Δ)
                      (Δ₂ := Δ)
                      (P₁ := .class_ boolClass)
                      (P₂ := P)
                      (n₁ := n)
                      (n₂ := (compileCheck scope hthen Δ P
                        (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                      (hdisjoint := hthenMono)
                      (exprPathC := restC)
                      (exprPathD := restD)
                      (calleeC := calleeC)
                      (argC := argC)
                      (paramTyC := paramTyC)
                      (returnTyC := returnTyC)
                      (labelsC := labelsC)
                      (pC := pC)
                      (eD := eD)
                      (attr := attr)
                      (ℓ := ℓD)
                      hnodeC hnodeD
                  intro hsite
                  exact hneq hsite.symm
              case condElse.condThen =>
                  have hneq :=
                    compileCheck_callReturn_dynAttr_intervals_disjoint
                      (scope := scope)
                      (hsrc₁ := hthen)
                      (hsrc₂ := helse)
                      (Δ₁ := Δ)
                      (Δ₂ := Δ)
                      (P₁ := P)
                      (P₂ := P)
                      (n₁ := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                      (n₂ := (compileCheck scope hthen Δ P
                        (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                      (hdisjoint := Nat.le_refl _)
                      (exprPathC := restC)
                      (exprPathD := restD)
                      (calleeC := calleeC)
                      (argC := argC)
                      (paramTyC := paramTyC)
                      (returnTyC := returnTyC)
                      (labelsC := labelsC)
                      (pC := pC)
                      (eD := eD)
                      (attr := attr)
                      (ℓ := ℓD)
                      hnodeC hnodeD
                  intro hsite
                  exact hneq hsite.symm
              case condElse.condElse =>
                  exact ihElse
                    (scope := scope)
                    (Δ := Δ)
                    (P := P)
                    (n := (compileCheck scope hthen Δ P
                      (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                    (exprPathD := restD)
                    (exprPathC := restC)
                    (eD := eD)
                    (attr := attr)
                    (ℓD := ℓD)
                    (calleeC := calleeC)
                    (argC := argC)
                    (paramTyC := paramTyC)
                    (returnTyC := returnTyC)
                    (labelsC := labelsC)
                    (pC := pC)
                    hnodeD hnodeC
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
      rename_i b C cls thenBranch thenSrcTy elseBranch elseSrcTy Γ' x
      cases hΔ : Δ.lookup x with
      | none =>
          cases exprPathD with
          | nil =>
              intro hnodeD
              simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeD
          | cons childD restD =>
              intro hnodeD hnodeC
              cases childD with
              | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeD
              | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeD
              | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeD
              | condTest =>
                  simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeD
                  cases restD <;> simp [CheckedExpr.nodeAt] at hnodeD
              | condThen =>
                  cases exprPathC with
                  | nil =>
                      simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                  | cons childC restC =>
                      cases childC with
                      | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | condTest =>
                          simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                          cases restC <;> simp [CheckedExpr.nodeAt] at hnodeC
                      | condThen =>
                          simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeD hnodeC
                          exact ihThen
                            (scope := scope)
                            (Δ := Δ)
                            (P := P)
                            (n := n)
                            (exprPathD := restD)
                            (exprPathC := restC)
                            (eD := eD)
                            (attr := attr)
                            (ℓD := ℓD)
                            (calleeC := calleeC)
                            (argC := argC)
                            (paramTyC := paramTyC)
                            (returnTyC := returnTyC)
                            (labelsC := labelsC)
                            (pC := pC)
                            hnodeD hnodeC
                      | condElse =>
                          simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeD hnodeC
                          exact compileCheck_dynAttr_callReturn_intervals_disjoint
                            (scope := scope)
                            (hsrc₁ := hthen)
                            (hsrc₂ := helse)
                            (Δ₁ := Δ)
                            (Δ₂ := Δ)
                            (P₁ := P)
                            (P₂ := P)
                            (n₁ := n)
                            (n₂ := (compileCheck scope hthen Δ P n).2)
                            (hdisjoint := Nat.le_refl _)
                            hnodeD hnodeC
                      | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
              | condElse =>
                  cases exprPathC with
                  | nil =>
                      simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                  | cons childC restC =>
                      cases childC with
                      | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | condTest =>
                          simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                          cases restC <;> simp [CheckedExpr.nodeAt] at hnodeC
                      | condThen =>
                          simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeD hnodeC
                          have hneq :=
                            compileCheck_callReturn_dynAttr_intervals_disjoint
                              (scope := scope)
                              (hsrc₁ := hthen)
                              (hsrc₂ := helse)
                              (Δ₁ := Δ)
                              (Δ₂ := Δ)
                              (P₁ := P)
                              (P₂ := P)
                              (n₁ := n)
                              (n₂ := (compileCheck scope hthen Δ P n).2)
                              (hdisjoint := Nat.le_refl _)
                              (exprPathC := restC)
                              (exprPathD := restD)
                              (calleeC := calleeC)
                              (argC := argC)
                              (paramTyC := paramTyC)
                              (returnTyC := returnTyC)
                              (labelsC := labelsC)
                              (pC := pC)
                              (eD := eD)
                              (attr := attr)
                              (ℓ := ℓD)
                              hnodeC hnodeD
                          intro hsite
                          exact hneq hsite.symm
                      | condElse =>
                          simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeD hnodeC
                          exact ihElse
                            (scope := scope)
                            (Δ := Δ)
                            (P := P)
                            (n := (compileCheck scope hthen Δ P n).2)
                            (exprPathD := restD)
                            (exprPathC := restC)
                            (eD := eD)
                            (attr := attr)
                            (ℓD := ℓD)
                            (calleeC := calleeC)
                            (argC := argC)
                            (paramTyC := paramTyC)
                            (returnTyC := returnTyC)
                            (labelsC := labelsC)
                            (pC := pC)
                            hnodeD hnodeC
                      | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
                      | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeC
              | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeD
              | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeD
      | some T =>
          by_cases href : CheckedBranchRefineOk gct T C
          · cases exprPathD with
            | nil =>
                intro hnodeD
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
            | cons childD restD =>
                intro hnodeD hnodeC
                cases childD with
                | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                | condTest =>
                    simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                    cases restD <;> simp [CheckedExpr.nodeAt] at hnodeD
                | condThen =>
                    cases exprPathC with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                    | cons childC restC =>
                        cases childC with
                        | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | condTest =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                            cases restC <;> simp [CheckedExpr.nodeAt] at hnodeC
                        | condThen =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD hnodeC
                            exact ihThen
                              (scope := scope)
                              (Δ := Δ.update x (.intersection T (.class_ C)))
                              (P := P)
                              (n := n)
                              (exprPathD := restD)
                              (exprPathC := restC)
                              (eD := eD)
                              (attr := attr)
                              (ℓD := ℓD)
                              (calleeC := calleeC)
                              (argC := argC)
                              (paramTyC := paramTyC)
                              (returnTyC := returnTyC)
                              (labelsC := labelsC)
                              (pC := pC)
                              hnodeD hnodeC
                        | condElse =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD hnodeC
                            exact compileCheck_dynAttr_callReturn_intervals_disjoint
                              (scope := scope)
                              (hsrc₁ := hthen)
                              (hsrc₂ := helse)
                              (Δ₁ := Δ.update x (.intersection T (.class_ C)))
                              (Δ₂ := Δ.update x (.intersection T (.negClass C)))
                              (P₁ := P)
                              (P₂ := P)
                              (n₁ := n)
                              (n₂ := (compileCheck scope hthen
                                (Δ.update x (.intersection T (.class_ C))) P n).2)
                              (hdisjoint := Nat.le_refl _)
                              hnodeD hnodeC
                        | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                | condElse =>
                    cases exprPathC with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                    | cons childC restC =>
                        cases childC with
                        | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | condTest =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                            cases restC <;> simp [CheckedExpr.nodeAt] at hnodeC
                        | condThen =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD hnodeC
                            have hneq :=
                              compileCheck_callReturn_dynAttr_intervals_disjoint
                                (scope := scope)
                                (hsrc₁ := hthen)
                                (hsrc₂ := helse)
                                (Δ₁ := Δ.update x (.intersection T (.class_ C)))
                                (Δ₂ := Δ.update x (.intersection T (.negClass C)))
                                (P₁ := P)
                                (P₂ := P)
                                (n₁ := n)
                                (n₂ := (compileCheck scope hthen
                                  (Δ.update x (.intersection T (.class_ C))) P n).2)
                                (hdisjoint := Nat.le_refl _)
                                (exprPathC := restC)
                                (exprPathD := restD)
                                (calleeC := calleeC)
                                (argC := argC)
                                (paramTyC := paramTyC)
                                (returnTyC := returnTyC)
                                (labelsC := labelsC)
                                (pC := pC)
                                (eD := eD)
                                (attr := attr)
                                (ℓ := ℓD)
                                hnodeC hnodeD
                            intro hsite
                            exact hneq hsite.symm
                        | condElse =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD hnodeC
                            exact ihElse
                              (scope := scope)
                              (Δ := Δ.update x (.intersection T (.negClass C)))
                              (P := P)
                              (n := (compileCheck scope hthen
                                (Δ.update x (.intersection T (.class_ C))) P n).2)
                              (exprPathD := restD)
                              (exprPathC := restC)
                              (eD := eD)
                              (attr := attr)
                              (ℓD := ℓD)
                              (calleeC := calleeC)
                              (argC := argC)
                              (paramTyC := paramTyC)
                              (returnTyC := returnTyC)
                              (labelsC := labelsC)
                              (pC := pC)
                              hnodeD hnodeC
                        | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
          · cases exprPathD with
            | nil =>
                intro hnodeD
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
            | cons childD restD =>
                intro hnodeD hnodeC
                cases childD with
                | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                | condTest =>
                    simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                    cases restD <;> simp [CheckedExpr.nodeAt] at hnodeD
                | condThen =>
                    cases exprPathC with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                    | cons childC restC =>
                        cases childC with
                        | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | condTest =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                            cases restC <;> simp [CheckedExpr.nodeAt] at hnodeC
                        | condThen =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD hnodeC
                            exact ihThen
                              (scope := scope)
                              (Δ := Δ)
                              (P := P)
                              (n := n)
                              (exprPathD := restD)
                              (exprPathC := restC)
                              (eD := eD)
                              (attr := attr)
                              (ℓD := ℓD)
                              (calleeC := calleeC)
                              (argC := argC)
                              (paramTyC := paramTyC)
                              (returnTyC := returnTyC)
                              (labelsC := labelsC)
                              (pC := pC)
                              hnodeD hnodeC
                        | condElse =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD hnodeC
                            exact compileCheck_dynAttr_callReturn_intervals_disjoint
                              (scope := scope)
                              (hsrc₁ := hthen)
                              (hsrc₂ := helse)
                              (Δ₁ := Δ)
                              (Δ₂ := Δ)
                              (P₁ := P)
                              (P₂ := P)
                              (n₁ := n)
                              (n₂ := (compileCheck scope hthen Δ P n).2)
                              (hdisjoint := Nat.le_refl _)
                              hnodeD hnodeC
                        | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                | condElse =>
                    cases exprPathC with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                    | cons childC restC =>
                        cases childC with
                        | attrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callCallee => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | callArg => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | condTest =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                            cases restC <;> simp [CheckedExpr.nodeAt] at hnodeC
                        | condThen =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD hnodeC
                            have hneq :=
                              compileCheck_callReturn_dynAttr_intervals_disjoint
                                (scope := scope)
                                (hsrc₁ := hthen)
                                (hsrc₂ := helse)
                                (Δ₁ := Δ)
                                (Δ₂ := Δ)
                                (P₁ := P)
                                (P₂ := P)
                                (n₁ := n)
                                (n₂ := (compileCheck scope hthen Δ P n).2)
                                (hdisjoint := Nat.le_refl _)
                                (exprPathC := restC)
                                (exprPathD := restD)
                                (calleeC := calleeC)
                                (argC := argC)
                                (paramTyC := paramTyC)
                                (returnTyC := returnTyC)
                                (labelsC := labelsC)
                                (pC := pC)
                                (eD := eD)
                                (attr := attr)
                                (ℓ := ℓD)
                                hnodeC hnodeD
                            intro hsite
                            exact hneq hsite.symm
                        | condElse =>
                            simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD hnodeC
                            exact ihElse
                              (scope := scope)
                              (Δ := Δ)
                              (P := P)
                              (n := (compileCheck scope hthen Δ P n).2)
                              (exprPathD := restD)
                              (exprPathC := restC)
                              (eD := eD)
                              (attr := attr)
                              (ℓD := ℓD)
                              (calleeC := calleeC)
                              (argC := argC)
                              (paramTyC := paramTyC)
                              (returnTyC := returnTyC)
                              (labelsC := labelsC)
                              (pC := pC)
                              hnodeD hnodeC
                        | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                        | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeC
                | enforceBody => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
