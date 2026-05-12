import FwPython.Gradual.TypeSystem.Source.Compile.Sites.Intervals

theorem compileCheck_enforce_site_unique
    (scope : LabelScope)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    ∀ {Δ P n exprPath₁ exprPath₂ e₁ e₂ c₁ c₂ labels₁ labels₂ p₁ p₂},
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPath₁ = some (.enforce e₁ c₁ labels₁) →
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPath₂ = some (.enforce e₂ c₂ labels₂) →
      (labels₁.at p₁).site = (labels₂.at p₂).site →
      exprPath₁ = exprPath₂ ∧ HEq labels₁ labels₂ ∧ c₁ = c₂ := by
  intro Δ P n exprPath₁ exprPath₂ e₁ e₂ c₁ c₂ labels₁ labels₂ p₁ p₂
  induction hsrc generalizing scope Δ P n exprPath₁ exprPath₂ e₁ e₂ c₁ c₂ labels₁ labels₂ p₁ p₂ with
  | var | constNone | constTrue | constFalse | new | isInstance =>
      cases exprPath₁ with
      | nil =>
          intro hnode₁ hnode₂ hsite
          cases exprPath₂ with
          | nil =>
              simp [compileCheck, CheckedExpr.nodeAt] at hnode₁ hnode₂
              rcases hnode₁ with ⟨_, rfl, hlabels₁⟩
              rcases hnode₂ with ⟨_, rfl, hlabels₂⟩
              cases hlabels₁
              cases hlabels₂
              exact ⟨rfl, HEq.rfl, rfl⟩
          | cons child₂ rest₂ =>
              cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
              case enforceBody =>
                cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
      | cons child₁ rest₁ =>
          intro hnode₁
          cases child₁ <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode₁
          case enforceBody =>
            cases rest₁ <;> simp [CheckedExpr.nodeAt] at hnode₁
  | attrAccess hbase _ ih =>
      cases exprPath₁ with
      | nil =>
          intro hnode₁ hnode₂ hsite
          simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode₁
          rcases hnode₁ with ⟨_, rfl, hlabels₁⟩
          cases hlabels₁
          cases exprPath₂ with
          | nil =>
              simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode₂
              rcases hnode₂ with ⟨_, rfl, hlabels₂⟩
              cases hlabels₂
              exact ⟨rfl, HEq.rfl, rfl⟩
          | cons child₂ rest₂ =>
              cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode₂
              case enforceBody =>
                  cases rest₂ with
                  | nil =>
                      simp [CheckedExpr.nodeAt] at hnode₂
                  | cons child₂' tail₂ =>
                      cases child₂' <;> simp [CheckedExpr.nodeAt] at hnode₂
                      case dynAttrBase =>
                          have hrootLo :=
                            (mkBoundaryLabels_interval
                              (scope := scope)
                              (pol := .positive)
                              (c := compileBoundaryTarget (checkedTargetOfRuntimePublicTy P))
                              (n := (compileCheck scope hbase Δ .any n).2 + 1)
                              (p := p₁)).1
                          obtain ⟨_, hbaseHi⟩ :=
                            compileCheck_enforce_site_interval
                              (scope := scope)
                              (hsrc := hbase)
                              (Δ := Δ)
                              (P := .any)
                              (n := n)
                              (exprPath := tail₂)
                              (e' := e₂)
                              (c := c₂)
                              (labels := labels₂)
                              p₂
                              hnode₂
                          exfalso
                          rw [hsite] at hrootLo
                          omega
      | cons child₁ rest₁ =>
          intro hnode₁ hnode₂ hsite
          cases child₁ <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode₁
          case enforceBody =>
              cases rest₁ with
              | nil =>
                  simp [CheckedExpr.nodeAt] at hnode₁
              | cons child₁' tail₁ =>
                  cases child₁' <;> simp [CheckedExpr.nodeAt] at hnode₁
                  case dynAttrBase =>
                      cases exprPath₂ with
                      | nil =>
                          simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode₂
                          rcases hnode₂ with ⟨_, rfl, hlabels₂⟩
                          cases hlabels₂
                          have hrootLo :=
                            (mkBoundaryLabels_interval
                              (scope := scope)
                              (pol := .positive)
                              (c := compileBoundaryTarget (checkedTargetOfRuntimePublicTy P))
                              (n := (compileCheck scope hbase Δ .any n).2 + 1)
                              (p := p₂)).1
                          obtain ⟨_, hbaseHi⟩ :=
                            compileCheck_enforce_site_interval
                              (scope := scope)
                              (hsrc := hbase)
                              (Δ := Δ)
                              (P := .any)
                              (n := n)
                              (exprPath := tail₁)
                              (e' := e₁)
                              (c := c₁)
                              (labels := labels₁)
                              p₁
                              hnode₁
                          exfalso
                          rw [← hsite] at hrootLo
                          omega
                      | cons child₂ rest₂ =>
                          cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode₂
                          case enforceBody =>
                              cases rest₂ with
                              | nil =>
                                  simp [CheckedExpr.nodeAt] at hnode₂
                              | cons child₂' tail₂ =>
                                  cases child₂' <;> simp [CheckedExpr.nodeAt] at hnode₂
                                  case dynAttrBase =>
                                      rcases ih
                                          (scope := scope)
                                          (Δ := Δ)
                                          (P := .any)
                                          (n := n)
                                          (exprPath₁ := tail₁)
                                          (exprPath₂ := tail₂)
                                          (e₁ := e₁)
                                          (e₂ := e₂)
                                          (c₁ := c₁)
                                          (c₂ := c₂)
                                          (labels₁ := labels₁)
                                          (labels₂ := labels₂)
                                          (p₁ := p₁)
                                          (p₂ := p₂)
                                          hnode₁ hnode₂ hsite with
                                        ⟨hpaths, hlabels, hc⟩
                                      cases hpaths
                                      exact ⟨rfl, hlabels, hc⟩
  | call hcallee harg _ _ _ _ ihC ihA =>
      rename_i Γ' callee calleeSrcTy arg argSrcTy R hcallee_callable hcallee_wf harg_wf hcall
      let D : GTy := callParamTarget gct argSrcTy
      cases exprPath₁ with
      | nil =>
          intro hnode₁
          simp [compileCheck, CheckedExpr.nodeAt] at hnode₁
      | cons child₁ rest₁ =>
          intro hnode₁ hnode₂ hsite
          cases exprPath₂ with
          | nil =>
              simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
          | cons child₂ rest₂ =>
              cases child₁ <;> cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode₁ hnode₂
              case callCallee.callCallee =>
                  rcases ihC
                      (scope := scope)
                      (Δ := Δ)
                      (P := .callable D P)
                      (n := n)
                      (exprPath₁ := rest₁)
                      (exprPath₂ := rest₂)
                      (e₁ := e₁)
                      (e₂ := e₂)
                      (c₁ := c₁)
                      (c₂ := c₂)
                      (labels₁ := labels₁)
                      (labels₂ := labels₂)
                      (p₁ := p₁)
                      (p₂ := p₂)
                      hnode₁ hnode₂ hsite with
                    ⟨hpaths, hlabels, hc⟩
                  cases hpaths
                  exact ⟨rfl, hlabels, hc⟩
              case callCallee.callArg =>
                  have hneq :=
                    compileCheck_intervals_disjoint
                      (scope := scope)
                      (hsrc₁ := hcallee)
                      (hsrc₂ := harg)
                      (Δ₁ := Δ)
                      (Δ₂ := Δ)
                      (P₁ := .callable D P)
                      (P₂ := D)
                      (n₁ := n)
                      (n₂ := (compileCheck scope hcallee Δ (.callable D P) n).2)
                      (p₁ := p₁)
                      (p₂ := p₂)
                      (hdisjoint := Nat.le_refl _)
                      hnode₁ hnode₂
                  exact False.elim (hneq hsite)
              case callArg.callCallee =>
                  have hneq :=
                    compileCheck_intervals_disjoint
                      (scope := scope)
                      (hsrc₁ := hcallee)
                      (hsrc₂ := harg)
                      (Δ₁ := Δ)
                      (Δ₂ := Δ)
                      (P₁ := .callable D P)
                      (P₂ := D)
                      (n₁ := n)
                      (n₂ := (compileCheck scope hcallee Δ (.callable D P) n).2)
                      (p₁ := p₂)
                      (p₂ := p₁)
                      (hdisjoint := Nat.le_refl _)
                      hnode₂ hnode₁
                  exact False.elim (hneq hsite.symm)
              case callArg.callArg =>
                  rcases ihA
                      (scope := scope)
                      (Δ := Δ)
                      (P := D)
                      (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
                      (exprPath₁ := rest₁)
                      (exprPath₂ := rest₂)
                      (e₁ := e₁)
                      (e₂ := e₂)
                      (c₁ := c₁)
                      (c₂ := c₂)
                      (labels₁ := labels₁)
                      (labels₂ := labels₂)
                      (p₁ := p₁)
                      (p₂ := p₂)
                      hnode₁ hnode₂ hsite with
                    ⟨hpaths, hlabels, hc⟩
                  cases hpaths
                  exact ⟨rfl, hlabels, hc⟩
  | cond _ htest _ hthen helse ihTest ihThen ihElse =>
      cases exprPath₁ with
      | nil =>
          intro hnode₁
          simp [compileCheck, CheckedExpr.nodeAt] at hnode₁
      | cons child₁ rest₁ =>
          intro hnode₁ hnode₂ hsite
          cases exprPath₂ with
          | nil =>
              simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
          | cons child₂ rest₂ =>
              cases child₁ <;> cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode₁ hnode₂
              case condTest.condTest =>
                  rcases ihTest
                      (scope := scope)
                      (Δ := Δ)
                      (P := .class_ boolClass)
                      (n := n)
                      (exprPath₁ := rest₁)
                      (exprPath₂ := rest₂)
                      (e₁ := e₁)
                      (e₂ := e₂)
                      (c₁ := c₁)
                      (c₂ := c₂)
                      (labels₁ := labels₁)
                      (labels₂ := labels₂)
                      (p₁ := p₁)
                      (p₂ := p₂)
                      hnode₁ hnode₂ hsite with
                    ⟨hpaths, hlabels, hc⟩
                  cases hpaths
                  exact ⟨rfl, hlabels, hc⟩
              case condTest.condThen =>
                  have hneq :=
                    compileCheck_intervals_disjoint
                      (scope := scope)
                      (hsrc₁ := htest)
                      (hsrc₂ := hthen)
                      (Δ₁ := Δ)
                      (Δ₂ := Δ)
                      (P₁ := .class_ boolClass)
                      (P₂ := P)
                      (n₁ := n)
                      (n₂ := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                      (p₁ := p₁)
                      (p₂ := p₂)
                      (hdisjoint := Nat.le_refl _)
                      hnode₁ hnode₂
                  exact False.elim (hneq hsite)
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
                  have hneq :=
                    compileCheck_intervals_disjoint
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
                      (p₁ := p₁)
                      (p₂ := p₂)
                      (hdisjoint := hthenMono)
                      hnode₁ hnode₂
                  exact False.elim (hneq hsite)
              case condThen.condTest =>
                  have hneq :=
                    compileCheck_intervals_disjoint
                      (scope := scope)
                      (hsrc₁ := htest)
                      (hsrc₂ := hthen)
                      (Δ₁ := Δ)
                      (Δ₂ := Δ)
                      (P₁ := .class_ boolClass)
                      (P₂ := P)
                      (n₁ := n)
                      (n₂ := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                      (p₁ := p₂)
                      (p₂ := p₁)
                      (hdisjoint := Nat.le_refl _)
                      hnode₂ hnode₁
                  exact False.elim (hneq hsite.symm)
              case condThen.condThen =>
                  rcases ihThen
                      (scope := scope)
                      (Δ := Δ)
                      (P := P)
                      (n := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                      (exprPath₁ := rest₁)
                      (exprPath₂ := rest₂)
                      (e₁ := e₁)
                      (e₂ := e₂)
                      (c₁ := c₁)
                      (c₂ := c₂)
                      (labels₁ := labels₁)
                      (labels₂ := labels₂)
                      (p₁ := p₁)
                      (p₂ := p₂)
                      hnode₁ hnode₂ hsite with
                    ⟨hpaths, hlabels, hc⟩
                  cases hpaths
                  exact ⟨rfl, hlabels, hc⟩
              case condThen.condElse =>
                  have hneq :=
                    compileCheck_intervals_disjoint
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
                      (p₁ := p₁)
                      (p₂ := p₂)
                      (hdisjoint := Nat.le_refl _)
                      hnode₁ hnode₂
                  exact False.elim (hneq hsite)
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
                    compileCheck_intervals_disjoint
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
                      (p₁ := p₂)
                      (p₂ := p₁)
                      (hdisjoint := hthenMono)
                      hnode₂ hnode₁
                  exact False.elim (hneq hsite.symm)
              case condElse.condThen =>
                  have hneq :=
                    compileCheck_intervals_disjoint
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
                      (p₁ := p₂)
                      (p₂ := p₁)
                      (hdisjoint := Nat.le_refl _)
                      hnode₂ hnode₁
                  exact False.elim (hneq hsite.symm)
              case condElse.condElse =>
                  rcases ihElse
                      (scope := scope)
                      (Δ := Δ)
                      (P := P)
                      (n := (compileCheck scope hthen Δ P
                        (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                      (exprPath₁ := rest₁)
                      (exprPath₂ := rest₂)
                      (e₁ := e₁)
                      (e₂ := e₂)
                      (c₁ := c₁)
                      (c₂ := c₂)
                      (labels₁ := labels₁)
                      (labels₂ := labels₂)
                      (p₁ := p₁)
                      (p₂ := p₂)
                      hnode₁ hnode₂ hsite with
                    ⟨hpaths, hlabels, hc⟩
                  cases hpaths
                  exact ⟨rfl, hlabels, hc⟩
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
      rename_i b C cls thenBranch thenSrcTy elseBranch elseSrcTy Γ' x
      cases hΔ : Δ.lookup x with
      | none =>
          cases exprPath₁ with
          | nil =>
              intro hnode₁
              simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode₁
          | cons child₁ rest₁ =>
              intro hnode₁ hnode₂ hsite
              cases child₁ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode₁
              · cases rest₁ <;> simp [CheckedExpr.nodeAt] at hnode₁
              · cases exprPath₂ with
                  | nil =>
                      simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode₂
                  | cons child₂ rest₂ =>
                      cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode₂
                      · cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
                      · rcases ihThen
                            (scope := scope)
                            (Δ := Δ)
                            (P := P)
                            (n := n)
                            (exprPath₁ := rest₁)
                            (exprPath₂ := rest₂)
                            (e₁ := e₁)
                            (e₂ := e₂)
                            (c₁ := c₁)
                            (c₂ := c₂)
                            (labels₁ := labels₁)
                            (labels₂ := labels₂)
                            (p₁ := p₁)
                            (p₂ := p₂)
                            hnode₁ hnode₂ hsite with
                          ⟨hpaths, hlabels, hc⟩
                        cases hpaths
                        exact ⟨rfl, hlabels, hc⟩
                      · have hneq :=
                          compileCheck_intervals_disjoint
                            (scope := scope)
                            (hsrc₁ := hthen)
                            (hsrc₂ := helse)
                            (Δ₁ := Δ)
                            (Δ₂ := Δ)
                            (P₁ := P)
                            (P₂ := P)
                            (n₁ := n)
                            (n₂ := (compileCheck scope hthen Δ P n).2)
                            (p₁ := p₁)
                            (p₂ := p₂)
                            (hdisjoint := Nat.le_refl _)
                            hnode₁ hnode₂
                        exact False.elim (hneq hsite)
              · cases exprPath₂ with
                  | nil =>
                      simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode₂
                  | cons child₂ rest₂ =>
                      cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode₂
                      · cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
                      · have hneq :=
                          compileCheck_intervals_disjoint
                            (scope := scope)
                            (hsrc₁ := hthen)
                            (hsrc₂ := helse)
                            (Δ₁ := Δ)
                            (Δ₂ := Δ)
                            (P₁ := P)
                            (P₂ := P)
                            (n₁ := n)
                            (n₂ := (compileCheck scope hthen Δ P n).2)
                            (p₁ := p₂)
                            (p₂ := p₁)
                            (hdisjoint := Nat.le_refl _)
                            hnode₂ hnode₁
                        exact False.elim (hneq hsite.symm)
                      · rcases ihElse
                            (scope := scope)
                            (Δ := Δ)
                            (P := P)
                            (n := (compileCheck scope hthen Δ P n).2)
                            (exprPath₁ := rest₁)
                            (exprPath₂ := rest₂)
                            (e₁ := e₁)
                            (e₂ := e₂)
                            (c₁ := c₁)
                            (c₂ := c₂)
                            (labels₁ := labels₁)
                            (labels₂ := labels₂)
                            (p₁ := p₁)
                            (p₂ := p₂)
                            hnode₁ hnode₂ hsite with
                          ⟨hpaths, hlabels, hc⟩
                        cases hpaths
                        exact ⟨rfl, hlabels, hc⟩
      | some T =>
          by_cases href : CheckedBranchRefineOk gct T C
          · cases exprPath₁ with
            | nil =>
                intro hnode₁
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₁
            | cons child₁ rest₁ =>
                intro hnode₁ hnode₂ hsite
                cases child₁ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₁
                · cases rest₁ <;> simp [CheckedExpr.nodeAt] at hnode₁
                · cases exprPath₂ with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                    | cons child₂ rest₂ =>
                        cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                        · cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
                        · rcases ihThen
                              (scope := scope)
                              (Δ := Δ.update x (.intersection T (.class_ C)))
                              (P := P)
                              (n := n)
                              (exprPath₁ := rest₁)
                              (exprPath₂ := rest₂)
                              (e₁ := e₁)
                              (e₂ := e₂)
                              (c₁ := c₁)
                              (c₂ := c₂)
                              (labels₁ := labels₁)
                              (labels₂ := labels₂)
                              (p₁ := p₁)
                              (p₂ := p₂)
                              hnode₁ hnode₂ hsite with
                            ⟨hpaths, hlabels, hc⟩
                          cases hpaths
                          exact ⟨rfl, hlabels, hc⟩
                        · have hneq :=
                            compileCheck_intervals_disjoint
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
                              (p₁ := p₁)
                              (p₂ := p₂)
                              (hdisjoint := Nat.le_refl _)
                              hnode₁ hnode₂
                          exact False.elim (hneq hsite)
                · cases exprPath₂ with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                    | cons child₂ rest₂ =>
                        cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                        · cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
                        · have hneq :=
                            compileCheck_intervals_disjoint
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
                              (p₁ := p₂)
                              (p₂ := p₁)
                              (hdisjoint := Nat.le_refl _)
                              hnode₂ hnode₁
                          exact False.elim (hneq hsite.symm)
                        · rcases ihElse
                              (scope := scope)
                              (Δ := Δ.update x (.intersection T (.negClass C)))
                              (P := P)
                              (n := (compileCheck scope hthen
                                (Δ.update x (.intersection T (.class_ C))) P n).2)
                              (exprPath₁ := rest₁)
                              (exprPath₂ := rest₂)
                              (e₁ := e₁)
                              (e₂ := e₂)
                              (c₁ := c₁)
                              (c₂ := c₂)
                              (labels₁ := labels₁)
                              (labels₂ := labels₂)
                              (p₁ := p₁)
                              (p₂ := p₂)
                              hnode₁ hnode₂ hsite with
                            ⟨hpaths, hlabels, hc⟩
                          cases hpaths
                          exact ⟨rfl, hlabels, hc⟩
          · cases exprPath₁ with
            | nil =>
                intro hnode₁
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₁
            | cons child₁ rest₁ =>
                intro hnode₁ hnode₂ hsite
                cases child₁ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₁
                · cases rest₁ <;> simp [CheckedExpr.nodeAt] at hnode₁
                · cases exprPath₂ with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                    | cons child₂ rest₂ =>
                        cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                        · cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
                        · rcases ihThen
                              (scope := scope)
                              (Δ := Δ)
                              (P := P)
                              (n := n)
                              (exprPath₁ := rest₁)
                              (exprPath₂ := rest₂)
                              (e₁ := e₁)
                              (e₂ := e₂)
                              (c₁ := c₁)
                              (c₂ := c₂)
                              (labels₁ := labels₁)
                              (labels₂ := labels₂)
                              (p₁ := p₁)
                              (p₂ := p₂)
                              hnode₁ hnode₂ hsite with
                            ⟨hpaths, hlabels, hc⟩
                          cases hpaths
                          exact ⟨rfl, hlabels, hc⟩
                        · have hneq :=
                            compileCheck_intervals_disjoint
                              (scope := scope)
                              (hsrc₁ := hthen)
                              (hsrc₂ := helse)
                              (Δ₁ := Δ)
                              (Δ₂ := Δ)
                              (P₁ := P)
                              (P₂ := P)
                              (n₁ := n)
                              (n₂ := (compileCheck scope hthen Δ P n).2)
                              (p₁ := p₁)
                              (p₂ := p₂)
                              (hdisjoint := Nat.le_refl _)
                              hnode₁ hnode₂
                          exact False.elim (hneq hsite)
                · cases exprPath₂ with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                    | cons child₂ rest₂ =>
                        cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                        · cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
                        · have hneq :=
                            compileCheck_intervals_disjoint
                              (scope := scope)
                              (hsrc₁ := hthen)
                              (hsrc₂ := helse)
                              (Δ₁ := Δ)
                              (Δ₂ := Δ)
                              (P₁ := P)
                              (P₂ := P)
                              (n₁ := n)
                              (n₂ := (compileCheck scope hthen Δ P n).2)
                              (p₁ := p₂)
                              (p₂ := p₁)
                              (hdisjoint := Nat.le_refl _)
                              hnode₂ hnode₁
                          exact False.elim (hneq hsite.symm)
                        · rcases ihElse
                              (scope := scope)
                              (Δ := Δ)
                              (P := P)
                              (n := (compileCheck scope hthen Δ P n).2)
                              (exprPath₁ := rest₁)
                              (exprPath₂ := rest₂)
                              (e₁ := e₁)
                              (e₂ := e₂)
                              (c₁ := c₁)
                              (c₂ := c₂)
                              (labels₁ := labels₁)
                              (labels₂ := labels₂)
                              (p₁ := p₁)
                              (p₂ := p₂)
                              hnode₁ hnode₂ hsite with
                            ⟨hpaths, hlabels, hc⟩
                          cases hpaths
                          exact ⟨rfl, hlabels, hc⟩

theorem compileCheck_call_return_path_unique
    (scope : LabelScope) (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    ∀ {Δ P n exprPath₁ exprPath₂}
      {callee₁ arg₁}
      {paramTy₁ returnTy₁ : CheckedTarget}
      {labels₁ : BoundaryLabels (compileBoundaryTarget returnTy₁)}
      {p₁ : BoundaryPath (compileBoundaryTarget returnTy₁)}
      {callee₂ arg₂}
      {paramTy₂ returnTy₂ : CheckedTarget}
      {labels₂ : BoundaryLabels (compileBoundaryTarget returnTy₂)}
      {p₂ : BoundaryPath (compileBoundaryTarget returnTy₂)},
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPath₁ =
        some (.call callee₁ arg₁ paramTy₁ returnTy₁ labels₁) →
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPath₂ =
        some (.call callee₂ arg₂ paramTy₂ returnTy₂ labels₂) →
      (labels₁.at p₁).site = (labels₂.at p₂).site →
      exprPath₁ = exprPath₂ := by
  intro Δ P n exprPath₁ exprPath₂ callee₁ arg₁ paramTy₁ returnTy₁ labels₁ p₁
    callee₂ arg₂ paramTy₂ returnTy₂ labels₂ p₂
  induction hsrc generalizing scope Δ P n exprPath₁ exprPath₂
      callee₁ arg₁ paramTy₁ returnTy₁ labels₁ p₁ callee₂ arg₂ paramTy₂ returnTy₂ labels₂ p₂ with
  | var | constNone | constTrue | constFalse | new | isInstance =>
      cases exprPath₁ with
      | nil =>
          intro hnode₁
          simp [compileCheck, CheckedExpr.nodeAt] at hnode₁
      | cons child₁ rest₁ =>
          intro hnode₁
          cases child₁ <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode₁
          case enforceBody =>
            cases rest₁ <;> simp [CheckedExpr.nodeAt] at hnode₁
  | attrAccess hbase _ ih =>
      cases exprPath₁ with
      | nil =>
          intro hnode₁
          simp [compileCheck, CheckedExpr.nodeAt] at hnode₁
      | cons child₁ rest₁ =>
          intro hnode₁ hnode₂ hsite
          cases child₁ <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode₁
          case enforceBody =>
              cases rest₁ with
              | nil =>
                  simp [CheckedExpr.nodeAt] at hnode₁
              | cons child₁' tail₁ =>
                  cases child₁' <;> simp [CheckedExpr.nodeAt] at hnode₁
                  case dynAttrBase =>
                      cases exprPath₂ with
                      | nil =>
                          simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                      | cons child₂ rest₂ =>
                          cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode₂
                          case enforceBody =>
                              cases rest₂ with
                              | nil =>
                                  simp [CheckedExpr.nodeAt] at hnode₂
                              | cons child₂' tail₂ =>
                                  cases child₂' <;> simp [CheckedExpr.nodeAt] at hnode₂
                                  case dynAttrBase =>
                                      have hpaths :=
                                        ih
                                          (scope := scope)
                                          (Δ := Δ)
                                          (P := .any)
                                          (n := n)
                                          (exprPath₁ := tail₁)
                                          (exprPath₂ := tail₂)
                                          (callee₁ := callee₁)
                                          (arg₁ := arg₁)
                                          (paramTy₁ := paramTy₁)
                                          (returnTy₁ := returnTy₁)
                                          (labels₁ := labels₁)
                                          (p₁ := p₁)
                                          (callee₂ := callee₂)
                                          (arg₂ := arg₂)
                                          (paramTy₂ := paramTy₂)
                                          (returnTy₂ := returnTy₂)
                                          (labels₂ := labels₂)
                                          (p₂ := p₂)
                                          hnode₁ hnode₂ hsite
                                      cases hpaths
                                      rfl
  | call hcallee harg _ _ _ _ ihC ihA =>
      rename_i Γ' calleeExpr calleeSrcTy argExpr argSrcTy R hcallee_callable hcallee_wf harg_wf hcall
      let D : GTy := callParamTarget gct argSrcTy
      cases exprPath₁ with
      | nil =>
          intro hnode₁ hnode₂ hsite
          cases exprPath₂ with
          | nil =>
              rfl
          | cons child₂ rest₂ =>
              cases child₂ with
              | attrBase | condTest | condThen | condElse | enforceBody | dynAttrBase =>
                  simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
              | callCallee =>
                  simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                  obtain ⟨_, hcalleeHi⟩ :=
                    compileCheck_call_return_site_interval
                      (scope := scope)
                      (hsrc := hcallee)
                      (Δ := Δ)
                      (P := .callable D P)
                      (n := n)
                      (exprPath := rest₂)
                      (callee := callee₂)
                      (arg := arg₂)
                      (paramTy := paramTy₂)
                      (returnTy := returnTy₂)
                      (labels := labels₂)
                      p₂
                      hnode₂
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
                      (callee := callee₁)
                      (arg := arg₁)
                      (paramTy := paramTy₁)
                      (returnTy := returnTy₁)
                      (labels := labels₁)
                      p₁
                      hnode₁
                  have hrootLo' :
                      (compileCheck scope harg Δ D
                        (compileCheck scope hcallee Δ (.callable D P) n).2).2 ≤
                        (labels₁.at p₁).site := by
                    simpa [D] using hrootLo
                  exfalso
                  rw [hsite] at hrootLo'
                  omega
              | callArg =>
                  simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                  obtain ⟨_, hargHi⟩ :=
                    compileCheck_call_return_site_interval
                      (scope := scope)
                      (hsrc := harg)
                      (Δ := Δ)
                      (P := D)
                      (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
                      (exprPath := rest₂)
                      (callee := callee₂)
                      (arg := arg₂)
                      (paramTy := paramTy₂)
                      (returnTy := returnTy₂)
                      (labels := labels₂)
                      p₂
                      hnode₂
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
                      (callee := callee₁)
                      (arg := arg₁)
                      (paramTy := paramTy₁)
                      (returnTy := returnTy₁)
                      (labels := labels₁)
                      p₁
                      hnode₁
                  have hrootLo' :
                      (compileCheck scope harg Δ D
                        (compileCheck scope hcallee Δ (.callable D P) n).2).2 ≤
                        (labels₁.at p₁).site := by
                    simpa [D] using hrootLo
                  exfalso
                  rw [hsite] at hrootLo'
                  omega
      | cons child₁ rest₁ =>
          intro hnode₁ hnode₂ hsite
          cases child₁ with
          | attrBase | condTest | condThen | condElse | enforceBody | dynAttrBase =>
              simp [compileCheck, CheckedExpr.nodeAt] at hnode₁
          | callCallee =>
              cases exprPath₂ with
              | nil =>
                  obtain ⟨_, hcalleeHi⟩ :=
                    compileCheck_call_return_site_interval
                      (scope := scope)
                      (hsrc := hcallee)
                      (Δ := Δ)
                      (P := .callable D P)
                      (n := n)
                      (exprPath := rest₁)
                      (callee := callee₁)
                      (arg := arg₁)
                      (paramTy := paramTy₁)
                      (returnTy := returnTy₁)
                      (labels := labels₁)
                      p₁
                      hnode₁
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
                      (callee := callee₂)
                      (arg := arg₂)
                      (paramTy := paramTy₂)
                      (returnTy := returnTy₂)
                      (labels := labels₂)
                      p₂
                      hnode₂
                  have hrootLo' :
                      (compileCheck scope harg Δ D
                        (compileCheck scope hcallee Δ (.callable D P) n).2).2 ≤
                        (labels₂.at p₂).site := by
                    simpa [D] using hrootLo
                  exfalso
                  rw [← hsite] at hrootLo'
                  omega
              | cons child₂ rest₂ =>
                  cases child₂ with
                  | attrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                  | condTest => simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                  | condThen => simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                  | condElse => simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                  | enforceBody => simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                  | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                  | callCallee =>
                      simp [compileCheck, CheckedExpr.nodeAt] at hnode₁ hnode₂
                      have hpaths :=
                        ihC
                          (scope := scope)
                          (Δ := Δ)
                          (P := .callable D P)
                          (n := n)
                          (exprPath₁ := rest₁)
                          (exprPath₂ := rest₂)
                          (callee₁ := callee₁)
                          (arg₁ := arg₁)
                          (paramTy₁ := paramTy₁)
                          (returnTy₁ := returnTy₁)
                          (labels₁ := labels₁)
                          (p₁ := p₁)
                          (callee₂ := callee₂)
                          (arg₂ := arg₂)
                          (paramTy₂ := paramTy₂)
                          (returnTy₂ := returnTy₂)
                          (labels₂ := labels₂)
                          (p₂ := p₂)
                          hnode₁ hnode₂ hsite
                      cases hpaths
                      rfl
                  | callArg =>
                      simp [compileCheck, CheckedExpr.nodeAt] at hnode₁ hnode₂
                      have hneq :=
                        compileCheck_callReturn_intervals_disjoint
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
                          (exprPath₁ := rest₁)
                          (exprPath₂ := rest₂)
                          (callee₁ := callee₁)
                          (arg₁ := arg₁)
                          (paramTy₁ := paramTy₁)
                          (returnTy₁ := returnTy₁)
                          (labels₁ := labels₁)
                          (p₁ := p₁)
                          (callee₂ := callee₂)
                          (arg₂ := arg₂)
                          (paramTy₂ := paramTy₂)
                          (returnTy₂ := returnTy₂)
                          (labels₂ := labels₂)
                          (p₂ := p₂)
                          hnode₁ hnode₂
                      exfalso
                      exact hneq hsite
          | callArg =>
              cases exprPath₂ with
              | nil =>
                  obtain ⟨_, hargHi⟩ :=
                    compileCheck_call_return_site_interval
                      (scope := scope)
                      (hsrc := harg)
                      (Δ := Δ)
                      (P := D)
                      (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
                      (exprPath := rest₁)
                      (callee := callee₁)
                      (arg := arg₁)
                      (paramTy := paramTy₁)
                      (returnTy := returnTy₁)
                      (labels := labels₁)
                      p₁
                      hnode₁
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
                      (callee := callee₂)
                      (arg := arg₂)
                      (paramTy := paramTy₂)
                      (returnTy := returnTy₂)
                      (labels := labels₂)
                      p₂
                      hnode₂
                  have hrootLo' :
                      (compileCheck scope harg Δ D
                        (compileCheck scope hcallee Δ (.callable D P) n).2).2 ≤
                        (labels₂.at p₂).site := by
                    simpa [D] using hrootLo
                  exfalso
                  rw [← hsite] at hrootLo'
                  omega
              | cons child₂ rest₂ =>
                  cases child₂ with
                  | attrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                  | condTest => simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                  | condThen => simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                  | condElse => simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                  | enforceBody => simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                  | dynAttrBase => simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                  | callCallee =>
                      simp [compileCheck, CheckedExpr.nodeAt] at hnode₁ hnode₂
                      have hneq :=
                        compileCheck_callReturn_intervals_disjoint
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
                          (exprPath₁ := rest₂)
                          (exprPath₂ := rest₁)
                          (callee₁ := callee₂)
                          (arg₁ := arg₂)
                          (paramTy₁ := paramTy₂)
                          (returnTy₁ := returnTy₂)
                          (labels₁ := labels₂)
                          (p₁ := p₂)
                          (callee₂ := callee₁)
                          (arg₂ := arg₁)
                          (paramTy₂ := paramTy₁)
                          (returnTy₂ := returnTy₁)
                          (labels₂ := labels₁)
                          (p₂ := p₁)
                          hnode₂ hnode₁
                      exfalso
                      exact hneq hsite.symm
                  | callArg =>
                      simp [compileCheck, CheckedExpr.nodeAt] at hnode₁ hnode₂
                      have hpaths :=
                        ihA
                          (scope := scope)
                          (Δ := Δ)
                          (P := D)
                          (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
                          (exprPath₁ := rest₁)
                          (exprPath₂ := rest₂)
                          (callee₁ := callee₁)
                          (arg₁ := arg₁)
                          (paramTy₁ := paramTy₁)
                          (returnTy₁ := returnTy₁)
                          (labels₁ := labels₁)
                          (p₁ := p₁)
                          (callee₂ := callee₂)
                          (arg₂ := arg₂)
                          (paramTy₂ := paramTy₂)
                          (returnTy₂ := returnTy₂)
                          (labels₂ := labels₂)
                          (p₂ := p₂)
                          hnode₁ hnode₂ hsite
                      cases hpaths
                      rfl
  | cond _ htest _ hthen helse ihTest ihThen ihElse =>
      cases exprPath₁ with
      | nil =>
          intro hnode₁
          simp [compileCheck, CheckedExpr.nodeAt] at hnode₁
      | cons child₁ rest₁ =>
          intro hnode₁ hnode₂ hsite
          cases exprPath₂ with
          | nil =>
              simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
          | cons child₂ rest₂ =>
              cases child₁ <;> cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode₁ hnode₂
              case condTest.condTest =>
                  have hpaths :=
                    ihTest
                      (scope := scope)
                      (Δ := Δ)
                      (P := .class_ boolClass)
                      (n := n)
                      (exprPath₁ := rest₁)
                      (exprPath₂ := rest₂)
                      (callee₁ := callee₁)
                      (arg₁ := arg₁)
                      (paramTy₁ := paramTy₁)
                      (returnTy₁ := returnTy₁)
                      (labels₁ := labels₁)
                      (p₁ := p₁)
                      (callee₂ := callee₂)
                      (arg₂ := arg₂)
                      (paramTy₂ := paramTy₂)
                      (returnTy₂ := returnTy₂)
                      (labels₂ := labels₂)
                      (p₂ := p₂)
                      hnode₁ hnode₂ hsite
                  cases hpaths
                  rfl
              case condTest.condThen =>
                  have hneq :=
                    compileCheck_callReturn_intervals_disjoint
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
                      (exprPath₁ := rest₁)
                      (exprPath₂ := rest₂)
                      (callee₁ := callee₁)
                      (arg₁ := arg₁)
                      (paramTy₁ := paramTy₁)
                      (returnTy₁ := returnTy₁)
                      (labels₁ := labels₁)
                      (p₁ := p₁)
                      (callee₂ := callee₂)
                      (arg₂ := arg₂)
                      (paramTy₂ := paramTy₂)
                      (returnTy₂ := returnTy₂)
                      (labels₂ := labels₂)
                      (p₂ := p₂)
                      hnode₁ hnode₂
                  exfalso
                  exact hneq hsite
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
                  have hneq :=
                    compileCheck_callReturn_intervals_disjoint
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
                      (exprPath₁ := rest₁)
                      (exprPath₂ := rest₂)
                      (callee₁ := callee₁)
                      (arg₁ := arg₁)
                      (paramTy₁ := paramTy₁)
                      (returnTy₁ := returnTy₁)
                      (labels₁ := labels₁)
                      (p₁ := p₁)
                      (callee₂ := callee₂)
                      (arg₂ := arg₂)
                      (paramTy₂ := paramTy₂)
                      (returnTy₂ := returnTy₂)
                      (labels₂ := labels₂)
                      (p₂ := p₂)
                      hnode₁ hnode₂
                  exfalso
                  exact hneq hsite
              case condThen.condTest =>
                  have hneq :=
                    compileCheck_callReturn_intervals_disjoint
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
                      (exprPath₁ := rest₂)
                      (exprPath₂ := rest₁)
                      (callee₁ := callee₂)
                      (arg₁ := arg₂)
                      (paramTy₁ := paramTy₂)
                      (returnTy₁ := returnTy₂)
                      (labels₁ := labels₂)
                      (p₁ := p₂)
                      (callee₂ := callee₁)
                      (arg₂ := arg₁)
                      (paramTy₂ := paramTy₁)
                      (returnTy₂ := returnTy₁)
                      (labels₂ := labels₁)
                      (p₂ := p₁)
                      hnode₂ hnode₁
                  exfalso
                  exact hneq hsite.symm
              case condThen.condThen =>
                  have hpaths :=
                    ihThen
                      (scope := scope)
                      (Δ := Δ)
                      (P := P)
                      (n := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                      (exprPath₁ := rest₁)
                      (exprPath₂ := rest₂)
                      (callee₁ := callee₁)
                      (arg₁ := arg₁)
                      (paramTy₁ := paramTy₁)
                      (returnTy₁ := returnTy₁)
                      (labels₁ := labels₁)
                      (p₁ := p₁)
                      (callee₂ := callee₂)
                      (arg₂ := arg₂)
                      (paramTy₂ := paramTy₂)
                      (returnTy₂ := returnTy₂)
                      (labels₂ := labels₂)
                      (p₂ := p₂)
                      hnode₁ hnode₂ hsite
                  cases hpaths
                  rfl
              case condThen.condElse =>
                  have hneq :=
                    compileCheck_callReturn_intervals_disjoint
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
                      (exprPath₁ := rest₁)
                      (exprPath₂ := rest₂)
                      (callee₁ := callee₁)
                      (arg₁ := arg₁)
                      (paramTy₁ := paramTy₁)
                      (returnTy₁ := returnTy₁)
                      (labels₁ := labels₁)
                      (p₁ := p₁)
                      (callee₂ := callee₂)
                      (arg₂ := arg₂)
                      (paramTy₂ := paramTy₂)
                      (returnTy₂ := returnTy₂)
                      (labels₂ := labels₂)
                      (p₂ := p₂)
                      hnode₁ hnode₂
                  exfalso
                  exact hneq hsite
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
                    compileCheck_callReturn_intervals_disjoint
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
                      (exprPath₁ := rest₂)
                      (exprPath₂ := rest₁)
                      (callee₁ := callee₂)
                      (arg₁ := arg₂)
                      (paramTy₁ := paramTy₂)
                      (returnTy₁ := returnTy₂)
                      (labels₁ := labels₂)
                      (p₁ := p₂)
                      (callee₂ := callee₁)
                      (arg₂ := arg₁)
                      (paramTy₂ := paramTy₁)
                      (returnTy₂ := returnTy₁)
                      (labels₂ := labels₁)
                      (p₂ := p₁)
                      hnode₂ hnode₁
                  exfalso
                  exact hneq hsite.symm
              case condElse.condThen =>
                  have hneq :=
                    compileCheck_callReturn_intervals_disjoint
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
                      (exprPath₁ := rest₂)
                      (exprPath₂ := rest₁)
                      (callee₁ := callee₂)
                      (arg₁ := arg₂)
                      (paramTy₁ := paramTy₂)
                      (returnTy₁ := returnTy₂)
                      (labels₁ := labels₂)
                      (p₁ := p₂)
                      (callee₂ := callee₁)
                      (arg₂ := arg₁)
                      (paramTy₂ := paramTy₁)
                      (returnTy₂ := returnTy₁)
                      (labels₂ := labels₁)
                      (p₂ := p₁)
                      hnode₂ hnode₁
                  exfalso
                  exact hneq hsite.symm
              case condElse.condElse =>
                  have hpaths :=
                    ihElse
                      (scope := scope)
                      (Δ := Δ)
                      (P := P)
                      (n := (compileCheck scope hthen Δ P
                        (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                      (exprPath₁ := rest₁)
                      (exprPath₂ := rest₂)
                      (callee₁ := callee₁)
                      (arg₁ := arg₁)
                      (paramTy₁ := paramTy₁)
                      (returnTy₁ := returnTy₁)
                      (labels₁ := labels₁)
                      (p₁ := p₁)
                      (callee₂ := callee₂)
                      (arg₂ := arg₂)
                      (paramTy₂ := paramTy₂)
                      (returnTy₂ := returnTy₂)
                      (labels₂ := labels₂)
                      (p₂ := p₂)
                      hnode₁ hnode₂ hsite
                  cases hpaths
                  rfl
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
      rename_i b C cls thenBranch thenSrcTy elseBranch elseSrcTy Γ' x
      cases hΔ : Δ.lookup x with
      | none =>
          cases exprPath₁ with
          | nil =>
              intro hnode₁
              simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode₁
          | cons child₁ rest₁ =>
              intro hnode₁ hnode₂ hsite
              cases child₁ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode₁
              · cases rest₁ <;> simp [CheckedExpr.nodeAt] at hnode₁
              · cases exprPath₂ with
                  | nil =>
                      simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode₂
                  | cons child₂ rest₂ =>
                      cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode₂
                      · cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
                      · have hpaths :=
                          ihThen
                            (scope := scope)
                            (Δ := Δ)
                            (P := P)
                            (n := n)
                            (exprPath₁ := rest₁)
                            (exprPath₂ := rest₂)
                            (callee₁ := callee₁)
                            (arg₁ := arg₁)
                            (paramTy₁ := paramTy₁)
                            (returnTy₁ := returnTy₁)
                            (labels₁ := labels₁)
                            (p₁ := p₁)
                            (callee₂ := callee₂)
                            (arg₂ := arg₂)
                            (paramTy₂ := paramTy₂)
                            (returnTy₂ := returnTy₂)
                            (labels₂ := labels₂)
                            (p₂ := p₂)
                            hnode₁ hnode₂ hsite
                        cases hpaths
                        rfl
                      · have hneq :=
                          compileCheck_callReturn_intervals_disjoint
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
                            (exprPath₁ := rest₁)
                            (exprPath₂ := rest₂)
                            (callee₁ := callee₁)
                            (arg₁ := arg₁)
                            (paramTy₁ := paramTy₁)
                            (returnTy₁ := returnTy₁)
                            (labels₁ := labels₁)
                            (p₁ := p₁)
                            (callee₂ := callee₂)
                            (arg₂ := arg₂)
                            (paramTy₂ := paramTy₂)
                            (returnTy₂ := returnTy₂)
                            (labels₂ := labels₂)
                            (p₂ := p₂)
                            hnode₁ hnode₂
                        exfalso
                        exact hneq hsite
              · cases exprPath₂ with
                  | nil =>
                      simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode₂
                  | cons child₂ rest₂ =>
                      cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode₂
                      · cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
                      · have hneq :=
                          compileCheck_callReturn_intervals_disjoint
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
                            (exprPath₁ := rest₂)
                            (exprPath₂ := rest₁)
                            (callee₁ := callee₂)
                            (arg₁ := arg₂)
                            (paramTy₁ := paramTy₂)
                            (returnTy₁ := returnTy₂)
                            (labels₁ := labels₂)
                            (p₁ := p₂)
                            (callee₂ := callee₁)
                            (arg₂ := arg₁)
                            (paramTy₂ := paramTy₁)
                            (returnTy₂ := returnTy₁)
                            (labels₂ := labels₁)
                            (p₂ := p₁)
                            hnode₂ hnode₁
                        exfalso
                        exact hneq hsite.symm
                      · have hpaths :=
                          ihElse
                            (scope := scope)
                            (Δ := Δ)
                            (P := P)
                            (n := (compileCheck scope hthen Δ P n).2)
                            (exprPath₁ := rest₁)
                            (exprPath₂ := rest₂)
                            (callee₁ := callee₁)
                            (arg₁ := arg₁)
                            (paramTy₁ := paramTy₁)
                            (returnTy₁ := returnTy₁)
                            (labels₁ := labels₁)
                            (p₁ := p₁)
                            (callee₂ := callee₂)
                            (arg₂ := arg₂)
                            (paramTy₂ := paramTy₂)
                            (returnTy₂ := returnTy₂)
                            (labels₂ := labels₂)
                            (p₂ := p₂)
                            hnode₁ hnode₂ hsite
                        cases hpaths
                        rfl
      | some T =>
          by_cases href : CheckedBranchRefineOk gct T C
          · cases exprPath₁ with
            | nil =>
                intro hnode₁
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₁
            | cons child₁ rest₁ =>
                intro hnode₁ hnode₂ hsite
                cases child₁ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₁
                · cases rest₁ <;> simp [CheckedExpr.nodeAt] at hnode₁
                · cases exprPath₂ with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                    | cons child₂ rest₂ =>
                        cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                        · cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
                        · have hpaths :=
                            ihThen
                              (scope := scope)
                              (Δ := Δ.update x (.intersection T (.class_ C)))
                              (P := P)
                              (n := n)
                              (exprPath₁ := rest₁)
                              (exprPath₂ := rest₂)
                              (callee₁ := callee₁)
                              (arg₁ := arg₁)
                              (paramTy₁ := paramTy₁)
                              (returnTy₁ := returnTy₁)
                              (labels₁ := labels₁)
                              (p₁ := p₁)
                              (callee₂ := callee₂)
                              (arg₂ := arg₂)
                              (paramTy₂ := paramTy₂)
                              (returnTy₂ := returnTy₂)
                              (labels₂ := labels₂)
                              (p₂ := p₂)
                              hnode₁ hnode₂ hsite
                          cases hpaths
                          rfl
                        · have hneq :=
                            compileCheck_callReturn_intervals_disjoint
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
                              (exprPath₁ := rest₁)
                              (exprPath₂ := rest₂)
                              (callee₁ := callee₁)
                              (arg₁ := arg₁)
                              (paramTy₁ := paramTy₁)
                              (returnTy₁ := returnTy₁)
                              (labels₁ := labels₁)
                              (p₁ := p₁)
                              (callee₂ := callee₂)
                              (arg₂ := arg₂)
                              (paramTy₂ := paramTy₂)
                              (returnTy₂ := returnTy₂)
                              (labels₂ := labels₂)
                              (p₂ := p₂)
                              hnode₁ hnode₂
                          exfalso
                          exact hneq hsite
                · cases exprPath₂ with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                    | cons child₂ rest₂ =>
                        cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                        · cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
                        · have hneq :=
                            compileCheck_callReturn_intervals_disjoint
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
                              (exprPath₁ := rest₂)
                              (exprPath₂ := rest₁)
                              (callee₁ := callee₂)
                              (arg₁ := arg₂)
                              (paramTy₁ := paramTy₂)
                              (returnTy₁ := returnTy₂)
                              (labels₁ := labels₂)
                              (p₁ := p₂)
                              (callee₂ := callee₁)
                              (arg₂ := arg₁)
                              (paramTy₂ := paramTy₁)
                              (returnTy₂ := returnTy₁)
                              (labels₂ := labels₁)
                              (p₂ := p₁)
                              hnode₂ hnode₁
                          exfalso
                          exact hneq hsite.symm
                        · have hpaths :=
                            ihElse
                              (scope := scope)
                              (Δ := Δ.update x (.intersection T (.negClass C)))
                              (P := P)
                              (n := (compileCheck scope hthen
                                (Δ.update x (.intersection T (.class_ C))) P n).2)
                              (exprPath₁ := rest₁)
                              (exprPath₂ := rest₂)
                              (callee₁ := callee₁)
                              (arg₁ := arg₁)
                              (paramTy₁ := paramTy₁)
                              (returnTy₁ := returnTy₁)
                              (labels₁ := labels₁)
                              (p₁ := p₁)
                              (callee₂ := callee₂)
                              (arg₂ := arg₂)
                              (paramTy₂ := paramTy₂)
                              (returnTy₂ := returnTy₂)
                              (labels₂ := labels₂)
                              (p₂ := p₂)
                              hnode₁ hnode₂ hsite
                          cases hpaths
                          rfl
          · cases exprPath₁ with
            | nil =>
                intro hnode₁
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₁
            | cons child₁ rest₁ =>
                intro hnode₁ hnode₂ hsite
                cases child₁ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₁
                · cases rest₁ <;> simp [CheckedExpr.nodeAt] at hnode₁
                · cases exprPath₂ with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                    | cons child₂ rest₂ =>
                        cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                        · cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
                        · have hpaths :=
                            ihThen
                              (scope := scope)
                              (Δ := Δ)
                              (P := P)
                              (n := n)
                              (exprPath₁ := rest₁)
                              (exprPath₂ := rest₂)
                              (callee₁ := callee₁)
                              (arg₁ := arg₁)
                              (paramTy₁ := paramTy₁)
                              (returnTy₁ := returnTy₁)
                              (labels₁ := labels₁)
                              (p₁ := p₁)
                              (callee₂ := callee₂)
                              (arg₂ := arg₂)
                              (paramTy₂ := paramTy₂)
                              (returnTy₂ := returnTy₂)
                              (labels₂ := labels₂)
                              (p₂ := p₂)
                              hnode₁ hnode₂ hsite
                          cases hpaths
                          rfl
                        · have hneq :=
                            compileCheck_callReturn_intervals_disjoint
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
                              (exprPath₁ := rest₁)
                              (exprPath₂ := rest₂)
                              (callee₁ := callee₁)
                              (arg₁ := arg₁)
                              (paramTy₁ := paramTy₁)
                              (returnTy₁ := returnTy₁)
                              (labels₁ := labels₁)
                              (p₁ := p₁)
                              (callee₂ := callee₂)
                              (arg₂ := arg₂)
                              (paramTy₂ := paramTy₂)
                              (returnTy₂ := returnTy₂)
                              (labels₂ := labels₂)
                              (p₂ := p₂)
                              hnode₁ hnode₂
                          exfalso
                          exact hneq hsite
                · cases exprPath₂ with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                    | cons child₂ rest₂ =>
                        cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                        · cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
                        · have hneq :=
                            compileCheck_callReturn_intervals_disjoint
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
                              (exprPath₁ := rest₂)
                              (exprPath₂ := rest₁)
                              (callee₁ := callee₂)
                              (arg₁ := arg₂)
                              (paramTy₁ := paramTy₂)
                              (returnTy₁ := returnTy₂)
                              (labels₁ := labels₂)
                              (p₁ := p₂)
                              (callee₂ := callee₁)
                              (arg₂ := arg₁)
                              (paramTy₂ := paramTy₁)
                              (returnTy₂ := returnTy₁)
                              (labels₂ := labels₁)
                              (p₂ := p₁)
                              hnode₂ hnode₁
                          exfalso
                          exact hneq hsite.symm
                        · have hpaths :=
                            ihElse
                              (scope := scope)
                              (Δ := Δ)
                              (P := P)
                              (n := (compileCheck scope hthen Δ P n).2)
                              (exprPath₁ := rest₁)
                              (exprPath₂ := rest₂)
                              (callee₁ := callee₁)
                              (arg₁ := arg₁)
                              (paramTy₁ := paramTy₁)
                              (returnTy₁ := returnTy₁)
                              (labels₁ := labels₁)
                              (p₁ := p₁)
                              (callee₂ := callee₂)
                              (arg₂ := arg₂)
                              (paramTy₂ := paramTy₂)
                              (returnTy₂ := returnTy₂)
                              (labels₂ := labels₂)
                              (p₂ := p₂)
                              hnode₁ hnode₂ hsite
                          cases hpaths
                          rfl

theorem compileCheck_call_return_site_unique
    (scope : LabelScope) (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    ∀ {Δ P n exprPath₁ exprPath₂}
      {callee₁ arg₁}
      {paramTy₁ returnTy₁ : CheckedTarget}
      {labels₁ : BoundaryLabels (compileBoundaryTarget returnTy₁)}
      {p₁ : BoundaryPath (compileBoundaryTarget returnTy₁)}
      {callee₂ arg₂}
      {paramTy₂ returnTy₂ : CheckedTarget}
      {labels₂ : BoundaryLabels (compileBoundaryTarget returnTy₂)}
      {p₂ : BoundaryPath (compileBoundaryTarget returnTy₂)},
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPath₁ =
        some (.call callee₁ arg₁ paramTy₁ returnTy₁ labels₁) →
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPath₂ =
        some (.call callee₂ arg₂ paramTy₂ returnTy₂ labels₂) →
      (labels₁.at p₁).site = (labels₂.at p₂).site →
      exprPath₁ = exprPath₂ ∧ HEq labels₁ labels₂ ∧ returnTy₁ = returnTy₂ := by
  intro Δ P n exprPath₁ exprPath₂ callee₁ arg₁ paramTy₁ returnTy₁ labels₁ p₁
    callee₂ arg₂ paramTy₂ returnTy₂ labels₂ p₂ hnode₁ hnode₂ hsite
  have hpaths :=
    compileCheck_call_return_path_unique
      (scope := scope)
      (hsrc := hsrc)
      (Δ := Δ)
      (P := P)
      (n := n)
      (exprPath₁ := exprPath₁)
      (exprPath₂ := exprPath₂)
      (callee₁ := callee₁)
      (arg₁ := arg₁)
      (paramTy₁ := paramTy₁)
      (returnTy₁ := returnTy₁)
      (labels₁ := labels₁)
      (p₁ := p₁)
      (callee₂ := callee₂)
      (arg₂ := arg₂)
      (paramTy₂ := paramTy₂)
      (returnTy₂ := returnTy₂)
      (labels₂ := labels₂)
      (p₂ := p₂)
      hnode₁ hnode₂ hsite
  cases hpaths
  have hEq :
      CheckedExpr.call callee₁ arg₁ paramTy₁ returnTy₁ labels₁ =
        CheckedExpr.call callee₂ arg₂ paramTy₂ returnTy₂ labels₂ := by
    exact Option.some.inj (hnode₁.symm.trans hnode₂)
  obtain ⟨hret, _, _, _, hlabels⟩ := checkedExpr_call_inversion hEq
  cases hret
  cases hlabels
  exact ⟨rfl, HEq.rfl, rfl⟩
