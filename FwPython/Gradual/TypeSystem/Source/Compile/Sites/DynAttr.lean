import FwPython.Gradual.TypeSystem.Source.Compile.Sites.Intervals

theorem compileCheck_dynAttr_site_unique
    (scope : LabelScope)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    ∀ {Δ P n exprPath₁ exprPath₂ e₁ e₂ attr₁ attr₂ ℓ₁ ℓ₂},
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPath₁ = some (.dynAttrAccess e₁ attr₁ ℓ₁) →
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPath₂ = some (.dynAttrAccess e₂ attr₂ ℓ₂) →
      ℓ₁.site = ℓ₂.site →
      exprPath₁ = exprPath₂ ∧ e₁ = e₂ ∧ attr₁ = attr₂ ∧ ℓ₁ = ℓ₂ := by
  intro Δ P n exprPath₁ exprPath₂ e₁ e₂ attr₁ attr₂ ℓ₁ ℓ₂
  induction hsrc generalizing scope Δ P n exprPath₁ exprPath₂ e₁ e₂ attr₁ attr₂ ℓ₁ ℓ₂ with
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
          cases child₁ <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode₁
          case enforceBody =>
              cases rest₁ with
              | nil =>
                  cases exprPath₂ with
                  | nil =>
                      simp [compileCheck, CheckedExpr.nodeAt] at hnode₂
                  | cons child₂ rest₂ =>
                      cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode₂
                      case enforceBody =>
                          cases rest₂ with
                          | nil =>
                              simp [CheckedExpr.nodeAt, freshLabel] at hnode₁ hnode₂
                              rcases hnode₁ with ⟨rfl, rfl, rfl⟩
                              rcases hnode₂ with ⟨rfl, rfl, rfl⟩
                              exact ⟨rfl, rfl, rfl, rfl⟩
                          | cons child₂' tail₂ =>
                              cases child₂' <;> simp [CheckedExpr.nodeAt] at hnode₂
                              case dynAttrBase =>
                                  simp [CheckedExpr.nodeAt, freshLabel] at hnode₁
                                  rcases hnode₁ with ⟨rfl, rfl, rfl⟩
                                  obtain ⟨_, hhigh₂⟩ :=
                                    compileCheck_dynAttr_site_interval
                                      (scope := scope)
                                      (hsrc := hbase)
                                      (Δ := Δ)
                                      (P := .any)
                                      (n := n)
                                      (exprPath := tail₂)
                                      (e' := e₂)
                                      (attr := attr₂)
                                      (ℓ := ℓ₂)
                                      hnode₂
                                  simp at hsite
                                  omega
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
                                  rcases hnode₂ with ⟨rfl, rfl, rfl⟩
                                  obtain ⟨_, hhigh₁⟩ :=
                                    compileCheck_dynAttr_site_interval
                                      (scope := scope)
                                      (hsrc := hbase)
                                      (Δ := Δ)
                                      (P := .any)
                                      (n := n)
                                      (exprPath := tail₁)
                                      (e' := e₁)
                                      (attr := attr₁)
                                      (ℓ := ℓ₁)
                                      hnode₁
                                  simp at hsite
                                  omega
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
                                          (attr₁ := attr₁)
                                          (attr₂ := attr₂)
                                          (ℓ₁ := ℓ₁)
                                          (ℓ₂ := ℓ₂)
                                          hnode₁ hnode₂ hsite with
                                        ⟨hpaths, he, hattr, hℓ⟩
                                      cases hpaths
                                      exact ⟨rfl, he, hattr, hℓ⟩
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
                      (attr₁ := attr₁)
                      (attr₂ := attr₂)
                      (ℓ₁ := ℓ₁)
                      (ℓ₂ := ℓ₂)
                      hnode₁ hnode₂ hsite with
                    ⟨hpaths, he, hattr, hℓ⟩
                  cases hpaths
                  exact ⟨rfl, he, hattr, hℓ⟩
              case callCallee.callArg =>
                  have hneq :=
                    compileCheck_dynAttr_intervals_disjoint
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
                      hnode₁ hnode₂
                  exact False.elim (hneq hsite)
              case callArg.callCallee =>
                  have hneq :=
                    compileCheck_dynAttr_intervals_disjoint
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
                      (attr₁ := attr₁)
                      (attr₂ := attr₂)
                      (ℓ₁ := ℓ₁)
                      (ℓ₂ := ℓ₂)
                      hnode₁ hnode₂ hsite with
                    ⟨hpaths, he, hattr, hℓ⟩
                  cases hpaths
                  exact ⟨rfl, he, hattr, hℓ⟩
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
                      (attr₁ := attr₁)
                      (attr₂ := attr₂)
                      (ℓ₁ := ℓ₁)
                      (ℓ₂ := ℓ₂)
                      hnode₁ hnode₂ hsite with
                    ⟨hpaths, he, hattr, hℓ⟩
                  cases hpaths
                  exact ⟨rfl, he, hattr, hℓ⟩
              case condTest.condThen =>
                  have hneq :=
                    compileCheck_dynAttr_intervals_disjoint
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
                    compileCheck_dynAttr_intervals_disjoint
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
                      hnode₁ hnode₂
                  exact False.elim (hneq hsite)
              case condThen.condTest =>
                  have hneq :=
                    compileCheck_dynAttr_intervals_disjoint
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
                      (attr₁ := attr₁)
                      (attr₂ := attr₂)
                      (ℓ₁ := ℓ₁)
                      (ℓ₂ := ℓ₂)
                      hnode₁ hnode₂ hsite with
                    ⟨hpaths, he, hattr, hℓ⟩
                  cases hpaths
                  exact ⟨rfl, he, hattr, hℓ⟩
              case condThen.condElse =>
                  have hneq :=
                    compileCheck_dynAttr_intervals_disjoint
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
                    compileCheck_dynAttr_intervals_disjoint
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
                      hnode₂ hnode₁
                  exact False.elim (hneq hsite.symm)
              case condElse.condThen =>
                  have hneq :=
                    compileCheck_dynAttr_intervals_disjoint
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
                      (attr₁ := attr₁)
                      (attr₂ := attr₂)
                      (ℓ₁ := ℓ₁)
                      (ℓ₂ := ℓ₂)
                      hnode₁ hnode₂ hsite with
                    ⟨hpaths, he, hattr, hℓ⟩
                  cases hpaths
                  exact ⟨rfl, he, hattr, hℓ⟩
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
                            (attr₁ := attr₁)
                            (attr₂ := attr₂)
                            (ℓ₁ := ℓ₁)
                            (ℓ₂ := ℓ₂)
                            hnode₁ hnode₂ hsite with
                          ⟨hpaths, he, hattr, hℓ⟩
                        cases hpaths
                        exact ⟨rfl, he, hattr, hℓ⟩
                      · have hneq :=
                          compileCheck_dynAttr_intervals_disjoint
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
                            hnode₁ hnode₂
                        exact False.elim (hneq hsite)
              · cases exprPath₂ with
                  | nil =>
                      simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode₂
                  | cons child₂ rest₂ =>
                      cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode₂
                      · cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
                      · have hneq :=
                          compileCheck_dynAttr_intervals_disjoint
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
                            (attr₁ := attr₁)
                            (attr₂ := attr₂)
                            (ℓ₁ := ℓ₁)
                            (ℓ₂ := ℓ₂)
                            hnode₁ hnode₂ hsite with
                          ⟨hpaths, he, hattr, hℓ⟩
                        cases hpaths
                        exact ⟨rfl, he, hattr, hℓ⟩
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
                              (attr₁ := attr₁)
                              (attr₂ := attr₂)
                              (ℓ₁ := ℓ₁)
                              (ℓ₂ := ℓ₂)
                              hnode₁ hnode₂ hsite with
                            ⟨hpaths, he, hattr, hℓ⟩
                          cases hpaths
                          exact ⟨rfl, he, hattr, hℓ⟩
                        · have hneq :=
                            compileCheck_dynAttr_intervals_disjoint
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
                              hnode₁ hnode₂
                          exact False.elim (hneq hsite)
                · cases exprPath₂ with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                    | cons child₂ rest₂ =>
                        cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                        · cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
                        · have hneq :=
                            compileCheck_dynAttr_intervals_disjoint
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
                              (attr₁ := attr₁)
                              (attr₂ := attr₂)
                              (ℓ₁ := ℓ₁)
                              (ℓ₂ := ℓ₂)
                              hnode₁ hnode₂ hsite with
                            ⟨hpaths, he, hattr, hℓ⟩
                          cases hpaths
                          exact ⟨rfl, he, hattr, hℓ⟩
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
                              (attr₁ := attr₁)
                              (attr₂ := attr₂)
                              (ℓ₁ := ℓ₁)
                              (ℓ₂ := ℓ₂)
                              hnode₁ hnode₂ hsite with
                            ⟨hpaths, he, hattr, hℓ⟩
                          cases hpaths
                          exact ⟨rfl, he, hattr, hℓ⟩
                        · have hneq :=
                            compileCheck_dynAttr_intervals_disjoint
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
                              hnode₁ hnode₂
                          exact False.elim (hneq hsite)
                · cases exprPath₂ with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                    | cons child₂ rest₂ =>
                        cases child₂ <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode₂
                        · cases rest₂ <;> simp [CheckedExpr.nodeAt] at hnode₂
                        · have hneq :=
                            compileCheck_dynAttr_intervals_disjoint
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
                              (attr₁ := attr₁)
                              (attr₂ := attr₂)
                              (ℓ₁ := ℓ₁)
                              (ℓ₂ := ℓ₂)
                              hnode₁ hnode₂ hsite with
                            ⟨hpaths, he, hattr, hℓ⟩
                          cases hpaths
                          exact ⟨rfl, he, hattr, hℓ⟩

theorem compileCheck_cross_kind_site_disjoint
    (scope : LabelScope)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    ∀ {Δ P n exprPathE exprPathD eE c labels p eD attr ℓ},
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPathE = some (.enforce eE c labels) →
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPathD = some (.dynAttrAccess eD attr ℓ) →
      (labels.at p).site ≠ ℓ.site := by
  intro Δ P n exprPathE exprPathD eE c labels p eD attr ℓ
  induction hsrc generalizing scope Δ P n exprPathE exprPathD eE c labels p eD attr ℓ with
  | var | constNone | constTrue | constFalse | new | isInstance =>
      cases exprPathD with
      | nil =>
          intro hnodeE hnodeD
          simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
      | cons childD restD =>
          intro hnodeE hnodeD
          cases childD <;> simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
          case enforceBody =>
            cases restD <;> simp [CheckedExpr.nodeAt] at hnodeD
  | attrAccess hbase _ ih =>
      cases exprPathE with
      | nil =>
          intro hnodeE hnodeD
          simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
          rcases hnodeE with ⟨_, rfl, hlabels⟩
          cases hlabels
          cases exprPathD with
          | nil =>
              simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
          | cons childD restD =>
              cases childD <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
              case enforceBody =>
                  cases restD with
                  | nil =>
                      simp [CheckedExpr.nodeAt] at hnodeD
                      rcases hnodeD with ⟨rfl, rfl, rfl⟩
                      have hrootLo :=
                        (mkBoundaryLabels_interval
                          (scope := scope)
                          (pol := .positive)
                          (c := compileBoundaryTarget (checkedTargetOfRuntimePublicTy P))
                          (n := (compileCheck scope hbase Δ .any n).2 + 1)
                          (p := p)).1
                      intro hsite
                      simp at hsite
                      omega
                  | cons childD' tailD =>
                      cases childD' <;> simp [CheckedExpr.nodeAt] at hnodeD
                      case dynAttrBase =>
                          have hrootLo :=
                            (mkBoundaryLabels_interval
                              (scope := scope)
                              (pol := .positive)
                              (c := compileBoundaryTarget (checkedTargetOfRuntimePublicTy P))
                              (n := (compileCheck scope hbase Δ .any n).2 + 1)
                              (p := p)).1
                          obtain ⟨_, hbaseHi⟩ :=
                            compileCheck_dynAttr_site_interval
                              (scope := scope)
                              (hsrc := hbase)
                              (Δ := Δ)
                              (P := .any)
                              (n := n)
                              (exprPath := tailD)
                              (e' := eD)
                              (attr := attr)
                              (ℓ := ℓ)
                              hnodeD
                          intro hsite
                          rw [hsite] at hrootLo
                          omega
      | cons childE restE =>
          intro hnodeE hnodeD
          cases childE <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeE
          case enforceBody =>
              cases restE with
              | nil =>
                  simp [CheckedExpr.nodeAt] at hnodeE
              | cons childE' tailE =>
                  cases childE' <;> simp [CheckedExpr.nodeAt] at hnodeE
                  case dynAttrBase =>
                      cases exprPathD with
                      | nil =>
                          simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
                      | cons childD restD =>
                          cases childD <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnodeD
                          case enforceBody =>
                              cases restD with
                              | nil =>
                                  simp [CheckedExpr.nodeAt] at hnodeD
                                  rcases hnodeD with ⟨rfl, rfl, rfl⟩
                                  obtain ⟨_, hbaseHi⟩ :=
                                    compileCheck_enforce_site_interval
                                      (scope := scope)
                                      (hsrc := hbase)
                                      (Δ := Δ)
                                      (P := .any)
                                      (n := n)
                                      (exprPath := tailE)
                                      (e' := eE)
                                      (c := c)
                                      (labels := labels)
                                      p
                                      hnodeE
                                  intro hsite
                                  simp at hsite
                                  omega
                              | cons childD' tailD =>
                                  cases childD' <;> simp [CheckedExpr.nodeAt] at hnodeD
                                  case dynAttrBase =>
                                      exact ih
                                        (scope := scope)
                                        (Δ := Δ)
                                        (P := .any)
                                        (n := n)
                                        (exprPathE := tailE)
                                        (exprPathD := tailD)
                                        (eE := eE)
                                        (c := c)
                                        (labels := labels)
                                        (p := p)
                                        (eD := eD)
                                        (attr := attr)
                                        (ℓ := ℓ)
                                        hnodeE hnodeD
  | call hcallee harg _ _ _ _ ihC ihA =>
      rename_i Γ' callee calleeSrcTy arg argSrcTy R hcallee_callable hcallee_wf harg_wf hcall
      let D : GTy := callParamTarget gct argSrcTy
      cases exprPathE with
      | nil =>
          intro hnodeE
          simp [compileCheck, CheckedExpr.nodeAt] at hnodeE
      | cons childE restE =>
          intro hnodeE hnodeD
          cases exprPathD with
          | nil =>
              simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
          | cons childD restD =>
              cases childE <;> cases childD <;> simp [compileCheck, CheckedExpr.nodeAt] at hnodeE hnodeD
              case callCallee.callCallee =>
                  exact ihC
                    (scope := scope)
                    (Δ := Δ)
                    (P := .callable D P)
                    (n := n)
                    (exprPathE := restE)
                    (exprPathD := restD)
                    (eE := eE)
                    (c := c)
                    (labels := labels)
                    (p := p)
                    (eD := eD)
                    (attr := attr)
                    (ℓ := ℓ)
                    hnodeE hnodeD
              case callCallee.callArg =>
                  exact compileCheck_enforce_dynAttr_intervals_disjoint
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
                    hnodeE hnodeD
              case callArg.callCallee =>
                  have hneq :=
                    compileCheck_dynAttr_enforce_intervals_disjoint
                      (scope := scope)
                      (hsrc₁ := hcallee)
                      (hsrc₂ := harg)
                      (Δ₁ := Δ)
                      (Δ₂ := Δ)
                      (P₁ := .callable D P)
                      (P₂ := D)
                      (n₁ := n)
                      (n₂ := (compileCheck scope hcallee Δ (.callable D P) n).2)
                      (p := p)
                      (hdisjoint := Nat.le_refl _)
                      hnodeD hnodeE
                  intro hsite
                  exact hneq hsite.symm
              case callArg.callArg =>
                  exact ihA
                    (scope := scope)
                    (Δ := Δ)
                    (P := D)
                    (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
                    (exprPathE := restE)
                    (exprPathD := restD)
                    (eE := eE)
                    (c := c)
                    (labels := labels)
                    (p := p)
                    (eD := eD)
                    (attr := attr)
                    (ℓ := ℓ)
                    hnodeE hnodeD
  | cond _ htest _ hthen helse ihTest ihThen ihElse =>
      cases exprPathE with
      | nil =>
          intro hnodeE
          simp [compileCheck, CheckedExpr.nodeAt] at hnodeE
      | cons childE restE =>
          intro hnodeE hnodeD
          cases exprPathD with
          | nil =>
              simp [compileCheck, CheckedExpr.nodeAt] at hnodeD
          | cons childD restD =>
              cases childE <;> cases childD <;> simp [compileCheck, CheckedExpr.nodeAt] at hnodeE hnodeD
              case condTest.condTest =>
                  exact ihTest
                    (scope := scope)
                    (Δ := Δ)
                    (P := .class_ boolClass)
                    (n := n)
                    (exprPathE := restE)
                    (exprPathD := restD)
                    (eE := eE)
                    (c := c)
                    (labels := labels)
                    (p := p)
                    (eD := eD)
                    (attr := attr)
                    (ℓ := ℓ)
                    hnodeE hnodeD
              case condTest.condThen =>
                  exact compileCheck_enforce_dynAttr_intervals_disjoint
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
                    hnodeE hnodeD
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
                  exact compileCheck_enforce_dynAttr_intervals_disjoint
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
                    hnodeE hnodeD
              case condThen.condTest =>
                  have hneq :=
                    compileCheck_dynAttr_enforce_intervals_disjoint
                      (scope := scope)
                      (hsrc₁ := htest)
                      (hsrc₂ := hthen)
                      (Δ₁ := Δ)
                      (Δ₂ := Δ)
                      (P₁ := .class_ boolClass)
                      (P₂ := P)
                      (n₁ := n)
                      (n₂ := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                      (p := p)
                      (hdisjoint := Nat.le_refl _)
                      hnodeD hnodeE
                  intro hsite
                  exact hneq hsite.symm
              case condThen.condThen =>
                  exact ihThen
                    (scope := scope)
                    (Δ := Δ)
                    (P := P)
                    (n := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                    (exprPathE := restE)
                    (exprPathD := restD)
                    (eE := eE)
                    (c := c)
                    (labels := labels)
                    (p := p)
                    (eD := eD)
                    (attr := attr)
                    (ℓ := ℓ)
                    hnodeE hnodeD
              case condThen.condElse =>
                  exact compileCheck_enforce_dynAttr_intervals_disjoint
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
                    hnodeE hnodeD
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
                    compileCheck_dynAttr_enforce_intervals_disjoint
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
                      (p := p)
                      (hdisjoint := hthenMono)
                      hnodeD hnodeE
                  intro hsite
                  exact hneq hsite.symm
              case condElse.condThen =>
                  have hneq :=
                    compileCheck_dynAttr_enforce_intervals_disjoint
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
                      (p := p)
                      (hdisjoint := Nat.le_refl _)
                      hnodeD hnodeE
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
                    (exprPathD := restD)
                    (eE := eE)
                    (c := c)
                    (labels := labels)
                    (p := p)
                    (eD := eD)
                    (attr := attr)
                    (ℓ := ℓ)
                    hnodeE hnodeD
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
      rename_i b C cls thenBranch thenSrcTy elseBranch elseSrcTy Γ' x
      cases hΔ : Δ.lookup x with
      | none =>
          cases exprPathE with
          | nil =>
              intro hnodeE
              simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeE
          | cons childE restE =>
              intro hnodeE hnodeD
              cases childE <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeE
              · cases restE <;> simp [CheckedExpr.nodeAt] at hnodeE
              · cases exprPathD with
                  | nil =>
                      simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeD
                  | cons childD restD =>
                      cases childD <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeD
                      · cases restD <;> simp [CheckedExpr.nodeAt] at hnodeD
                      · exact ihThen
                          (scope := scope)
                          (Δ := Δ)
                          (P := P)
                          (n := n)
                          (exprPathE := restE)
                          (exprPathD := restD)
                          (eE := eE)
                          (c := c)
                          (labels := labels)
                          (p := p)
                          (eD := eD)
                          (attr := attr)
                          (ℓ := ℓ)
                          hnodeE hnodeD
                      · exact compileCheck_enforce_dynAttr_intervals_disjoint
                          (scope := scope)
                          (hsrc₁ := hthen)
                          (hsrc₂ := helse)
                          (Δ₁ := Δ)
                          (Δ₂ := Δ)
                          (P₁ := P)
                          (P₂ := P)
                          (n₁ := n)
                          (n₂ := (compileCheck scope hthen Δ P n).2)
                          (p := p)
                          (hdisjoint := Nat.le_refl _)
                          hnodeE hnodeD
              · cases exprPathD with
                  | nil =>
                      simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeD
                  | cons childD restD =>
                      cases childD <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnodeD
                      · cases restD <;> simp [CheckedExpr.nodeAt] at hnodeD
                      · have hneq :=
                          compileCheck_dynAttr_enforce_intervals_disjoint
                            (scope := scope)
                            (hsrc₁ := hthen)
                            (hsrc₂ := helse)
                            (Δ₁ := Δ)
                            (Δ₂ := Δ)
                            (P₁ := P)
                            (P₂ := P)
                            (n₁ := n)
                            (n₂ := (compileCheck scope hthen Δ P n).2)
                            (p := p)
                            (hdisjoint := Nat.le_refl _)
                            hnodeD hnodeE
                        intro hsite
                        exact hneq hsite.symm
                      · exact ihElse
                          (scope := scope)
                          (Δ := Δ)
                          (P := P)
                          (n := (compileCheck scope hthen Δ P n).2)
                          (exprPathE := restE)
                          (exprPathD := restD)
                          (eE := eE)
                          (c := c)
                          (labels := labels)
                          (p := p)
                          (eD := eD)
                          (attr := attr)
                          (ℓ := ℓ)
                          hnodeE hnodeD
      | some T =>
          by_cases href : CheckedBranchRefineOk gct T C
          · cases exprPathE with
            | nil =>
                intro hnodeE
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
            | cons childE restE =>
                intro hnodeE hnodeD
                cases childE <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
                · cases restE <;> simp [CheckedExpr.nodeAt] at hnodeE
                · cases exprPathD with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                    | cons childD restD =>
                        cases childD <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                        · cases restD <;> simp [CheckedExpr.nodeAt] at hnodeD
                        · exact ihThen
                            (scope := scope)
                            (Δ := Δ.update x (.intersection T (.class_ C)))
                            (P := P)
                            (n := n)
                            (exprPathE := restE)
                            (exprPathD := restD)
                            (eE := eE)
                            (c := c)
                            (labels := labels)
                            (p := p)
                            (eD := eD)
                            (attr := attr)
                            (ℓ := ℓ)
                            hnodeE hnodeD
                        · exact compileCheck_enforce_dynAttr_intervals_disjoint
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
                            (p := p)
                            (hdisjoint := Nat.le_refl _)
                            hnodeE hnodeD
                · cases exprPathD with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                    | cons childD restD =>
                        cases childD <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                        · cases restD <;> simp [CheckedExpr.nodeAt] at hnodeD
                        · have hneq :=
                            compileCheck_dynAttr_enforce_intervals_disjoint
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
                              (p := p)
                              (hdisjoint := Nat.le_refl _)
                              hnodeD hnodeE
                          intro hsite
                          exact hneq hsite.symm
                        · exact ihElse
                            (scope := scope)
                            (Δ := Δ.update x (.intersection T (.negClass C)))
                            (P := P)
                            (n := (compileCheck scope hthen
                              (Δ.update x (.intersection T (.class_ C))) P n).2)
                            (exprPathE := restE)
                            (exprPathD := restD)
                            (eE := eE)
                            (c := c)
                            (labels := labels)
                            (p := p)
                            (eD := eD)
                            (attr := attr)
                            (ℓ := ℓ)
                            hnodeE hnodeD
          · cases exprPathE with
            | nil =>
                intro hnodeE
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
            | cons childE restE =>
                intro hnodeE hnodeD
                cases childE <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeE
                · cases restE <;> simp [CheckedExpr.nodeAt] at hnodeE
                · cases exprPathD with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                    | cons childD restD =>
                        cases childD <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                        · cases restD <;> simp [CheckedExpr.nodeAt] at hnodeD
                        · exact ihThen
                            (scope := scope)
                            (Δ := Δ)
                            (P := P)
                            (n := n)
                            (exprPathE := restE)
                            (exprPathD := restD)
                            (eE := eE)
                            (c := c)
                            (labels := labels)
                            (p := p)
                            (eD := eD)
                            (attr := attr)
                            (ℓ := ℓ)
                            hnodeE hnodeD
                        · exact compileCheck_enforce_dynAttr_intervals_disjoint
                            (scope := scope)
                            (hsrc₁ := hthen)
                            (hsrc₂ := helse)
                            (Δ₁ := Δ)
                            (Δ₂ := Δ)
                            (P₁ := P)
                            (P₂ := P)
                            (n₁ := n)
                            (n₂ := (compileCheck scope hthen Δ P n).2)
                            (p := p)
                            (hdisjoint := Nat.le_refl _)
                            hnodeE hnodeD
                · cases exprPathD with
                    | nil =>
                        simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                    | cons childD restD =>
                        cases childD <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnodeD
                        · cases restD <;> simp [CheckedExpr.nodeAt] at hnodeD
                        · have hneq :=
                            compileCheck_dynAttr_enforce_intervals_disjoint
                              (scope := scope)
                              (hsrc₁ := hthen)
                              (hsrc₂ := helse)
                              (Δ₁ := Δ)
                              (Δ₂ := Δ)
                              (P₁ := P)
                              (P₂ := P)
                              (n₁ := n)
                              (n₂ := (compileCheck scope hthen Δ P n).2)
                              (p := p)
                              (hdisjoint := Nat.le_refl _)
                              hnodeD hnodeE
                          intro hsite
                          exact hneq hsite.symm
                        · exact ihElse
                            (scope := scope)
                            (Δ := Δ)
                            (P := P)
                            (n := (compileCheck scope hthen Δ P n).2)
                            (exprPathE := restE)
                            (exprPathD := restD)
                            (eE := eE)
                            (c := c)
                            (labels := labels)
                            (p := p)
                            (eD := eD)
                            (attr := attr)
                            (ℓ := ℓ)
                            hnodeE hnodeD
