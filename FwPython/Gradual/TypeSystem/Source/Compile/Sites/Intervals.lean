import FwPython.Gradual.TypeSystem.Source.Compile.Core

/-! # Label site interval and uniqueness proofs for `compileCheck` -/

theorem compileCheck_enforce_site_interval
    (scope : LabelScope)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    ∀ {Δ P n exprPath e' c labels} (p : BoundaryPath (compileBoundaryTarget c)),
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPath = some (.enforce e' c labels) →
      n ≤ (labels.at p).site ∧
        (labels.at p).site < (compileCheck scope hsrc Δ P n).2 := by
  intro Δ P n exprPath e' c labels p
  induction hsrc generalizing scope Δ P n exprPath e' c labels with
  | var | constNone | constTrue | constFalse | new | isInstance =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
          rcases hnode with ⟨_, rfl, hlabels⟩
          cases hlabels
          simpa [compileCheck] using
            (mkBoundaryLabels_interval
              (scope := scope)
              (pol := .positive)
              (c := compileBoundaryTarget (checkedTargetOfRuntimePublicTy P))
              (n := n)
              (p := p))
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case enforceBody =>
            cases rest <;> simp [CheckedExpr.nodeAt] at hnode
  | attrAccess hbase _ ih =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode
          rcases hnode with ⟨_, rfl, hlabels⟩
          cases hlabels
          have hinterval :=
            mkBoundaryLabels_interval
              (scope := scope)
              (pol := .positive)
              (c := compileBoundaryTarget (checkedTargetOfRuntimePublicTy P))
              (n := (compileCheck scope hbase Δ .any n).2 + 1)
              (p := p)
          have hbaseMono :=
            compileCheck_counter_monotone
              (scope := scope) (hsrc := hbase) (Δ := Δ) (P := .any) (n := n)
          constructor
          · omega
          · simpa [compileCheck, freshLabel] using hinterval.2
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode
          case enforceBody =>
            cases rest with
            | nil =>
                simp [CheckedExpr.nodeAt] at hnode
            | cons child' tail =>
                cases child' <;> simp [CheckedExpr.nodeAt] at hnode
                case dynAttrBase =>
                  rcases ih (scope := scope) (Δ := Δ) (P := .any) (n := n) (p := p) hnode with
                    ⟨hlow, hhigh⟩
                  constructor
                  · exact hlow
                  · simp [compileCheck, freshLabel, mkBoundaryLabels_next]
                    omega
  | call hcallee harg _ _ _ _ ihC ihA =>
      rename_i Γ' callee calleeSrcTy arg argSrcTy R hcallee_callable hcallee_wf harg_wf hcall
      let D : GTy := callParamTarget gct argSrcTy
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case callCallee =>
            rcases ihC (scope := scope) (Δ := Δ) (P := .callable D P) (n := n) (p := p) hnode with
              ⟨hlow, hhigh⟩
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
            have hhigh' :
                (labels.at p).site <
                  (compileCheck scope hcallee Δ
                    (.callable (callParamTarget gct argSrcTy) P) n).2 := by
              simpa [D] using hhigh
            have hargMono' :
                (compileCheck scope hcallee Δ
                  (.callable (callParamTarget gct argSrcTy) P) n).2 ≤
                  (compileCheck scope harg Δ (callParamTarget gct argSrcTy)
                    (compileCheck scope hcallee Δ
                      (.callable (callParamTarget gct argSrcTy) P) n).2).2 := by
              simpa [D] using hargMono
            constructor
            · exact hlow
            · simp [compileCheck]
              have hhigh := hhigh'
              have hargMono := hargMono'
              omega
          case callArg =>
              rcases ihA
                  (scope := scope)
                  (Δ := Δ)
                  (P := D)
                  (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
                  (p := p)
                  hnode with
                ⟨hlow, hhigh⟩
              have hcalleeMono :
                  n ≤ (compileCheck scope hcallee Δ (.callable D P) n).2 :=
                compileCheck_counter_monotone
                  (scope := scope)
                  (hsrc := hcallee)
                  (Δ := Δ)
                  (P := .callable D P)
                  (n := n)
              have hcalleeMono' :
                  n ≤ (compileCheck scope hcallee Δ
                    (.callable (callParamTarget gct argSrcTy) P) n).2 := by
                simpa [D] using hcalleeMono
              have hhigh' :
                  (labels.at p).site <
                    (compileCheck scope harg Δ (callParamTarget gct argSrcTy)
                      (compileCheck scope hcallee Δ
                        (.callable (callParamTarget gct argSrcTy) P) n).2).2 := by
                simpa [D] using hhigh
              have hcount :
                  0 < (compileBoundaryTarget (checkedTargetOfRuntimePublicTy P)).labelCount := by
                simpa [compileBoundaryTarget_checkedTargetOfRuntimePublicTy, BoundaryContract.labelCount]
                  using (show 0 < (compileBoundaryRaw (runtimePublicTy P)).labelCount by
                    cases runtimePublicTy P <;>
                      simp [compileBoundaryRaw, BoundaryContract.labelCount] <;> omega)
              constructor
              · omega
              · simp [compileCheck, mkBoundaryLabels_next]
                omega
  | cond _ htest _ hthen helse ihTest ihThen ihElse =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case condTest =>
            rcases ihTest (scope := scope) (Δ := Δ) (P := .class_ boolClass) (n := n) (p := p) hnode with
              ⟨hlow, hhigh⟩
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
            have helseMono :
                (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2 ≤
                  (compileCheck scope helse Δ P
                    (compileCheck scope hthen Δ P
                      (compileCheck scope htest Δ (.class_ boolClass) n).2).2).2 :=
              compileCheck_counter_monotone
                (scope := scope)
                (hsrc := helse)
                (Δ := Δ)
                (P := P)
                (n := (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
            constructor
            · exact hlow
            · simp [compileCheck]
              omega
          case condThen =>
            rcases ihThen
                (scope := scope)
                (Δ := Δ)
                (P := P)
                (n := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                (p := p)
                hnode with
              ⟨hlow, hhigh⟩
            have htestMono :=
              compileCheck_counter_monotone
                (scope := scope) (hsrc := htest) (Δ := Δ) (P := .class_ boolClass) (n := n)
            have helseMono :
                (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2 ≤
                  (compileCheck scope helse Δ P
                    (compileCheck scope hthen Δ P
                      (compileCheck scope htest Δ (.class_ boolClass) n).2).2).2 :=
              compileCheck_counter_monotone
                (scope := scope)
                (hsrc := helse)
                (Δ := Δ)
                (P := P)
                (n := (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
            constructor
            · omega
            · simp [compileCheck]
              omega
          case condElse =>
            rcases ihElse
                (scope := scope)
                (Δ := Δ)
                (P := P)
                (n := (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                (p := p)
                hnode with
              ⟨hlow, hhigh⟩
            have htestMono :=
              compileCheck_counter_monotone
                (scope := scope) (hsrc := htest) (Δ := Δ) (P := .class_ boolClass) (n := n)
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
            constructor
            · omega
            · exact hhigh
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
      rename_i b C cls thenBranch thenSrcTy elseBranch elseSrcTy Γ' x
      cases hΔ : Δ.lookup x with
      | none =>
          cases exprPath with
          | nil =>
              intro hnode
              simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
          | cons child rest =>
              intro hnode
              cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
              · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
              · rcases ihThen (scope := scope) (Δ := Δ) (P := P) (n := n) (p := p) hnode with
                    ⟨hlow, hhigh⟩
                have helseMono :
                    (compileCheck scope hthen Δ P n).2 ≤
                      (compileCheck scope helse Δ P
                        (compileCheck scope hthen Δ P n).2).2 :=
                  compileCheck_counter_monotone
                    (scope := scope)
                    (hsrc := helse)
                    (Δ := Δ)
                    (P := P)
                    (n := (compileCheck scope hthen Δ P n).2)
                refine ⟨hlow, ?_⟩
                simp [compileCheck, hΔ]; omega
              · rcases ihElse
                    (scope := scope)
                    (Δ := Δ)
                    (P := P)
                    (n := (compileCheck scope hthen Δ P n).2)
                    (p := p)
                    hnode with
                  ⟨hlow, hhigh⟩
                have hthenMono :
                    n ≤ (compileCheck scope hthen Δ P n).2 :=
                  compileCheck_counter_monotone
                    (scope := scope) (hsrc := hthen) (Δ := Δ) (P := P) (n := n)
                refine ⟨by omega, ?_⟩
                simpa [compileCheck, hΔ] using hhigh
      | some T =>
          by_cases href : CheckedBranchRefineOk gct T C
          · cases exprPath with
            | nil =>
                intro hnode
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
            | cons child rest =>
                intro hnode
                cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
                · rcases ihThen
                      (scope := scope)
                      (Δ := Δ.update x (.intersection T (.class_ C)))
                      (P := P)
                      (n := n)
                      (p := p)
                      hnode with
                    ⟨hlow, hhigh⟩
                  have helseMono :
                      (compileCheck scope hthen
                        (Δ.update x (.intersection T (.class_ C))) P n).2 ≤
                        (compileCheck scope helse
                          (Δ.update x (.intersection T (.negClass C))) P
                          (compileCheck scope hthen
                            (Δ.update x (.intersection T (.class_ C))) P n).2).2 :=
                    compileCheck_counter_monotone
                      (scope := scope)
                      (hsrc := helse)
                      (Δ := Δ.update x (.intersection T (.negClass C)))
                      (P := P)
                      (n := (compileCheck scope hthen
                        (Δ.update x (.intersection T (.class_ C))) P n).2)
                  refine ⟨hlow, ?_⟩
                  simp [compileCheck, hΔ, href]; omega
                · rcases ihElse
                      (scope := scope)
                      (Δ := Δ.update x (.intersection T (.negClass C)))
                      (P := P)
                      (n := (compileCheck scope hthen
                        (Δ.update x (.intersection T (.class_ C))) P n).2)
                      (p := p)
                      hnode with
                    ⟨hlow, hhigh⟩
                  have hthenMono :
                      n ≤
                        (compileCheck scope hthen
                          (Δ.update x (.intersection T (.class_ C))) P n).2 :=
                    compileCheck_counter_monotone
                      (scope := scope)
                      (hsrc := hthen)
                      (Δ := Δ.update x (.intersection T (.class_ C)))
                      (P := P)
                      (n := n)
                  refine ⟨by omega, ?_⟩
                  simpa [compileCheck, hΔ, href] using hhigh
          · cases exprPath with
            | nil =>
                intro hnode
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
            | cons child rest =>
                intro hnode
                cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
                · rcases ihThen (scope := scope) (Δ := Δ) (P := P) (n := n) (p := p) hnode with
                    ⟨hlow, hhigh⟩
                  have helseMono :
                      (compileCheck scope hthen Δ P n).2 ≤
                        (compileCheck scope helse Δ P
                          (compileCheck scope hthen Δ P n).2).2 :=
                    compileCheck_counter_monotone
                      (scope := scope)
                      (hsrc := helse)
                      (Δ := Δ)
                      (P := P)
                      (n := (compileCheck scope hthen Δ P n).2)
                  refine ⟨hlow, ?_⟩
                  simp [compileCheck, hΔ, href]; omega
                · rcases ihElse
                      (scope := scope)
                      (Δ := Δ)
                      (P := P)
                      (n := (compileCheck scope hthen Δ P n).2)
                      (p := p)
                      hnode with
                    ⟨hlow, hhigh⟩
                  have hthenMono :
                      n ≤ (compileCheck scope hthen Δ P n).2 :=
                    compileCheck_counter_monotone
                      (scope := scope) (hsrc := hthen) (Δ := Δ) (P := P) (n := n)
                  refine ⟨by omega, ?_⟩
                  simpa [compileCheck, hΔ, href] using hhigh

theorem compileCheck_dynAttr_site_interval
    (scope : LabelScope)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    ∀ {Δ P n exprPath e' attr ℓ},
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPath = some (.dynAttrAccess e' attr ℓ) →
      n ≤ ℓ.site ∧ ℓ.site < (compileCheck scope hsrc Δ P n).2 := by
  intro Δ P n exprPath e' attr ℓ
  induction hsrc generalizing scope Δ P n exprPath e' attr ℓ with
  | var | constNone | constTrue | constFalse | new | isInstance =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case enforceBody =>
            cases rest <;> simp [CheckedExpr.nodeAt] at hnode
  | attrAccess hbase _ ih =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode
          case enforceBody =>
            cases rest with
            | nil =>
                rcases hnode with ⟨rfl, rfl, rfl⟩
                have hbaseMono :=
                  compileCheck_counter_monotone
                    (scope := scope) (hsrc := hbase) (Δ := Δ) (P := .any) (n := n)
                constructor
                · simp
                  omega
                · simp [compileCheck, freshLabel, mkBoundaryLabels_next]
                  omega
            | cons child' tail =>
                cases child' <;> simp [CheckedExpr.nodeAt] at hnode
                case dynAttrBase =>
                  rcases ih (scope := scope) (Δ := Δ) (P := .any) (n := n) hnode with
                    ⟨hlow, hhigh⟩
                  constructor
                  · exact hlow
                  · simp [compileCheck, freshLabel, mkBoundaryLabels_next]
                    omega
  | call hcallee harg _ _ _ _ ihC ihA =>
      rename_i Γ' callee calleeSrcTy arg argSrcTy R hcallee_callable hcallee_wf harg_wf hcall
      let D : GTy := callParamTarget gct argSrcTy
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case callCallee =>
            rcases ihC (scope := scope) (Δ := Δ) (P := .callable D P) (n := n) hnode with
              ⟨hlow, hhigh⟩
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
            have hhigh' :
                ℓ.site <
                  (compileCheck scope hcallee Δ
                    (.callable (callParamTarget gct argSrcTy) P) n).2 := by
              simpa [D] using hhigh
            have hargMono' :
                (compileCheck scope hcallee Δ
                  (.callable (callParamTarget gct argSrcTy) P) n).2 ≤
                  (compileCheck scope harg Δ (callParamTarget gct argSrcTy)
                    (compileCheck scope hcallee Δ
                      (.callable (callParamTarget gct argSrcTy) P) n).2).2 := by
              simpa [D] using hargMono
            constructor
            · exact hlow
            · simp [compileCheck]
              have hhigh := hhigh'
              have hargMono := hargMono'
              omega
          case callArg =>
              rcases ihA
                  (scope := scope)
                  (Δ := Δ)
                  (P := D)
                  (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
                  hnode with
                ⟨hlow, hhigh⟩
              have hcalleeMono :
                  n ≤ (compileCheck scope hcallee Δ (.callable D P) n).2 :=
                compileCheck_counter_monotone
                  (scope := scope)
                  (hsrc := hcallee)
                  (Δ := Δ)
                  (P := .callable D P)
                  (n := n)
              have hcalleeMono' :
                  n ≤ (compileCheck scope hcallee Δ
                    (.callable (callParamTarget gct argSrcTy) P) n).2 := by
                simpa [D] using hcalleeMono
              have hhigh' :
                  ℓ.site <
                    (compileCheck scope harg Δ (callParamTarget gct argSrcTy)
                      (compileCheck scope hcallee Δ
                        (.callable (callParamTarget gct argSrcTy) P) n).2).2 := by
                simpa [D] using hhigh
              have hcount :
                  0 < (compileBoundaryTarget (checkedTargetOfRuntimePublicTy P)).labelCount := by
                simpa [compileBoundaryTarget_checkedTargetOfRuntimePublicTy, BoundaryContract.labelCount]
                  using (show 0 < (compileBoundaryRaw (runtimePublicTy P)).labelCount by
                    cases runtimePublicTy P <;>
                      simp [compileBoundaryRaw, BoundaryContract.labelCount] <;> omega)
              constructor
              · omega
              · simp [compileCheck, mkBoundaryLabels_next]
                omega
  | cond _ htest _ hthen helse ihTest ihThen ihElse =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case condTest =>
            rcases ihTest (scope := scope) (Δ := Δ) (P := .class_ boolClass) (n := n) hnode with
              ⟨hlow, hhigh⟩
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
            have helseMono :
                (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2 ≤
                  (compileCheck scope helse Δ P
                    (compileCheck scope hthen Δ P
                      (compileCheck scope htest Δ (.class_ boolClass) n).2).2).2 :=
              compileCheck_counter_monotone
                (scope := scope)
                (hsrc := helse)
                (Δ := Δ)
                (P := P)
                (n := (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
            constructor
            · exact hlow
            · simp [compileCheck]
              omega
          case condThen =>
            rcases ihThen
                (scope := scope)
                (Δ := Δ)
                (P := P)
                (n := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                hnode with
              ⟨hlow, hhigh⟩
            have htestMono :=
              compileCheck_counter_monotone
                (scope := scope) (hsrc := htest) (Δ := Δ) (P := .class_ boolClass) (n := n)
            have helseMono :
                (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2 ≤
                  (compileCheck scope helse Δ P
                    (compileCheck scope hthen Δ P
                      (compileCheck scope htest Δ (.class_ boolClass) n).2).2).2 :=
              compileCheck_counter_monotone
                (scope := scope)
                (hsrc := helse)
                (Δ := Δ)
                (P := P)
                (n := (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
            constructor
            · omega
            · simp [compileCheck]
              omega
          case condElse =>
            rcases ihElse
                (scope := scope)
                (Δ := Δ)
                (P := P)
                (n := (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                hnode with
              ⟨hlow, hhigh⟩
            have htestMono :=
              compileCheck_counter_monotone
                (scope := scope) (hsrc := htest) (Δ := Δ) (P := .class_ boolClass) (n := n)
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
            constructor
            · omega
            · exact hhigh
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
      rename_i b C cls thenBranch thenSrcTy elseBranch elseSrcTy Γ' x
      cases hΔ : Δ.lookup x with
      | none =>
          cases exprPath with
          | nil =>
              intro hnode
              simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
          | cons child rest =>
              intro hnode
              cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
              · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
              · rcases ihThen (scope := scope) (Δ := Δ) (P := P) (n := n) hnode with
                    ⟨hlow, hhigh⟩
                have helseMono :
                    (compileCheck scope hthen Δ P n).2 ≤
                      (compileCheck scope helse Δ P
                        (compileCheck scope hthen Δ P n).2).2 :=
                  compileCheck_counter_monotone
                    (scope := scope)
                    (hsrc := helse)
                    (Δ := Δ)
                    (P := P)
                    (n := (compileCheck scope hthen Δ P n).2)
                refine ⟨hlow, ?_⟩
                simp [compileCheck, hΔ]; omega
              · rcases ihElse
                    (scope := scope)
                    (Δ := Δ)
                    (P := P)
                    (n := (compileCheck scope hthen Δ P n).2)
                    hnode with
                  ⟨hlow, hhigh⟩
                have hthenMono :
                    n ≤ (compileCheck scope hthen Δ P n).2 :=
                  compileCheck_counter_monotone
                    (scope := scope) (hsrc := hthen) (Δ := Δ) (P := P) (n := n)
                refine ⟨by omega, ?_⟩
                simpa [compileCheck, hΔ] using hhigh
      | some T =>
          by_cases href : CheckedBranchRefineOk gct T C
          · cases exprPath with
            | nil =>
                intro hnode
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
            | cons child rest =>
                intro hnode
                cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
                · rcases ihThen
                      (scope := scope)
                      (Δ := Δ.update x (.intersection T (.class_ C)))
                      (P := P)
                      (n := n)
                      hnode with
                    ⟨hlow, hhigh⟩
                  have helseMono :
                      (compileCheck scope hthen
                        (Δ.update x (.intersection T (.class_ C))) P n).2 ≤
                        (compileCheck scope helse
                          (Δ.update x (.intersection T (.negClass C))) P
                          (compileCheck scope hthen
                            (Δ.update x (.intersection T (.class_ C))) P n).2).2 :=
                    compileCheck_counter_monotone
                      (scope := scope)
                      (hsrc := helse)
                      (Δ := Δ.update x (.intersection T (.negClass C)))
                      (P := P)
                      (n := (compileCheck scope hthen
                        (Δ.update x (.intersection T (.class_ C))) P n).2)
                  refine ⟨hlow, ?_⟩
                  simp [compileCheck, hΔ, href]; omega
                · rcases ihElse
                      (scope := scope)
                      (Δ := Δ.update x (.intersection T (.negClass C)))
                      (P := P)
                      (n := (compileCheck scope hthen
                        (Δ.update x (.intersection T (.class_ C))) P n).2)
                      hnode with
                    ⟨hlow, hhigh⟩
                  have hthenMono :
                      n ≤
                        (compileCheck scope hthen
                          (Δ.update x (.intersection T (.class_ C))) P n).2 :=
                    compileCheck_counter_monotone
                      (scope := scope)
                      (hsrc := hthen)
                      (Δ := Δ.update x (.intersection T (.class_ C)))
                      (P := P)
                      (n := n)
                  refine ⟨by omega, ?_⟩
                  simpa [compileCheck, hΔ, href] using hhigh
          · cases exprPath with
            | nil =>
                intro hnode
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
            | cons child rest =>
                intro hnode
                cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
                · rcases ihThen (scope := scope) (Δ := Δ) (P := P) (n := n) hnode with
                    ⟨hlow, hhigh⟩
                  have helseMono :
                      (compileCheck scope hthen Δ P n).2 ≤
                        (compileCheck scope helse Δ P
                          (compileCheck scope hthen Δ P n).2).2 :=
                    compileCheck_counter_monotone
                      (scope := scope)
                      (hsrc := helse)
                      (Δ := Δ)
                      (P := P)
                      (n := (compileCheck scope hthen Δ P n).2)
                  refine ⟨hlow, ?_⟩
                  simp [compileCheck, hΔ, href]; omega
                · rcases ihElse
                      (scope := scope)
                      (Δ := Δ)
                      (P := P)
                      (n := (compileCheck scope hthen Δ P n).2)
                      hnode with
                    ⟨hlow, hhigh⟩
                  have hthenMono :
                      n ≤ (compileCheck scope hthen Δ P n).2 :=
                    compileCheck_counter_monotone
                      (scope := scope) (hsrc := hthen) (Δ := Δ) (P := P) (n := n)
                  refine ⟨by omega, ?_⟩
                  simpa [compileCheck, hΔ, href] using hhigh

theorem compileCheck_call_return_site_interval
    (scope : LabelScope)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    ∀ {Δ P n exprPath callee arg paramTy returnTy}
      {labels : BoundaryLabels (compileBoundaryTarget returnTy)}
      (p : BoundaryPath (compileBoundaryTarget returnTy)),
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPath =
        some (.call callee arg paramTy returnTy labels) →
      n ≤ (labels.at p).site ∧
        (labels.at p).site < (compileCheck scope hsrc Δ P n).2 := by
  intro Δ P n exprPath callee arg paramTy returnTy labels p
  induction hsrc generalizing scope Δ P n exprPath callee arg paramTy returnTy labels with
  | var | constNone | constTrue | constFalse | new | isInstance =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case enforceBody =>
            cases rest <;> simp [CheckedExpr.nodeAt] at hnode
  | attrAccess hbase _ ih =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode
          case enforceBody =>
            cases rest with
            | nil =>
                simp [CheckedExpr.nodeAt] at hnode
            | cons child' tail =>
                cases child' <;> simp [CheckedExpr.nodeAt] at hnode
                case dynAttrBase =>
                  rcases ih (scope := scope) (Δ := Δ) (P := .any) (n := n) (p := p) hnode with
                    ⟨hlow, hhigh⟩
                  constructor
                  · exact hlow
                  · simp [compileCheck, freshLabel, mkBoundaryLabels_next]
                    omega
  | call hcallee harg _ _ _ _ ihC ihA =>
      rename_i Γ' calleeSrc calleeSrcTy argSrc argSrcTy R hcallee_callable hcallee_wf harg_wf hcall
      let D : GTy := callParamTarget gct argSrcTy
      cases exprPath with
      | nil =>
          intro hnode
          have hEq :
              CheckedExpr.call
                  (compileCheck scope hcallee Δ (.callable D P) n).1
                  (compileCheck scope harg Δ D
                    (compileCheck scope hcallee Δ (.callable D P) n).2).1
                  (callParamCheckedTarget gct argSrcTy)
                  (checkedTargetOfRuntimePublicTy P)
                  (mkBoundaryLabels scope .positive
                    (compileBoundaryTarget (checkedTargetOfRuntimePublicTy P))
                    (compileCheck scope harg Δ D
                      (compileCheck scope hcallee Δ (.callable D P) n).2).2).1 =
                CheckedExpr.call callee arg paramTy returnTy labels := by
            exact Option.some.inj (by
              simpa [CheckedExpr.nodeAt, compileCheck, D] using hnode)
          obtain ⟨hret, _, _, _, hlabels⟩ := checkedExpr_call_inversion hEq
          cases hret
          have hcalleeMono :
              n ≤ (compileCheck scope hcallee Δ (.callable D P) n).2 :=
            compileCheck_counter_monotone
              (scope := scope)
              (hsrc := hcallee)
              (Δ := Δ)
              (P := .callable D P)
              (n := n)
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
          have hinterval :=
            mkBoundaryLabels_interval
              (scope := scope)
              (pol := .positive)
              (c := compileBoundaryTarget (checkedTargetOfRuntimePublicTy P))
              (n := (compileCheck scope harg Δ D
                (compileCheck scope hcallee Δ (.callable D P) n).2).2)
              (p := p)
          constructor
          · have hrootLo :
                n ≤ (((mkBoundaryLabels scope .positive
                  (compileBoundaryTarget (checkedTargetOfRuntimePublicTy P))
                  (compileCheck scope harg Δ D
                    (compileCheck scope hcallee Δ (.callable D P) n).2).2).1).at p).site := by
              have hrootLo := hinterval.1
              omega
            simpa [compileCheck, D, hlabels] using hrootLo
          · have hrootHi :
                (((mkBoundaryLabels scope .positive
                  (compileBoundaryTarget (checkedTargetOfRuntimePublicTy P))
                  (compileCheck scope harg Δ D
                    (compileCheck scope hcallee Δ (.callable D P) n).2).2).1).at p).site <
                  (compileCheck scope
                    (.call hcallee harg hcallee_callable hcallee_wf harg_wf hcall)
                    Δ P n).2 := by
              simpa [compileCheck, D] using hinterval.2
            simpa [compileCheck, D, hlabels] using hrootHi
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case callCallee =>
            rcases ihC
                (scope := scope)
                (Δ := Δ)
                (P := .callable D P)
                (n := n)
                (p := p)
                hnode with
              ⟨hlow, hhigh⟩
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
            have hhigh' :
                (labels.at p).site <
                  (compileCheck scope hcallee Δ
                    (.callable (callParamTarget gct argSrcTy) P) n).2 := by
              simpa [D] using hhigh
            have hargMono' :
                (compileCheck scope hcallee Δ
                  (.callable (callParamTarget gct argSrcTy) P) n).2 ≤
                  (compileCheck scope harg Δ (callParamTarget gct argSrcTy)
                    (compileCheck scope hcallee Δ
                      (.callable (callParamTarget gct argSrcTy) P) n).2).2 := by
              simpa [D] using hargMono
            constructor
            · exact hlow
            · simp [compileCheck]
              have hhigh := hhigh'
              have hargMono := hargMono'
              omega
          case callArg =>
            rcases ihA
                (scope := scope)
                (Δ := Δ)
                (P := D)
                (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
                (p := p)
                hnode with
              ⟨hlow, hhigh⟩
            have hcalleeMono :
                n ≤ (compileCheck scope hcallee Δ (.callable D P) n).2 :=
              compileCheck_counter_monotone
                (scope := scope)
                (hsrc := hcallee)
                (Δ := Δ)
                (P := .callable D P)
                (n := n)
            have hcalleeMono' :
                n ≤ (compileCheck scope hcallee Δ
                  (.callable (callParamTarget gct argSrcTy) P) n).2 := by
              simpa [D] using hcalleeMono
            have hhigh' :
                (labels.at p).site <
                  (compileCheck scope harg Δ (callParamTarget gct argSrcTy)
                    (compileCheck scope hcallee Δ
                      (.callable (callParamTarget gct argSrcTy) P) n).2).2 := by
              simpa [D] using hhigh
            constructor
            · have hcalleeMono := hcalleeMono'
              omega
            · simp [compileCheck]
              have hhigh := hhigh'
              omega
  | cond _ htest _ hthen helse ihTest ihThen ihElse =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case condTest =>
            rcases ihTest (scope := scope) (Δ := Δ) (P := .class_ boolClass) (n := n) (p := p) hnode with
              ⟨hlow, hhigh⟩
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
            have helseMono :
                (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2 ≤
                  (compileCheck scope helse Δ P
                    (compileCheck scope hthen Δ P
                      (compileCheck scope htest Δ (.class_ boolClass) n).2).2).2 :=
              compileCheck_counter_monotone
                (scope := scope)
                (hsrc := helse)
                (Δ := Δ)
                (P := P)
                (n := (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
            constructor
            · exact hlow
            · simp [compileCheck]
              omega
          case condThen =>
            rcases ihThen
                (scope := scope)
                (Δ := Δ)
                (P := P)
                (n := (compileCheck scope htest Δ (.class_ boolClass) n).2)
                (p := p)
                hnode with
              ⟨hlow, hhigh⟩
            have htestMono :=
              compileCheck_counter_monotone
                (scope := scope) (hsrc := htest) (Δ := Δ) (P := .class_ boolClass) (n := n)
            have helseMono :
                (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2 ≤
                  (compileCheck scope helse Δ P
                    (compileCheck scope hthen Δ P
                      (compileCheck scope htest Δ (.class_ boolClass) n).2).2).2 :=
              compileCheck_counter_monotone
                (scope := scope)
                (hsrc := helse)
                (Δ := Δ)
                (P := P)
                (n := (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
            constructor
            · omega
            · simp [compileCheck]
              omega
          case condElse =>
            rcases ihElse
                (scope := scope)
                (Δ := Δ)
                (P := P)
                (n := (compileCheck scope hthen Δ P
                  (compileCheck scope htest Δ (.class_ boolClass) n).2).2)
                (p := p)
                hnode with
              ⟨hlow, hhigh⟩
            have htestMono :
                n ≤ (compileCheck scope htest Δ (.class_ boolClass) n).2 :=
              compileCheck_counter_monotone
                (scope := scope)
                (hsrc := htest)
                (Δ := Δ)
                (P := .class_ boolClass)
                (n := n)
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
            constructor
            · omega
            · exact hhigh
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
      rename_i b C cls thenBranch thenSrcTy elseBranch elseSrcTy Γ' x
      cases hΔ : Δ.lookup x with
      | none =>
          cases exprPath with
          | nil =>
              intro hnode
              simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
          | cons child rest =>
              intro hnode
              cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
              · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
              · rcases ihThen (scope := scope) (Δ := Δ) (P := P) (n := n) (p := p) hnode with
                    ⟨hlow, hhigh⟩
                have helseMono :
                    (compileCheck scope hthen Δ P n).2 ≤
                      (compileCheck scope helse Δ P
                        (compileCheck scope hthen Δ P n).2).2 :=
                  compileCheck_counter_monotone
                    (scope := scope)
                    (hsrc := helse)
                    (Δ := Δ)
                    (P := P)
                    (n := (compileCheck scope hthen Δ P n).2)
                refine ⟨hlow, ?_⟩
                simp [compileCheck, hΔ]; omega
              · rcases ihElse
                    (scope := scope)
                    (Δ := Δ)
                    (P := P)
                    (n := (compileCheck scope hthen Δ P n).2)
                    (p := p)
                    hnode with
                  ⟨hlow, hhigh⟩
                have hthenMono :
                    n ≤ (compileCheck scope hthen Δ P n).2 :=
                  compileCheck_counter_monotone
                    (scope := scope) (hsrc := hthen) (Δ := Δ) (P := P) (n := n)
                refine ⟨by omega, ?_⟩
                simpa [compileCheck, hΔ] using hhigh
      | some T =>
          by_cases href : CheckedBranchRefineOk gct T C
          · cases exprPath with
            | nil =>
                intro hnode
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
            | cons child rest =>
                intro hnode
                cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
                · rcases ihThen
                      (scope := scope)
                      (Δ := Δ.update x (.intersection T (.class_ C)))
                      (P := P)
                      (n := n)
                      (p := p)
                      hnode with
                    ⟨hlow, hhigh⟩
                  have helseMono :
                      (compileCheck scope hthen
                        (Δ.update x (.intersection T (.class_ C))) P n).2 ≤
                        (compileCheck scope helse
                          (Δ.update x (.intersection T (.negClass C))) P
                          (compileCheck scope hthen
                            (Δ.update x (.intersection T (.class_ C))) P n).2).2 :=
                    compileCheck_counter_monotone
                      (scope := scope)
                      (hsrc := helse)
                      (Δ := Δ.update x (.intersection T (.negClass C)))
                      (P := P)
                      (n := (compileCheck scope hthen
                        (Δ.update x (.intersection T (.class_ C))) P n).2)
                  refine ⟨hlow, ?_⟩
                  simp [compileCheck, hΔ, href]; omega
                · rcases ihElse
                      (scope := scope)
                      (Δ := Δ.update x (.intersection T (.negClass C)))
                      (P := P)
                      (n := (compileCheck scope hthen
                        (Δ.update x (.intersection T (.class_ C))) P n).2)
                      (p := p)
                      hnode with
                    ⟨hlow, hhigh⟩
                  have hthenMono :
                      n ≤
                        (compileCheck scope hthen
                          (Δ.update x (.intersection T (.class_ C))) P n).2 :=
                    compileCheck_counter_monotone
                      (scope := scope)
                      (hsrc := hthen)
                      (Δ := Δ.update x (.intersection T (.class_ C)))
                      (P := P)
                      (n := n)
                  refine ⟨by omega, ?_⟩
                  simpa [compileCheck, hΔ, href] using hhigh
          · cases exprPath with
            | nil =>
                intro hnode
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
            | cons child rest =>
                intro hnode
                cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
                · rcases ihThen (scope := scope) (Δ := Δ) (P := P) (n := n) (p := p) hnode with
                    ⟨hlow, hhigh⟩
                  have helseMono :
                      (compileCheck scope hthen Δ P n).2 ≤
                        (compileCheck scope helse Δ P
                          (compileCheck scope hthen Δ P n).2).2 :=
                    compileCheck_counter_monotone
                      (scope := scope)
                      (hsrc := helse)
                      (Δ := Δ)
                      (P := P)
                      (n := (compileCheck scope hthen Δ P n).2)
                  refine ⟨hlow, ?_⟩
                  simp [compileCheck, hΔ, href]; omega
                · rcases ihElse
                      (scope := scope)
                      (Δ := Δ)
                      (P := P)
                      (n := (compileCheck scope hthen Δ P n).2)
                      (p := p)
                      hnode with
                    ⟨hlow, hhigh⟩
                  have hthenMono :
                      n ≤ (compileCheck scope hthen Δ P n).2 :=
                    compileCheck_counter_monotone
                      (scope := scope) (hsrc := hthen) (Δ := Δ) (P := P) (n := n)
                  refine ⟨by omega, ?_⟩
                  simpa [compileCheck, hΔ, href] using hhigh

theorem compileCheck_call_root_site_lower_bound
    (scope : LabelScope)
    {Γ' : SBindingEnv}
    {calleeExpr argExpr : GExpr}
    {calleeSrcTy argSrcTy R : GTy}
    (hcallee : GSrcInfer gct hwfct Γ' calleeExpr calleeSrcTy)
    (harg : GSrcInfer gct hwfct Γ' argExpr argSrcTy)
    (hcallee_callable : SourceCallableTy gct calleeSrcTy)
    (hcallee_wf : WellFormedGTy gct calleeSrcTy)
    (harg_wf : WellFormedGTy gct argSrcTy)
    (hcall :
      callSourceTy?
          (gct := gct)
          (s := calleeSummarySrc gct calleeSrcTy)
          (argTy := argSrcTy)
          hwfct
          (callableSummaryOk_calleeSummarySrc hcallee_callable hcallee_wf)
          harg_wf =
        some R) :
    ∀ {Δ P n callee arg paramTy returnTy}
      {labels : BoundaryLabels (compileBoundaryTarget returnTy)}
      (p : BoundaryPath (compileBoundaryTarget returnTy)),
      (compileCheck scope
        (.call hcallee harg hcallee_callable hcallee_wf harg_wf hcall) Δ P n).1.nodeAt [] =
          some (.call callee arg paramTy returnTy labels) →
      (compileCheck scope harg Δ (callParamTarget gct argSrcTy)
        (compileCheck scope hcallee Δ
          (.callable (callParamTarget gct argSrcTy) P) n).2).2 ≤
        (labels.at p).site := by
  intro Δ P n callee arg paramTy returnTy labels p hnode
  let D : GTy := callParamTarget gct argSrcTy
  have hEq :
      CheckedExpr.call
          (compileCheck scope hcallee Δ (.callable D P) n).1
          (compileCheck scope harg Δ D
            (compileCheck scope hcallee Δ (.callable D P) n).2).1
          (callParamCheckedTarget gct argSrcTy)
          (checkedTargetOfRuntimePublicTy P)
          (mkBoundaryLabels scope .positive
            (compileBoundaryTarget (checkedTargetOfRuntimePublicTy P))
            (compileCheck scope harg Δ D
              (compileCheck scope hcallee Δ (.callable D P) n).2).2).1 =
        CheckedExpr.call callee arg paramTy returnTy labels := by
    exact Option.some.inj (by
      simpa [CheckedExpr.nodeAt, compileCheck, D] using hnode)
  obtain ⟨hret, _, _, _, hlabels⟩ := checkedExpr_call_inversion hEq
  cases hret
  have hinterval :=
    mkBoundaryLabels_interval
      (scope := scope)
      (pol := .positive)
      (c := compileBoundaryTarget (checkedTargetOfRuntimePublicTy P))
      (n := (compileCheck scope harg Δ D
        (compileCheck scope hcallee Δ (.callable D P) n).2).2)
      (p := p)
  have hrootLo :
      (compileCheck scope harg Δ D
        (compileCheck scope hcallee Δ (.callable D P) n).2).2 ≤
        (((mkBoundaryLabels scope .positive
          (compileBoundaryTarget (checkedTargetOfRuntimePublicTy P))
          (compileCheck scope harg Δ D
            (compileCheck scope hcallee Δ (.callable D P) n).2).2).1).at p).site := by
    exact hinterval.1
  simpa [compileCheck, D, hlabels] using hrootLo

inductive CompileCheckSiteKind where
  | enforce
  | dynAttr
  | callReturn

inductive CompileCheckSiteAt :
    CompileCheckSiteKind → CheckedExpr → ExprPath → Nat → Prop where
  | enforce {e c labels}
      (p : BoundaryPath (compileBoundaryTarget c)) :
      expr.nodeAt exprPath = some (.enforce e c labels) →
      CompileCheckSiteAt .enforce expr exprPath (labels.at p).site
  | dynAttr {e attr ℓ} :
      expr.nodeAt exprPath = some (.dynAttrAccess e attr ℓ) →
      CompileCheckSiteAt .dynAttr expr exprPath ℓ.site
  | callReturn
      {callee arg paramTy returnTy}
      {labels : BoundaryLabels (compileBoundaryTarget returnTy)}
      (p : BoundaryPath (compileBoundaryTarget returnTy)) :
      expr.nodeAt exprPath = some (.call callee arg paramTy returnTy labels) →
      CompileCheckSiteAt .callReturn expr exprPath (labels.at p).site

theorem compileCheck_site_interval
    (kind : CompileCheckSiteKind)
    (scope : LabelScope)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    ∀ {Δ P n exprPath site},
      CompileCheckSiteAt kind (compileCheck scope hsrc Δ P n).1 exprPath site →
      n ≤ site ∧ site < (compileCheck scope hsrc Δ P n).2 := by
  intro Δ P n exprPath site hsite
  cases hsite with
  | enforce p hnode =>
      exact compileCheck_enforce_site_interval
        (scope := scope) (hsrc := hsrc) (Δ := Δ) (P := P) (n := n)
        (exprPath := exprPath) p hnode
  | dynAttr hnode =>
      exact compileCheck_dynAttr_site_interval
        (scope := scope) (hsrc := hsrc) (Δ := Δ) (P := P) (n := n)
        (exprPath := exprPath) hnode
  | callReturn p hnode =>
      exact compileCheck_call_return_site_interval
        (scope := scope) (hsrc := hsrc) (Δ := Δ) (P := P) (n := n)
        (exprPath := exprPath) p hnode

theorem compileCheck_kind_intervals_disjoint
    (kind₁ kind₂ : CompileCheckSiteKind)
    (scope : LabelScope)
    {Γ₁ Γ₂ : SBindingEnv}
    {e₁ e₂ : GExpr}
    {srcTy₁ srcTy₂ : GTy}
    {hsrc₁ : GSrcInfer gct hwfct Γ₁ e₁ srcTy₁}
    {hsrc₂ : GSrcInfer gct hwfct Γ₂ e₂ srcTy₂}
    {Δ₁ Δ₂ : GTyEnv}
    {P₁ P₂ : GTy}
    {n₁ n₂ : Nat}
    (hdisjoint : (compileCheck scope hsrc₁ Δ₁ P₁ n₁).2 ≤ n₂) :
    ∀ {exprPath₁ exprPath₂ site₁ site₂},
      CompileCheckSiteAt kind₁ (compileCheck scope hsrc₁ Δ₁ P₁ n₁).1 exprPath₁ site₁ →
      CompileCheckSiteAt kind₂ (compileCheck scope hsrc₂ Δ₂ P₂ n₂).1 exprPath₂ site₂ →
      site₁ ≠ site₂ := by
  intro exprPath₁ exprPath₂ site₁ site₂ hsite₁ hsite₂ hsite
  obtain ⟨_, hleftHi⟩ :=
    compileCheck_site_interval kind₁ scope hsrc₁
      (Δ := Δ₁) (P := P₁) (n := n₁) (exprPath := exprPath₁) (site := site₁) hsite₁
  obtain ⟨hrightLo, _⟩ :=
    compileCheck_site_interval kind₂ scope hsrc₂
      (Δ := Δ₂) (P := P₂) (n := n₂) (exprPath := exprPath₂) (site := site₂) hsite₂
  rw [hsite] at hleftHi
  omega

theorem compileCheck_intervals_disjoint
    (scope : LabelScope)
    {Γ₁ Γ₂ : SBindingEnv}
    {e₁ e₂ : GExpr}
    {srcTy₁ srcTy₂ : GTy}
    {hsrc₁ : GSrcInfer gct hwfct Γ₁ e₁ srcTy₁}
    {hsrc₂ : GSrcInfer gct hwfct Γ₂ e₂ srcTy₂}
    {Δ₁ Δ₂ : GTyEnv}
    {P₁ P₂ : GTy}
    {n₁ n₂ : Nat}
    (hdisjoint : (compileCheck scope hsrc₁ Δ₁ P₁ n₁).2 ≤ n₂) :
    ∀ {exprPath₁ exprPath₂ e₁' e₂' c₁ c₂ labels₁ labels₂ p₁ p₂},
      (compileCheck scope hsrc₁ Δ₁ P₁ n₁).1.nodeAt exprPath₁ = some (.enforce e₁' c₁ labels₁) →
      (compileCheck scope hsrc₂ Δ₂ P₂ n₂).1.nodeAt exprPath₂ = some (.enforce e₂' c₂ labels₂) →
      (labels₁.at p₁).site ≠ (labels₂.at p₂).site := by
  intro exprPath₁ exprPath₂ e₁' e₂' c₁ c₂ labels₁ labels₂ p₁ p₂ hnode₁ hnode₂
  exact compileCheck_kind_intervals_disjoint .enforce .enforce scope hdisjoint
    (.enforce p₁ hnode₁) (.enforce p₂ hnode₂)

theorem compileCheck_dynAttr_intervals_disjoint
    (scope : LabelScope)
    {Γ₁ Γ₂ : SBindingEnv}
    {e₁ e₂ : GExpr}
    {srcTy₁ srcTy₂ : GTy}
    {hsrc₁ : GSrcInfer gct hwfct Γ₁ e₁ srcTy₁}
    {hsrc₂ : GSrcInfer gct hwfct Γ₂ e₂ srcTy₂}
    {Δ₁ Δ₂ : GTyEnv}
    {P₁ P₂ : GTy}
    {n₁ n₂ : Nat}
    (hdisjoint : (compileCheck scope hsrc₁ Δ₁ P₁ n₁).2 ≤ n₂) :
    ∀ {exprPath₁ exprPath₂ e₁' e₂' attr₁ attr₂ ℓ₁ ℓ₂},
      (compileCheck scope hsrc₁ Δ₁ P₁ n₁).1.nodeAt exprPath₁ = some (.dynAttrAccess e₁' attr₁ ℓ₁) →
      (compileCheck scope hsrc₂ Δ₂ P₂ n₂).1.nodeAt exprPath₂ = some (.dynAttrAccess e₂' attr₂ ℓ₂) →
      ℓ₁.site ≠ ℓ₂.site := by
  intro exprPath₁ exprPath₂ e₁' e₂' attr₁ attr₂ ℓ₁ ℓ₂ hnode₁ hnode₂
  exact compileCheck_kind_intervals_disjoint .dynAttr .dynAttr scope hdisjoint
    (.dynAttr hnode₁) (.dynAttr hnode₂)

theorem compileCheck_callReturn_intervals_disjoint
    (scope : LabelScope)
    {Γ₁ Γ₂ : SBindingEnv}
    {e₁ e₂ : GExpr}
    {srcTy₁ srcTy₂ : GTy}
    {hsrc₁ : GSrcInfer gct hwfct Γ₁ e₁ srcTy₁}
    {hsrc₂ : GSrcInfer gct hwfct Γ₂ e₂ srcTy₂}
    {Δ₁ Δ₂ : GTyEnv}
    {P₁ P₂ : GTy}
    {n₁ n₂ : Nat}
    (hdisjoint : (compileCheck scope hsrc₁ Δ₁ P₁ n₁).2 ≤ n₂) :
    ∀ {exprPath₁ exprPath₂ callee₁ arg₁}
      {paramTy₁ returnTy₁ : CheckedTarget}
      {labels₁ : BoundaryLabels (compileBoundaryTarget returnTy₁)}
      {p₁ : BoundaryPath (compileBoundaryTarget returnTy₁)}
      {callee₂ arg₂}
      {paramTy₂ returnTy₂ : CheckedTarget}
      {labels₂ : BoundaryLabels (compileBoundaryTarget returnTy₂)}
      {p₂ : BoundaryPath (compileBoundaryTarget returnTy₂)},
      (compileCheck scope hsrc₁ Δ₁ P₁ n₁).1.nodeAt exprPath₁ =
        some (.call callee₁ arg₁ paramTy₁ returnTy₁ labels₁) →
      (compileCheck scope hsrc₂ Δ₂ P₂ n₂).1.nodeAt exprPath₂ =
        some (.call callee₂ arg₂ paramTy₂ returnTy₂ labels₂) →
      (labels₁.at p₁).site ≠ (labels₂.at p₂).site := by
  intro exprPath₁ exprPath₂ callee₁ arg₁ paramTy₁ returnTy₁ labels₁ p₁
    callee₂ arg₂ paramTy₂ returnTy₂ labels₂ p₂ hnode₁ hnode₂
  exact compileCheck_kind_intervals_disjoint .callReturn .callReturn scope hdisjoint
    (.callReturn p₁ hnode₁) (.callReturn p₂ hnode₂)

theorem compileCheck_enforce_dynAttr_intervals_disjoint
    (scope : LabelScope)
    {Γ₁ Γ₂ : SBindingEnv}
    {e₁ e₂ : GExpr}
    {srcTy₁ srcTy₂ : GTy}
    {hsrc₁ : GSrcInfer gct hwfct Γ₁ e₁ srcTy₁}
    {hsrc₂ : GSrcInfer gct hwfct Γ₂ e₂ srcTy₂}
    {Δ₁ Δ₂ : GTyEnv}
    {P₁ P₂ : GTy}
    {n₁ n₂ : Nat}
    (hdisjoint : (compileCheck scope hsrc₁ Δ₁ P₁ n₁).2 ≤ n₂) :
    ∀ {exprPathE exprPathD eE c labels p eD attr ℓ},
      (compileCheck scope hsrc₁ Δ₁ P₁ n₁).1.nodeAt exprPathE = some (.enforce eE c labels) →
      (compileCheck scope hsrc₂ Δ₂ P₂ n₂).1.nodeAt exprPathD = some (.dynAttrAccess eD attr ℓ) →
      (labels.at p).site ≠ ℓ.site := by
  intro exprPathE exprPathD eE c labels p eD attr ℓ hnodeE hnodeD
  exact compileCheck_kind_intervals_disjoint .enforce .dynAttr scope hdisjoint
    (.enforce p hnodeE) (.dynAttr hnodeD)

theorem compileCheck_dynAttr_enforce_intervals_disjoint
    (scope : LabelScope)
    {Γ₁ Γ₂ : SBindingEnv}
    {e₁ e₂ : GExpr}
    {srcTy₁ srcTy₂ : GTy}
    {hsrc₁ : GSrcInfer gct hwfct Γ₁ e₁ srcTy₁}
    {hsrc₂ : GSrcInfer gct hwfct Γ₂ e₂ srcTy₂}
    {Δ₁ Δ₂ : GTyEnv}
    {P₁ P₂ : GTy}
    {n₁ n₂ : Nat}
    (hdisjoint : (compileCheck scope hsrc₁ Δ₁ P₁ n₁).2 ≤ n₂) :
    ∀ {exprPathD exprPathE eD attr ℓ eE c labels p},
      (compileCheck scope hsrc₁ Δ₁ P₁ n₁).1.nodeAt exprPathD = some (.dynAttrAccess eD attr ℓ) →
      (compileCheck scope hsrc₂ Δ₂ P₂ n₂).1.nodeAt exprPathE = some (.enforce eE c labels) →
      ℓ.site ≠ (labels.at p).site := by
  intro exprPathD exprPathE eD attr ℓ eE c labels p hnodeD hnodeE
  exact compileCheck_kind_intervals_disjoint .dynAttr .enforce scope hdisjoint
    (.dynAttr hnodeD) (.enforce p hnodeE)

theorem compileCheck_enforce_callReturn_intervals_disjoint
    (scope : LabelScope)
    {Γ₁ Γ₂ : SBindingEnv}
    {e₁ e₂ : GExpr}
    {srcTy₁ srcTy₂ : GTy}
    {hsrc₁ : GSrcInfer gct hwfct Γ₁ e₁ srcTy₁}
    {hsrc₂ : GSrcInfer gct hwfct Γ₂ e₂ srcTy₂}
    {Δ₁ Δ₂ : GTyEnv}
    {P₁ P₂ : GTy}
    {n₁ n₂ : Nat}
    (hdisjoint : (compileCheck scope hsrc₁ Δ₁ P₁ n₁).2 ≤ n₂) :
    ∀ {exprPathE exprPathC eE c labelsE pE calleeC argC}
      {paramTyC returnTyC : CheckedTarget}
      {labelsC : BoundaryLabels (compileBoundaryTarget returnTyC)}
      {pC : BoundaryPath (compileBoundaryTarget returnTyC)},
      (compileCheck scope hsrc₁ Δ₁ P₁ n₁).1.nodeAt exprPathE = some (.enforce eE c labelsE) →
      (compileCheck scope hsrc₂ Δ₂ P₂ n₂).1.nodeAt exprPathC =
        some (.call calleeC argC paramTyC returnTyC labelsC) →
      (labelsE.at pE).site ≠ (labelsC.at pC).site := by
  intro exprPathE exprPathC eE c labelsE pE calleeC argC paramTyC returnTyC labelsC pC hnodeE hnodeC
  exact compileCheck_kind_intervals_disjoint .enforce .callReturn scope hdisjoint
    (.enforce pE hnodeE) (.callReturn pC hnodeC)

theorem compileCheck_callReturn_enforce_intervals_disjoint
    (scope : LabelScope)
    {Γ₁ Γ₂ : SBindingEnv}
    {e₁ e₂ : GExpr}
    {srcTy₁ srcTy₂ : GTy}
    {hsrc₁ : GSrcInfer gct hwfct Γ₁ e₁ srcTy₁}
    {hsrc₂ : GSrcInfer gct hwfct Γ₂ e₂ srcTy₂}
    {Δ₁ Δ₂ : GTyEnv}
    {P₁ P₂ : GTy}
    {n₁ n₂ : Nat}
    (hdisjoint : (compileCheck scope hsrc₁ Δ₁ P₁ n₁).2 ≤ n₂) :
    ∀ {exprPathC exprPathE calleeC argC}
      {paramTyC returnTyC : CheckedTarget}
      {labelsC : BoundaryLabels (compileBoundaryTarget returnTyC)}
      {pC : BoundaryPath (compileBoundaryTarget returnTyC)}
      {eE c labelsE pE},
      (compileCheck scope hsrc₁ Δ₁ P₁ n₁).1.nodeAt exprPathC =
        some (.call calleeC argC paramTyC returnTyC labelsC) →
      (compileCheck scope hsrc₂ Δ₂ P₂ n₂).1.nodeAt exprPathE = some (.enforce eE c labelsE) →
      (labelsC.at pC).site ≠ (labelsE.at pE).site := by
  intro exprPathC exprPathE calleeC argC paramTyC returnTyC labelsC pC eE c labelsE pE hnodeC hnodeE
  exact compileCheck_kind_intervals_disjoint .callReturn .enforce scope hdisjoint
    (.callReturn pC hnodeC) (.enforce pE hnodeE)

theorem compileCheck_dynAttr_callReturn_intervals_disjoint
    (scope : LabelScope)
    {Γ₁ Γ₂ : SBindingEnv}
    {e₁ e₂ : GExpr}
    {srcTy₁ srcTy₂ : GTy}
    {hsrc₁ : GSrcInfer gct hwfct Γ₁ e₁ srcTy₁}
    {hsrc₂ : GSrcInfer gct hwfct Γ₂ e₂ srcTy₂}
    {Δ₁ Δ₂ : GTyEnv}
    {P₁ P₂ : GTy}
    {n₁ n₂ : Nat}
    (hdisjoint : (compileCheck scope hsrc₁ Δ₁ P₁ n₁).2 ≤ n₂) :
    ∀ {exprPathD exprPathC eD attr ℓ calleeC argC}
      {paramTyC returnTyC : CheckedTarget}
      {labelsC : BoundaryLabels (compileBoundaryTarget returnTyC)}
      {pC : BoundaryPath (compileBoundaryTarget returnTyC)},
      (compileCheck scope hsrc₁ Δ₁ P₁ n₁).1.nodeAt exprPathD = some (.dynAttrAccess eD attr ℓ) →
      (compileCheck scope hsrc₂ Δ₂ P₂ n₂).1.nodeAt exprPathC =
        some (.call calleeC argC paramTyC returnTyC labelsC) →
      ℓ.site ≠ (labelsC.at pC).site := by
  intro exprPathD exprPathC eD attr ℓ calleeC argC paramTyC returnTyC labelsC pC hnodeD hnodeC
  exact compileCheck_kind_intervals_disjoint .dynAttr .callReturn scope hdisjoint
    (.dynAttr hnodeD) (.callReturn pC hnodeC)

theorem compileCheck_callReturn_dynAttr_intervals_disjoint
    (scope : LabelScope)
    {Γ₁ Γ₂ : SBindingEnv}
    {e₁ e₂ : GExpr}
    {srcTy₁ srcTy₂ : GTy}
    {hsrc₁ : GSrcInfer gct hwfct Γ₁ e₁ srcTy₁}
    {hsrc₂ : GSrcInfer gct hwfct Γ₂ e₂ srcTy₂}
    {Δ₁ Δ₂ : GTyEnv}
    {P₁ P₂ : GTy}
    {n₁ n₂ : Nat}
    (hdisjoint : (compileCheck scope hsrc₁ Δ₁ P₁ n₁).2 ≤ n₂) :
    ∀ {exprPathC exprPathD calleeC argC}
      {paramTyC returnTyC : CheckedTarget}
      {labelsC : BoundaryLabels (compileBoundaryTarget returnTyC)}
      {pC : BoundaryPath (compileBoundaryTarget returnTyC)}
      {eD attr ℓ},
      (compileCheck scope hsrc₁ Δ₁ P₁ n₁).1.nodeAt exprPathC =
        some (.call calleeC argC paramTyC returnTyC labelsC) →
      (compileCheck scope hsrc₂ Δ₂ P₂ n₂).1.nodeAt exprPathD = some (.dynAttrAccess eD attr ℓ) →
      (labelsC.at pC).site ≠ ℓ.site := by
  intro exprPathC exprPathD calleeC argC paramTyC returnTyC labelsC pC eD attr ℓ hnodeC hnodeD
  exact compileCheck_kind_intervals_disjoint .callReturn .dynAttr scope hdisjoint
    (.callReturn pC hnodeC) (.dynAttr hnodeD)
