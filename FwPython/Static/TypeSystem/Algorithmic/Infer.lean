import FwPython.Static.TypeSystem.Algorithmic.Attr
import FwPython.Static.TypeSystem.Algorithmic.Call
import FwPython.Static.TypeSystem.Algorithmic.Basis

/-! ## Algorithmic basis inference -/

private def mkInferredBasisOfSound
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (raw : List Ty)
    (hrawSound : ∀ T, T ∈ raw → HasType ct Γ e T) :
    InferredBasis ct Γ e where
  raw := raw
  elems := saturateBasis raw
  saturated := rfl
  wf := by
    intro T hT
    exact saturateBasis_member_wellFormed
      (ct := ct) (B := raw)
      (fun U hU => hasType_wellFormed hwfct hΓwf (hrawSound U hU))
      hT
  sound := by
    intro T hT
    exact saturateBasis_member_sound
      (ct := ct) (Γ := Γ) (e := e) (B := raw) hrawSound hT

@[simp] theorem mkInferredBasisOfSound_raw
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (raw : List Ty)
    (hrawSound : ∀ T, T ∈ raw → HasType ct Γ e T) :
    (mkInferredBasisOfSound
      (ct := ct) (Γ := Γ) (e := e) hwfct hΓwf raw hrawSound).raw = raw := rfl

@[simp] theorem mkInferredBasisOfSound_elems
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (raw : List Ty)
    (hrawSound : ∀ T, T ∈ raw → HasType ct Γ e T) :
    (mkInferredBasisOfSound
      (ct := ct) (Γ := Γ) (e := e) hwfct hΓwf raw hrawSound).elems = saturateBasis raw := rfl

def pairwiseUnions (left right : List Ty) : List Ty :=
  left.flatMap fun T1 =>
    right.map fun T2 =>
      .union T1 T2

theorem mem_pairwiseUnions :
    U ∈ pairwiseUnions left right ↔
      ∃ T1, T1 ∈ left ∧ ∃ T2, T2 ∈ right ∧ U = .union T1 T2 := by
  constructor
  · intro hU
    rw [pairwiseUnions] at hU
    rw [List.mem_flatMap] at hU
    rcases hU with ⟨T1, hT1, hmap⟩
    rw [List.mem_map] at hmap
    rcases hmap with ⟨T2, hT2, hEq⟩
    exact ⟨T1, hT1, T2, hT2, hEq.symm⟩
  · rintro ⟨T1, hT1, T2, hT2, rfl⟩
    rw [pairwiseUnions]
    rw [List.mem_flatMap]
    refine ⟨T1, hT1, ?_⟩
    rw [List.mem_map]
    exact ⟨T2, hT2, rfl⟩

def findBoolWitness
    (hwfct : WellFormedClassTable ct)
    (basis : List Ty)
    (hbasisWf : ∀ T, T ∈ basis → WellFormedTy ct T) :
    Option { S // S ∈ basis ∧ IsSubtype ct S (.class_ boolClass) } :=
  match basis with
  | [] =>
      none
  | S :: rest =>
      let hwfBool := wellFormed_bool_type hwfct
      let _ : Decidable (IsSubtype ct S (.class_ boolClass)) :=
        isSubtype_decidable (ct := ct) (T := S) (U := .class_ boolClass)
          hwfct (hbasisWf S (by simp)) hwfBool
      if hsub : IsSubtype ct S (.class_ boolClass) then
        some ⟨S, by exact ⟨by simp, hsub⟩⟩
      else
        match findBoolWitness hwfct rest (fun T hT => hbasisWf T (by simp [hT])) with
        | none =>
            none
        | some ⟨T, hT, hsubT⟩ =>
            some ⟨T, by exact ⟨by simp [hT], hsubT⟩⟩
termination_by basis.length

def ordinaryCondRaw
    (hwfct : WellFormedClassTable ct)
    (condBasis : InferredBasis ct Γ condExpr)
    (thenBasis : InferredBasis ct Γ thenBr)
    (elseBasis : InferredBasis ct Γ elseBr) : List Ty :=
  match findBoolWitness hwfct condBasis.elems condBasis.wf with
  | some _ => pairwiseUnions thenBasis.elems elseBasis.elems
  | none => []

private theorem ordinaryCondRaw_sound
    (hwfct : WellFormedClassTable ct)
    (condBasis : InferredBasis ct Γ condExpr)
    (thenBasis : InferredBasis ct Γ thenBr)
    (elseBasis : InferredBasis ct Γ elseBr)
    (hmem : T ∈ ordinaryCondRaw hwfct condBasis thenBasis elseBasis) :
    HasType ct Γ (.cond condExpr thenBr elseBr) T := by
  revert hmem
  unfold ordinaryCondRaw
  cases hwitness : findBoolWitness hwfct condBasis.elems condBasis.wf with
  | none =>
      intro hmem
      simp at hmem
  | some witness =>
      intro hmem
      simp at hmem
      rcases (mem_pairwiseUnions.1 hmem) with ⟨Tthen, hthen, Telse, helse, rfl⟩
      exact .cond
        (condBasis.sound witness.1 witness.2.1)
        witness.2.2
        (thenBasis.sound Tthen hthen)
        (elseBasis.sound Telse helse)

theorem findBoolWitness_some_of_match
    (hwfct : WellFormedClassTable ct)
    (hbasisWf : ∀ T, T ∈ basis → WellFormedTy ct T)
    (hcond : S ∈ basis)
    (hbool : IsSubtype ct S (.class_ boolClass)) :
    ∃ w, findBoolWitness hwfct basis hbasisWf = some w := by
  induction basis with
  | nil =>
      cases hcond
  | cons T rest ih =>
      let hwfBool := wellFormed_bool_type hwfct
      let _ : Decidable (IsSubtype ct T (.class_ boolClass)) :=
        isSubtype_decidable (ct := ct) (T := T) (U := .class_ boolClass)
          hwfct (hbasisWf T (by simp)) hwfBool
      by_cases hsubT : IsSubtype ct T (.class_ boolClass)
      · refine ⟨⟨T, by exact ⟨by simp, hsubT⟩⟩, ?_⟩
        simp [findBoolWitness, hsubT]
      · rcases List.mem_cons.mp hcond with rfl | hcondRest
        · exact False.elim (hsubT hbool)
        · obtain ⟨⟨U, hUrest, hUbool⟩, hw⟩ :=
            ih
              (fun U hU => hbasisWf U (by simp [hU]))
              hcondRest
          refine ⟨⟨U, by exact ⟨by simp [hUrest], hUbool⟩⟩, ?_⟩
          simp [findBoolWitness, hsubT, hw]

theorem ordinaryCondRaw_mem_of_witness
    (hwfct : WellFormedClassTable ct)
    (condBasis : InferredBasis ct Γ condExpr)
    (thenBasis : InferredBasis ct Γ thenBr)
    (elseBasis : InferredBasis ct Γ elseBr)
    (hcond : Scond ∈ condBasis.elems)
    (hbool : IsSubtype ct Scond (.class_ boolClass))
    (hthen : Tthen ∈ thenBasis.elems)
    (helse : Telse ∈ elseBasis.elems) :
    (.union Tthen Telse) ∈ ordinaryCondRaw hwfct condBasis thenBasis elseBasis := by
  obtain ⟨w, hw⟩ :=
    findBoolWitness_some_of_match
      (ct := ct) (basis := condBasis.elems)
      hwfct condBasis.wf hcond hbool
  unfold ordinaryCondRaw
  rw [hw]
  exact mem_pairwiseUnions.2 ⟨Tthen, hthen, Telse, helse, rfl⟩

def lookupWitness? (Γ : TyEnv) (x : Identifier) :
    Option { T // Γ.lookup x = some T } :=
  match heq : Γ.lookup x with
  | none => none
  | some T => some ⟨T, by simp⟩

def classLookupWitness? (ct : ClassTable) (C : Identifier) :
    Option { cls // findClass ct C = some cls } :=
  match heq : findClass ct C with
  | none => none
  | some cls => some ⟨cls, by simp⟩

theorem lookupWitness?_eq_some
    {Γ : TyEnv} {x : Identifier} {T : Ty}
    (hlook : Γ.lookup x = some T) :
    lookupWitness? Γ x = some ⟨T, hlook⟩ := by
  unfold lookupWitness?
  generalize hgen : Γ.lookup x = look at hlook
  cases look with
  | none => cases hlook
  | some T' =>
      cases hlook
      rfl

theorem classLookupWitness?_eq_some
    {ct : ClassTable} {C : Identifier} {cls : Class}
    (hfind : findClass ct C = some cls) :
    classLookupWitness? ct C = some ⟨cls, hfind⟩ := by
  unfold classLookupWitness?
  generalize hgen : findClass ct C = found at hfind
  cases found with
  | none => cases hfind
  | some cls' =>
      cases hfind
      rfl

def inferBasisCertified
    (hwfct : WellFormedClassTable ct)
    (Γ : TyEnv) (hΓwf : WellFormedTyEnv ct Γ) :
    (e : Expr) → InferredBasis ct Γ e
  | .var x =>
      match hlook : Γ.lookup x with
      | some T =>
          mkInferredBasisOfSound hwfct hΓwf [T] <| by
            intro U hU
            simp at hU
            rcases hU with rfl
            exact .var hlook
      | none =>
          mkInferredBasisOfSound hwfct hΓwf [] <| by
            intro U hU
            cases hU
  | .new cname =>
      match hfind : findClass ct cname with
      | none =>
          mkInferredBasisOfSound hwfct hΓwf [] <| by
            intro U hU
            cases hU
      | some _ =>
          if hbool : cname = boolClass then
            mkInferredBasisOfSound hwfct hΓwf [] <| by
              intro U hU
              cases hU
          else if hnone : cname = noneClass then
            mkInferredBasisOfSound hwfct hΓwf [] <| by
              intro U hU
              cases hU
          else if hbm : cname = boundMethodClass then
            mkInferredBasisOfSound hwfct hΓwf [] <| by
              intro U hU
              cases hU
          else
            mkInferredBasisOfSound hwfct hΓwf [.class_ cname] <| by
              intro U hU
              simp at hU
              rcases hU with rfl
              exact .new hfind hbool hnone hbm
  | .attrAccess base attrName =>
      let baseBasis := inferBasisCertified hwfct Γ hΓwf base
      let raw :=
        baseBasis.elems.attach.flatMap fun entry =>
          attrResultsFromTy hwfct entry.1 (baseBasis.wf entry.1 entry.2) attrName
      mkInferredBasisOfSound hwfct hΓwf raw <| by
        intro U hU
        rw [List.mem_flatMap] at hU
        rcases hU with ⟨entry, _, hentry⟩
        exact attrResultsFromTy_sound
          (hwfct := hwfct)
          (sourceTy := entry.1)
          (hwfSource := baseBasis.wf entry.1 entry.2)
          (attr := attrName)
          (R := U)
          hentry
          (baseBasis.sound entry.1 entry.2)
  | .call callee arg =>
      let calleeBasis := inferBasisCertified hwfct Γ hΓwf callee
      let argBasis := inferBasisCertified hwfct Γ hΓwf arg
      let raw :=
        calleeBasis.elems.attach.flatMap fun entry =>
          callResultsFromTy hwfct entry.1 (calleeBasis.wf entry.1 entry.2)
            argBasis.elems argBasis.wf
      mkInferredBasisOfSound hwfct hΓwf raw <| by
        intro U hU
        rw [List.mem_flatMap] at hU
        rcases hU with ⟨entry, _, hentry⟩
        exact callResultsFromTy_sound
          (hwfct := hwfct)
          (calleeTy := entry.1)
          (hwfCallee := calleeBasis.wf entry.1 entry.2)
          (argBasis := argBasis.elems)
          (hArgWf := argBasis.wf)
          (R := U)
          hentry
          (calleeBasis.sound entry.1 entry.2)
          (fun A hA => argBasis.sound A hA)
  | .constNone =>
      mkInferredBasisOfSound hwfct hΓwf [.class_ noneClass] <| by
        intro U hU
        simp at hU
        rcases hU with rfl
        exact .constNone
  | .constTrue =>
      mkInferredBasisOfSound hwfct hΓwf [.class_ boolClass] <| by
        intro U hU
        simp at hU
        rcases hU with rfl
        exact .constTrue
  | .constFalse =>
      mkInferredBasisOfSound hwfct hΓwf [.class_ boolClass] <| by
        intro U hU
        simp at hU
        rcases hU with rfl
        exact .constFalse
  | .cond (.isInstance x C) thenBr elseBr =>
      let condBasis := inferBasisCertified hwfct Γ hΓwf (.isInstance x C)
      let thenBasis := inferBasisCertified hwfct Γ hΓwf thenBr
      let elseBasis := inferBasisCertified hwfct Γ hΓwf elseBr
      let ordinaryRaw := ordinaryCondRaw hwfct condBasis thenBasis elseBasis
      let specializedRawCore :=
        fun (T : Ty) (hlook : Γ.lookup x = some T) (cls : Class)
            (hfind : findClass ct C = some cls) =>
          let hmro := (hwfct.allMrosExist _ _ hfind).hmro
          let hΓThen :=
            wellFormedTyEnv_update_class
              (ct := ct) (Γ := Γ) hΓwf hlook hfind hmro
          let hΓElse :=
            wellFormedTyEnv_update_negClass
              (ct := ct) (Γ := Γ) hΓwf hlook hfind hmro
          let thenNarrow :=
            inferBasisCertified hwfct
              (Γ.update x (.intersection T (.class_ C))) hΓThen thenBr
          let elseNarrow :=
            inferBasisCertified hwfct
              (Γ.update x (.intersection T (.negClass C))) hΓElse elseBr
          pairwiseUnions thenNarrow.elems elseNarrow.elems
      let specializedRaw :=
        match lookupWitness? Γ x with
        | none => []
        | some w =>
            match classLookupWitness? ct C with
            | none => []
            | some wcls => specializedRawCore w.1 w.2 wcls.1 wcls.2
      let raw := ordinaryRaw ++ specializedRaw
      mkInferredBasisOfSound hwfct hΓwf raw <| by
        intro U hU
        rcases List.mem_append.mp hU with hU | hU
        · exact ordinaryCondRaw_sound hwfct condBasis thenBasis elseBasis hU
        · revert hU
          cases hlookup : lookupWitness? Γ x with
          | none =>
              intro hU
              simp [specializedRaw, hlookup] at hU
          | some w =>
              rcases w with ⟨T, hlook⟩
              cases hfind : classLookupWitness? ct C with
              | none =>
                  intro hU
                  simp [specializedRaw, hlookup, hfind] at hU
              | some wcls =>
                  rcases wcls with ⟨cls, hfindClass⟩
                  let hmro := (hwfct.allMrosExist _ _ hfindClass).hmro
                  let hΓThen :=
                    wellFormedTyEnv_update_class
                      (ct := ct) (Γ := Γ) hΓwf hlook hfindClass hmro
                  let hΓElse :=
                    wellFormedTyEnv_update_negClass
                      (ct := ct) (Γ := Γ) hΓwf hlook hfindClass hmro
                  let thenNarrow :=
                    inferBasisCertified hwfct
                      (Γ.update x (.intersection T (.class_ C))) hΓThen thenBr
                  let elseNarrow :=
                    inferBasisCertified hwfct
                      (Γ.update x (.intersection T (.negClass C))) hΓElse elseBr
                  intro hU
                  have hU' : U ∈ pairwiseUnions thenNarrow.elems elseNarrow.elems := by
                    simpa [specializedRaw, specializedRawCore, hlookup, hfind, thenNarrow, elseNarrow] using hU
                  rcases (mem_pairwiseUnions.1 hU') with ⟨Tthen, hthen, Telse, helse, rfl⟩
                  exact .condIsInstance hlook hfindClass
                    (thenNarrow.sound Tthen hthen)
                    (elseNarrow.sound Telse helse)
  | .cond condExpr thenBr elseBr =>
      let condBasis := inferBasisCertified hwfct Γ hΓwf condExpr
      let thenBasis := inferBasisCertified hwfct Γ hΓwf thenBr
      let elseBasis := inferBasisCertified hwfct Γ hΓwf elseBr
      let raw := ordinaryCondRaw hwfct condBasis thenBasis elseBasis
      mkInferredBasisOfSound hwfct hΓwf raw <| by
        intro U hU
        exact ordinaryCondRaw_sound hwfct condBasis thenBasis elseBasis hU
  | .isInstance x C =>
      match hlook : Γ.lookup x, hfind : findClass ct C with
      | some _, some _ =>
          mkInferredBasisOfSound hwfct hΓwf [.class_ boolClass] <| by
            intro U hU
            simp at hU
            rcases hU with rfl
            exact .isInstance hlook hfind
      | _, _ =>
          mkInferredBasisOfSound hwfct hΓwf [] <| by
            intro U hU
            cases hU

def inferBasis
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (e : Expr) : List Ty :=
  (inferBasisCertified hwfct Γ hΓwf e).elems

theorem inferBasis_all_wellFormed
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hmem : T ∈ inferBasis hwfct hΓwf e) :
    WellFormedTy ct T :=
  (inferBasisCertified hwfct Γ hΓwf e).wf T hmem

theorem inferBasis_sound
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hmem : T ∈ inferBasis hwfct hΓwf e) :
    HasType ct Γ e T :=
  (inferBasisCertified hwfct Γ hΓwf e).sound T hmem

@[simp] theorem inferBasis_var_eq
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hlook : Γ.lookup x = some T) :
    inferBasis hwfct hΓwf (.var x) = saturateBasis [T] := by
  unfold inferBasis inferBasisCertified
  split <;> simp_all [mkInferredBasisOfSound_elems]

@[simp] theorem inferBasis_constNone_eq
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ) :
    inferBasis hwfct hΓwf .constNone = saturateBasis [.class_ noneClass] := by
  unfold inferBasis
  rw [inferBasisCertified.eq_5]
  simp [mkInferredBasisOfSound_elems]

@[simp] theorem inferBasis_constTrue_eq
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ) :
    inferBasis hwfct hΓwf .constTrue = saturateBasis [.class_ boolClass] := by
  unfold inferBasis
  rw [inferBasisCertified.eq_6]
  simp [mkInferredBasisOfSound_elems]

@[simp] theorem inferBasis_constFalse_eq
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ) :
    inferBasis hwfct hΓwf .constFalse = saturateBasis [.class_ boolClass] := by
  unfold inferBasis
  rw [inferBasisCertified.eq_7]
  simp [mkInferredBasisOfSound_elems]

@[simp] theorem inferBasis_new_eq
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hfind : findClass ct cname = some cls)
    (hbool : cname ≠ boolClass)
    (hnone : cname ≠ noneClass)
    (hbm : cname ≠ boundMethodClass) :
    inferBasis hwfct hΓwf (.new cname) = saturateBasis [.class_ cname] := by
  unfold inferBasis inferBasisCertified
  split <;> simp_all [mkInferredBasisOfSound_elems]

@[simp] theorem inferBasis_isInstance_eq
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hlook : Γ.lookup x = some T)
    (hfind : findClass ct C = some cls) :
    inferBasis hwfct hΓwf (.isInstance x C) = saturateBasis [.class_ boolClass] := by
  unfold inferBasis inferBasisCertified
  split <;> simp_all [mkInferredBasisOfSound_elems]

/-! ### Step lemmas for completeness

For each non-leaf typing constructor we expose a step lemma: given basis
witnesses for the sub-derivations, the result type lies in the basis of the
compound expression. -/

theorem inferBasis_attrAccess_step_general
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hSb : Sb ∈ inferBasis hwfct hΓwf base)
    (hsub : IsSubtype ct Sb viewTy)
    (hviewMem : (viewTy, R) ∈ allAttrReceiverViews hwfct attrName) :
    R ∈ inferBasis hwfct hΓwf (.attrAccess base attrName) := by
  let baseCert := inferBasisCertified hwfct Γ hΓwf base
  show R ∈ (inferBasisCertified hwfct Γ hΓwf (.attrAccess base attrName)).elems
  refine saturateBasis_mem_of_mem (List.mem_flatMap.mpr ⟨⟨Sb, hSb⟩, by simp, ?_⟩)
  exact attrResultsFromTy_complete_of_member hwfct
    (hwfSource := baseCert.wf Sb hSb) hsub hviewMem

theorem inferBasis_attrAccess_step
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hSb : Sb ∈ inferBasis hwfct hΓwf base)
    (hsub : IsSubtype ct Sb (.class_ cname))
    (hfmt : FindMethodType ct cname attrName paramTy returnTy) :
    (.callable paramTy returnTy) ∈ inferBasis hwfct hΓwf (.attrAccess base attrName) :=
  inferBasis_attrAccess_step_general hwfct hΓwf hSb hsub
    (attrReceiverView_class_member hwfct hfmt)

theorem inferBasis_attrAccessUnion_step
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hSb : Sb ∈ inferBasis hwfct hΓwf base)
    (hsub : IsSubtype ct Sb (.union (.class_ c1) (.class_ c2)))
    (hfmt1 : FindMethodType ct c1 attrName p1 r1)
    (hfmt2 : FindMethodType ct c2 attrName p2 r2) :
    (.union (.callable p1 r1) (.callable p2 r2)) ∈
      inferBasis hwfct hΓwf (.attrAccess base attrName) :=
  inferBasis_attrAccess_step_general hwfct hΓwf hSb hsub
    (attrReceiverView_union_member hwfct hfmt1 hfmt2)

theorem inferBasis_call_step
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hSc : Sc ∈ inferBasis hwfct hΓwf callee)
    (hSa : Sa ∈ inferBasis hwfct hΓwf arg)
    (hsubCallable : IsSubtype ct Sc (.callable paramTy returnTy))
    (hsubArg : IsSubtype ct Sa paramTy) :
    ∃ R, R ∈ inferBasis hwfct hΓwf (.call callee arg) ∧ IsSubtype ct R returnTy := by
  let calleeCert := inferBasisCertified hwfct Γ hΓwf callee
  let argCert := inferBasisCertified hwfct Γ hΓwf arg
  obtain ⟨R, hR, hRsub⟩ :=
    callResultsFromTy_complete (hwfct := hwfct) (calleeTy := Sc)
      (hwfCallee := calleeCert.wf Sc hSc)
      (argBasis := argCert.elems) (hArgWf := argCert.wf)
      (P := paramTy) (R := returnTy) (A := Sa)
      hsubCallable hSa hsubArg
  refine ⟨R, ?_, hRsub⟩
  show R ∈ (inferBasisCertified hwfct Γ hΓwf (.call callee arg)).elems
  exact saturateBasis_mem_of_mem
    (List.mem_flatMap.mpr ⟨⟨Sc, hSc⟩, by simp, hR⟩)

theorem inferBasis_cond_ordinary_step
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hSc : Sc ∈ inferBasis hwfct hΓwf condExpr)
    (hbool : IsSubtype ct Sc (.class_ boolClass))
    (hSt : St ∈ inferBasis hwfct hΓwf thenBr)
    (hSe : Se ∈ inferBasis hwfct hΓwf elseBr) :
    (.union St Se) ∈ inferBasis hwfct hΓwf (.cond condExpr thenBr elseBr) := by
  have hord :
      (.union St Se) ∈
        ordinaryCondRaw hwfct
          (inferBasisCertified hwfct Γ hΓwf condExpr)
          (inferBasisCertified hwfct Γ hΓwf thenBr)
          (inferBasisCertified hwfct Γ hΓwf elseBr) :=
    ordinaryCondRaw_mem_of_witness (ct := ct) (Γ := Γ)
      hwfct _ _ _ hSc hbool hSt hSe
  show (.union St Se) ∈
    (inferBasisCertified hwfct Γ hΓwf (.cond condExpr thenBr elseBr)).elems
  cases condExpr with
  | isInstance _ _ =>
      exact saturateBasis_mem_of_mem (List.mem_append.mpr (Or.inl hord))
  | _ => all_goals exact saturateBasis_mem_of_mem hord

theorem inferBasis_cond_isInstance_specialized_step
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hlook : Γ.lookup x = some T)
    (hfind : findClass ct C = some cls)
    (St Se : Ty)
    (hSt : St ∈ inferBasis hwfct
            (Γ := Γ.update x (.intersection T (.class_ C)))
            (wellFormedTyEnv_update_class hΓwf hlook hfind
              (hwfct.allMrosExist _ _ hfind).hmro)
            thenBr)
    (hSe : Se ∈ inferBasis hwfct
            (Γ := Γ.update x (.intersection T (.negClass C)))
            (wellFormedTyEnv_update_negClass hΓwf hlook hfind
              (hwfct.allMrosExist _ _ hfind).hmro)
            elseBr) :
    (.union St Se) ∈
      inferBasis hwfct hΓwf (.cond (.isInstance x C) thenBr elseBr) := by
  show (.union St Se) ∈
    (inferBasisCertified hwfct Γ hΓwf (.cond (.isInstance x C) thenBr elseBr)).elems
  refine saturateBasis_mem_of_mem (List.mem_append.mpr (Or.inr ?_))
  show (.union St Se) ∈
    (match lookupWitness? Γ x with
    | none => []
    | some w =>
        match classLookupWitness? ct C with
        | none => []
        | some wcls =>
            let hmro := (hwfct.allMrosExist _ _ wcls.2).hmro
            let hΓThen := wellFormedTyEnv_update_class hΓwf w.2 wcls.2 hmro
            let hΓElse := wellFormedTyEnv_update_negClass hΓwf w.2 wcls.2 hmro
            let thenNarrow := inferBasisCertified hwfct
              (Γ.update x (.intersection w.1 (.class_ C))) hΓThen thenBr
            let elseNarrow := inferBasisCertified hwfct
              (Γ.update x (.intersection w.1 (.negClass C))) hΓElse elseBr
            pairwiseUnions thenNarrow.elems elseNarrow.elems)
  rw [lookupWitness?_eq_some hlook, classLookupWitness?_eq_some hfind]
  exact mem_pairwiseUnions.mpr ⟨St, hSt, Se, hSe, rfl⟩

theorem inferBasis_intersection_step
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hS1 : S1 ∈ inferBasis hwfct hΓwf e)
    (hS2 : S2 ∈ inferBasis hwfct hΓwf e) :
    ∃ U, U ∈ inferBasis hwfct hΓwf e ∧ IsSubtype ct U (.intersection S1 S2) := by
  let basis := inferBasisCertified hwfct Γ hΓwf e
  have h1 : S1 ∈ saturateBasis basis.raw := basis.saturated ▸ hS1
  have h2 : S2 ∈ saturateBasis basis.raw := basis.saturated ▸ hS2
  obtain ⟨U, hUmem, hUsub⟩ := saturateBasis_intersection_cover h1 h2
  refine ⟨U, ?_, hUsub⟩
  show U ∈ basis.elems
  rw [basis.saturated]
  exact hUmem
