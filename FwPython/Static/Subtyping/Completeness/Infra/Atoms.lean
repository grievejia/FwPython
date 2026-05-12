import FwPython.Static.Subtyping.Completeness.Infra.Normalization

/-! ### Union and intersection atom analysis -/

def Ty.unionFree : Ty → Prop
  | .union _ _ => False
  | .intersection T U => T.unionFree ∧ U.unionFree
  | _ => True

instance unionFreeDecidable : (T : Ty) → Decidable T.unionFree
  | .bottom => isTrue trivial
  | .class_ _ => isTrue trivial
  | .negClass _ => isTrue trivial
  | .callable _ _ => isTrue trivial
  | .union _ _ => isFalse (by simp [Ty.unionFree])
  | .intersection T U =>
      match unionFreeDecidable T, unionFreeDecidable U with
      | isTrue hT, isTrue hU => isTrue ⟨hT, hU⟩
      | isFalse hT, _ => isFalse (fun h => hT h.1)
      | _, isFalse hU => isFalse (fun h => hU h.2)

def Ty.interAtoms : Ty → List Ty
  | .intersection T U => T.interAtoms ++ U.interAtoms
  | T => [T]

def Ty.interAtomsFold : List Ty → Ty
  | [] => .class_ objectClass
  | [T] => T
  | T :: Ts => .intersection T (Ty.interAtomsFold Ts)

def Ty.unionAtoms : Ty → List Ty
  | .union T U => T.unionAtoms ++ U.unionAtoms
  | T => [T]

def Ty.unionAtomsFold : List Ty → Ty
  | [] => .bottom
  | [T] => T
  | T :: Ts => .union T (Ty.unionAtomsFold Ts)

def usefulUnionArm : Ty → Bool
  | .bottom | .class_ _ | .negClass _ | .intersection _ _ => true
  | _ => false

def pickUsefulUnionArm : List Ty → Option (Ty × List Ty)
  | [] => none
  | A :: As =>
      if usefulUnionArm A then
        some (A, As)
      else
        match pickUsefulUnionArm As with
        | none => none
        | some (B, Bs) => some (B, A :: Bs)

def tySizeSum : List Ty → Nat
  | [] => 0
  | A :: As => A.size + tySizeSum As

theorem tySizeSum_append (xs ys : List Ty) :
    tySizeSum (xs ++ ys) = tySizeSum xs + tySizeSum ys := by
  induction xs with
  | nil =>
      simp [tySizeSum]
  | cons x xs ih =>
      simp [tySizeSum, ih, Nat.add_assoc]

theorem interAtoms_union_not_mem
    (T U V : Ty)
    (huf : T.unionFree) :
    .union U V ∉ T.interAtoms := by
  induction T with
  | bottom | class_ | negClass | callable =>
      simp [Ty.unionFree, Ty.interAtoms] at huf ⊢
  | union T U =>
      cases huf
  | intersection T U ihT ihU =>
      rcases huf with ⟨hufT, hufU⟩
      intro hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact ihT hufT hmem
      · exact ihU hufU hmem

theorem interAtoms_intersection_not_mem
    (T U V : Ty)
    (huf : T.unionFree) :
    .intersection U V ∉ T.interAtoms := by
  induction T with
  | bottom | class_ | negClass | callable =>
      simp [Ty.unionFree, Ty.interAtoms] at huf ⊢
  | union T U =>
      cases huf
  | intersection T U ihT ihU =>
      rcases huf with ⟨hufT, hufU⟩
      intro hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact ihT hufT hmem
      · exact ihU hufU hmem

theorem unionAtoms_union_not_mem
    (T U V : Ty) :
    .union U V ∉ T.unionAtoms := by
  induction T with
  | bottom | class_ | negClass | callable | intersection =>
      simp [Ty.unionAtoms]
  | union T U ihT ihU =>
      intro hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact ihT hmem
      · exact ihU hmem

structure SourceUnionSplit (T : Ty) where
  left : Ty
  right : Ty
  left_lt : left.size < T.size
  right_lt : right.size < T.size
  toUnion : IsSubtype ct T (.union left right)
  fromUnion : IsSubtype ct (.union left right) T

def splitNonUnionFree :
    (T : Ty) → ¬ T.unionFree → SourceUnionSplit T
  | .bottom, hnu => False.elim (hnu trivial)
  | .class_ _, hnu => False.elim (hnu trivial)
  | .negClass _, hnu => False.elim (hnu trivial)
  | .callable _ _, hnu => False.elim (hnu trivial)
  | .union T U, _ =>
      { left := T
        right := U
        left_lt := by simp [Ty.size]; omega
        right_lt := by simp [Ty.size]; omega
        toUnion := .refl
        fromUnion := .refl }
  | .intersection T U, hnu =>
      by
        by_cases hT : T.unionFree
        · have hU : ¬ U.unionFree := by
            intro hU
            exact hnu ⟨hT, hU⟩
          let splitU := splitNonUnionFree U hU
          exact
            { left := .intersection T splitU.left
              right := .intersection T splitU.right
              left_lt := by
                simp [Ty.size, splitU.left_lt]
              right_lt := by
                simp [Ty.size, splitU.right_lt]
              toUnion := by
                exact .trans
                  (.interIntro
                    (.interLeft .refl)
                    (.trans (.interRight .refl) splitU.toUnion))
                  subtype_inter_union_normalize_right_to
              fromUnion := by
                exact .trans
                  subtype_inter_union_normalize_right_from
                  (.interIntro
                    (.interLeft .refl)
                    (.trans (.interRight .refl) splitU.fromUnion)) }
        · let splitT := splitNonUnionFree T hT
          exact
            { left := .intersection splitT.left U
              right := .intersection splitT.right U
              left_lt := by
                simp [Ty.size, splitT.left_lt]
              right_lt := by
                simp [Ty.size, splitT.right_lt]
              toUnion := by
                exact .trans
                  (.interIntro
                    (.trans (.interLeft .refl) splitT.toUnion)
                    (.interRight .refl))
                  subtype_inter_union_normalize_left_to
              fromUnion := by
                exact .trans
                  subtype_inter_union_normalize_left_from
                  (.interIntro
                    (.trans (.interLeft .refl) splitT.fromUnion)
                    (.interRight .refl)) }

theorem splitNonUnionFree_wf_left
    (hwfT : WellFormedTy ct T)
    (hnu : ¬ T.unionFree) :
    WellFormedTy ct (splitNonUnionFree T hnu).left := by
  induction T with
  | bottom =>
      cases hnu trivial
  | class_ _ =>
      cases hnu trivial
  | negClass _ =>
      cases hnu trivial
  | callable _ _ =>
      cases hnu trivial
  | union T U =>
      cases hwfT with
      | union hwfT hwfU =>
          simpa [splitNonUnionFree] using hwfT
  | intersection T U ihT ihU =>
      cases hwfT with
      | intersection hwfT hwfU =>
          by_cases hTuf : T.unionFree
          · have hUnu : ¬ U.unionFree := by
              intro hUuf
              exact hnu ⟨hTuf, hUuf⟩
            simpa [splitNonUnionFree, hTuf, hUnu] using
              (WellFormedTy.intersection hwfT (ihU hwfU hUnu))
          · simpa [splitNonUnionFree, hTuf] using
              (WellFormedTy.intersection (ihT hwfT hTuf) hwfU)

theorem splitNonUnionFree_wf_right
    (hwfT : WellFormedTy ct T)
    (hnu : ¬ T.unionFree) :
    WellFormedTy ct (splitNonUnionFree T hnu).right := by
  induction T with
  | bottom =>
      cases hnu trivial
  | class_ _ =>
      cases hnu trivial
  | negClass _ =>
      cases hnu trivial
  | callable _ _ =>
      cases hnu trivial
  | union T U =>
      cases hwfT with
      | union hwfT hwfU =>
          simpa [splitNonUnionFree] using hwfU
  | intersection T U ihT ihU =>
      cases hwfT with
      | intersection hwfT hwfU =>
          by_cases hTuf : T.unionFree
          · have hUnu : ¬ U.unionFree := by
              intro hUuf
              exact hnu ⟨hTuf, hUuf⟩
            simpa [splitNonUnionFree, hTuf, hUnu] using
              (WellFormedTy.intersection hwfT (ihU hwfU hUnu))
          · simpa [splitNonUnionFree, hTuf] using
              (WellFormedTy.intersection (ihT hwfT hTuf) hwfU)

theorem interAtoms_member_wellFormed
    (hwfT : WellFormedTy ct T)
    (huf : T.unionFree)
    (hmem : A ∈ T.interAtoms) :
    WellFormedTy ct A := by
  induction T generalizing A with
  | bottom =>
      cases hwfT
      simp [Ty.interAtoms] at hmem
      subst hmem
      exact .bottom
  | class_ C =>
      cases hwfT with
      | class_ hfind hmro =>
          simp [Ty.interAtoms] at hmem
          subst hmem
          exact .class_ hfind hmro
  | negClass C =>
      cases hwfT with
      | negClass hfind hmro =>
          simp [Ty.interAtoms] at hmem
          subst hmem
          exact .negClass hfind hmro
  | callable P R ihP ihR =>
      cases hwfT with
      | callable hwfP hwfR =>
          simp [Ty.interAtoms] at hmem
          subst hmem
          exact .callable hwfP hwfR
  | union T U ihT ihU =>
      cases huf
  | intersection T U ihT ihU =>
      cases hwfT with
      | intersection hwfT hwfU =>
          rcases huf with ⟨hufT, hufU⟩
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact ihT hwfT hufT hmem
          · exact ihU hwfU hufU hmem

theorem unionAtoms_member_wellFormed
    (hwfT : WellFormedTy ct T)
    (hmem : A ∈ T.unionAtoms) :
    WellFormedTy ct A := by
  induction T generalizing A with
  | bottom =>
      cases hwfT
      simp [Ty.unionAtoms] at hmem
      subst hmem
      exact .bottom
  | class_ C =>
      cases hwfT with
      | class_ hfind hmro =>
          simp [Ty.unionAtoms] at hmem
          subst hmem
          exact .class_ hfind hmro
  | negClass C =>
      cases hwfT with
      | negClass hfind hmro =>
          simp [Ty.unionAtoms] at hmem
          subst hmem
          exact .negClass hfind hmro
  | callable P R ihP ihR =>
      cases hwfT with
      | callable hwfP hwfR =>
          simp [Ty.unionAtoms] at hmem
          subst hmem
          exact .callable hwfP hwfR
  | union T U ihT ihU =>
      cases hwfT with
      | union hwfT hwfU =>
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact ihT hwfT hmem
          · exact ihU hwfU hmem
  | intersection T U ihT ihU =>
      cases hwfT with
      | intersection hwfT hwfU =>
          simp [Ty.unionAtoms] at hmem
          subst hmem
          exact .intersection hwfT hwfU

theorem Ty.interAtoms_ne_nil (T : Ty) : T.interAtoms ≠ [] := by
  induction T with
  | class_ | negClass | callable | union | bottom => simp [Ty.interAtoms]
  | intersection T U ihT ihU =>
      simp [Ty.interAtoms, ihT, ihU]

theorem interAtoms_length_pos (T : Ty) : 1 ≤ T.interAtoms.length := by
  cases hatoms : T.interAtoms with
  | nil => exact absurd hatoms T.interAtoms_ne_nil
  | cons _ _ => simp

theorem size_eq_tySizeSum_interAtoms (S : Ty) :
    S.size + 1 = tySizeSum S.interAtoms + S.interAtoms.length := by
  induction S with
  | bottom | class_ | negClass | callable | union =>
      simp [Ty.size, Ty.interAtoms, tySizeSum]
  | intersection T U ihT ihU =>
      calc
        (Ty.intersection T U).size + 1
            = (T.size + 1) + (U.size + 1) := by
                simp [Ty.size]
                omega
        _ = (tySizeSum T.interAtoms + T.interAtoms.length) +
              (tySizeSum U.interAtoms + U.interAtoms.length) := by
              rw [ihT, ihU]
        _ = tySizeSum (Ty.intersection T U).interAtoms + (Ty.intersection T U).interAtoms.length := by
              simp [Ty.interAtoms, tySizeSum_append, List.length_append]
              omega

theorem Ty.unionAtoms_ne_nil (T : Ty) : T.unionAtoms ≠ [] := by
  induction T with
  | class_ | negClass | callable | intersection | bottom => simp [Ty.unionAtoms]
  | union T U ihT ihU =>
      simp [Ty.unionAtoms, ihT, ihU]

theorem interAtomsFold_projection
    (hmem : A ∈ atoms) :
    IsSubtype ct (Ty.interAtomsFold atoms) A := by
  induction atoms generalizing A with
  | nil => cases hmem
  | cons T Ts ih =>
      cases Ts with
      | nil =>
          simp at hmem
          subst hmem
          exact .refl
      | cons U Us =>
          simp [Ty.interAtomsFold] at hmem ⊢
          rcases hmem with rfl | hmem
          · exact .interLeft .refl
          · exact .interRight (ih (by simpa using hmem))

theorem semDenotes_interAtomsFold_intro
    (hall : ∀ A, A ∈ atoms → Ty.semDenotes ct A obj) :
    Ty.semDenotes ct (Ty.interAtomsFold atoms) obj := by
  induction atoms with
  | nil =>
      simpa [Ty.interAtomsFold, Ty.semDenotes, SemObject.hasAncestor] using
        (SemObject.object_mem (ct := ct) obj)
  | cons A As ih =>
      cases As with
      | nil =>
          simpa [Ty.interAtomsFold] using hall A (by simp)
      | cons B Bs =>
          simp [Ty.interAtomsFold, Ty.semDenotes]
          exact ⟨hall A (by simp), ih (fun X hX => hall X (by simp [hX]))⟩

theorem subtype_interAtomsFold_intro
    (hall : ∀ A, A ∈ atoms → IsSubtype ct T A) :
    IsSubtype ct T (Ty.interAtomsFold atoms) := by
  induction atoms generalizing T with
  | nil =>
      simp [Ty.interAtomsFold]
      exact .objectTop
  | cons A As ih =>
      cases As with
      | nil =>
          simpa [Ty.interAtomsFold] using hall A (by simp)
      | cons B Bs =>
          simp [Ty.interAtomsFold]
          refine .interIntro ?_ ?_
          · exact hall A (by simp)
          · exact ih (fun X hX => hall X (by simp [hX]))

theorem interAtomsFold_subtype_of_subset
    (hsub : ∀ A, A ∈ atoms₁ → A ∈ atoms₂) :
    IsSubtype ct (Ty.interAtomsFold atoms₂) (Ty.interAtomsFold atoms₁) :=
  subtype_interAtomsFold_intro (ct := ct) (T := Ty.interAtomsFold atoms₂) fun A hA =>
    interAtomsFold_projection (ct := ct) (A := A) (atoms := atoms₂) (hsub A hA)

theorem interAtomsFold_append_to_inter :
    IsSubtype ct
      (Ty.interAtomsFold (atoms₁ ++ atoms₂))
      (.intersection (Ty.interAtomsFold atoms₁) (Ty.interAtomsFold atoms₂)) := by
  refine .interIntro ?_ ?_
  · exact interAtomsFold_subtype_of_subset
      (ct := ct)
      (atoms₁ := atoms₁)
      (atoms₂ := atoms₁ ++ atoms₂)
      (fun A hA => List.mem_append_left _ hA)
  · exact interAtomsFold_subtype_of_subset
      (ct := ct)
      (atoms₁ := atoms₂)
      (atoms₂ := atoms₁ ++ atoms₂)
      (fun A hA => List.mem_append_right _ hA)

theorem interAtomsFold_inter_to_append :
    IsSubtype ct
      (.intersection (Ty.interAtomsFold atoms₁) (Ty.interAtomsFold atoms₂))
      (Ty.interAtomsFold (atoms₁ ++ atoms₂)) := by
  refine subtype_interAtomsFold_intro (ct := ct) (T := .intersection (Ty.interAtomsFold atoms₁) (Ty.interAtomsFold atoms₂)) ?_
  intro A hA
  rcases List.mem_append.mp hA with hA | hA
  · exact .interLeft (interAtomsFold_projection (ct := ct) (A := A) (atoms := atoms₁) hA)
  · exact .interRight (interAtomsFold_projection (ct := ct) (A := A) (atoms := atoms₂) hA)

theorem unionAtomsFold_injection
    (hmem : A ∈ atoms) :
    IsSubtype ct A (Ty.unionAtomsFold atoms) := by
  induction atoms generalizing A with
  | nil =>
      cases hmem
  | cons T Ts ih =>
      cases Ts with
      | nil =>
          simp at hmem
          subst hmem
          exact .refl
      | cons U Us =>
          simp [Ty.unionAtomsFold] at hmem ⊢
          rcases hmem with rfl | hmem
          · exact .unionLeft .refl
          · exact .trans (ih (by simpa using hmem)) (.unionRight .refl)

theorem unionAtomsFold_elim
    (hall : ∀ A, A ∈ atoms → IsSubtype ct A T) :
    IsSubtype ct (Ty.unionAtomsFold atoms) T := by
  induction atoms with
  | nil =>
      simp [Ty.unionAtomsFold]
      exact .bottom
  | cons A As ih =>
      cases As with
      | nil =>
          simpa [Ty.unionAtomsFold] using hall A (by simp)
      | cons B Bs =>
          simp [Ty.unionAtomsFold]
          exact .unionElim
            (hall A (by simp))
            (ih (fun X hX => hall X (by simp [hX])))

theorem unionAtomsFold_wellFormed
    (hall : ∀ A, A ∈ atoms → WellFormedTy ct A) :
    WellFormedTy ct (Ty.unionAtomsFold atoms) := by
  induction atoms with
  | nil =>
      exact .bottom
  | cons A As ih =>
      cases As with
      | nil =>
          simpa [Ty.unionAtomsFold] using hall A (by simp)
      | cons B Bs =>
          simp [Ty.unionAtomsFold]
          exact .union
            (hall A (by simp))
            (ih (fun X hX => hall X (by simp [hX])))

theorem unionAtomsFold_append_left :
    IsSubtype ct
      (Ty.unionAtomsFold atoms₁)
      (Ty.unionAtomsFold (atoms₁ ++ atoms₂)) :=
  unionAtomsFold_elim (ct := ct) (T := Ty.unionAtomsFold (atoms₁ ++ atoms₂)) fun A hA =>
    unionAtomsFold_injection (ct := ct) (A := A) (atoms := atoms₁ ++ atoms₂)
      (List.mem_append_left _ hA)

theorem unionAtomsFold_append_right :
    IsSubtype ct
      (Ty.unionAtomsFold atoms₂)
      (Ty.unionAtomsFold (atoms₁ ++ atoms₂)) :=
  unionAtomsFold_elim (ct := ct) (T := Ty.unionAtomsFold (atoms₁ ++ atoms₂)) fun A hA =>
    unionAtomsFold_injection (ct := ct) (A := A) (atoms := atoms₁ ++ atoms₂)
      (List.mem_append_right _ hA)

theorem unionAtomsFold_subtype_of_subset
    (hsub : ∀ A, A ∈ atoms₁ → A ∈ atoms₂) :
    IsSubtype ct (Ty.unionAtomsFold atoms₁) (Ty.unionAtomsFold atoms₂) :=
  unionAtomsFold_elim (ct := ct) (T := Ty.unionAtomsFold atoms₂) fun A hA =>
    unionAtomsFold_injection (ct := ct) (A := A) (atoms := atoms₂) (hsub A hA)

theorem subtype_self_unionAtomsFold :
    IsSubtype ct T (Ty.unionAtomsFold T.unionAtoms) := by
  induction T with
  | class_ | negClass | callable | intersection | bottom =>
      simp [Ty.unionAtoms, Ty.unionAtomsFold]
      exact .refl
  | union T U ihT ihU =>
      exact .unionElim
        (.trans ihT (unionAtomsFold_append_left (ct := ct) (atoms₁ := T.unionAtoms) (atoms₂ := U.unionAtoms)))
        (.trans ihU (unionAtomsFold_append_right (ct := ct) (atoms₁ := T.unionAtoms) (atoms₂ := U.unionAtoms)))

theorem unionAtomsFold_subtype_self :
    IsSubtype ct (Ty.unionAtomsFold T.unionAtoms) T := by
  induction T with
  | class_ | negClass | callable | intersection | bottom =>
      simp [Ty.unionAtoms, Ty.unionAtomsFold]
      exact .refl
  | union T U ihT ihU =>
      refine unionAtomsFold_elim (ct := ct) (T := .union T U) ?_
      intro A hA
      rcases List.mem_append.mp hA with hA | hA
      · exact .trans
          (unionAtomsFold_injection (ct := ct) (A := A) (atoms := T.unionAtoms) hA)
          <| .trans
            ihT
          (.unionLeft .refl)
      · exact .trans
          (unionAtomsFold_injection (ct := ct) (A := A) (atoms := U.unionAtoms) hA)
          <| .trans
            ihU
          (.unionRight .refl)

theorem unionAtomsFold_append_size
    (h₁ : atoms₁ ≠ [])
    (h₂ : atoms₂ ≠ []) :
    (Ty.unionAtomsFold (atoms₁ ++ atoms₂)).size =
      (Ty.unionAtomsFold atoms₁).size + (Ty.unionAtomsFold atoms₂).size + 1 := by
  induction atoms₁ with
  | nil =>
      cases h₁ rfl
  | cons A As ih =>
      cases As with
      | nil =>
          simp [Ty.unionAtomsFold, Ty.size]
          omega
      | cons B Bs =>
          have htail : B :: Bs ≠ [] := by simp
          have ih' := ih htail
          simpa [Ty.unionAtomsFold, Ty.size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            congrArg (fun n => A.size + n + 1) ih'

theorem unionAtomsFold_size_eq_self (T : Ty) :
    (Ty.unionAtomsFold T.unionAtoms).size = T.size := by
  induction T with
  | bottom | class_ | negClass | callable | intersection =>
      simp [Ty.unionAtoms, Ty.unionAtomsFold, Ty.size]
  | union T U ihT ihU =>
      have hT : T.unionAtoms ≠ [] := Ty.unionAtoms_ne_nil T
      have hU : U.unionAtoms ≠ [] := Ty.unionAtoms_ne_nil U
      rw [Ty.unionAtoms, unionAtomsFold_append_size hT hU, ihT, ihU]
      simp [Ty.size]
      omega

theorem pickUsefulUnionArm_rest_size_lt
    (h : pickUsefulUnionArm atoms = some (A, rest)) :
    rest ≠ [] →
    (Ty.unionAtomsFold rest).size < (Ty.unionAtomsFold atoms).size := by
  induction atoms generalizing A rest with
  | nil =>
      simp [pickUsefulUnionArm] at h
  | cons B Bs ih =>
      unfold pickUsefulUnionArm at h
      by_cases hB : usefulUnionArm B = true
      · simp [hB] at h
        rcases h with ⟨rfl, rfl⟩
        intro hrest
        cases Bs with
        | nil =>
            cases hrest rfl
        | cons C Cs =>
            simp [Ty.unionAtomsFold, Ty.size]
            omega
      · simp [hB] at h
        cases hpick : pickUsefulUnionArm Bs with
        | none =>
            simp [hpick] at h
        | some pair =>
            rcases pair with ⟨C, Cs⟩
            simp [hpick] at h
            rcases h with ⟨rfl, rfl⟩
            intro _hrest
            cases Cs with
            | nil =>
                cases Bs with
                | nil =>
                    cases hpick
                | cons D Ds =>
                    simp [Ty.unionAtomsFold, Ty.size] at hpick ⊢
                    omega
            | cons E Es =>
                have ih' : (Ty.unionAtomsFold (E :: Es)).size < (Ty.unionAtomsFold Bs).size :=
                  ih hpick (by simp)
                cases Bs with
                | nil =>
                    cases hpick
                | cons D Ds =>
                    simp [Ty.unionAtomsFold, Ty.size] at ih' ⊢
                    omega

theorem pickUsefulUnionArm_spec_some
    (h : pickUsefulUnionArm atoms = some (A, rest)) :
    A ∈ atoms ∧ usefulUnionArm A = true ∧
      (∀ X, X ∈ rest → X ∈ atoms) ∧
      (∀ X, X ∈ atoms → X = A ∨ X ∈ rest) := by
  induction atoms generalizing A rest with
  | nil =>
      simp [pickUsefulUnionArm] at h
  | cons B Bs ih =>
      unfold pickUsefulUnionArm at h
      by_cases hB : usefulUnionArm B = true
      · simp [hB] at h
        rcases h with ⟨hA, hrest⟩
        subst hA
        subst hrest
        refine ⟨by simp, hB, ?_, ?_⟩
        · intro X hX
          exact List.mem_cons_of_mem _ hX
        · intro X hX
          rcases List.mem_cons.mp hX with rfl | hX
          · exact Or.inl rfl
          · exact Or.inr hX
      · simp [hB] at h
        cases hpick : pickUsefulUnionArm Bs with
        | none =>
            simp [hpick] at h
        | some pair =>
            rcases pair with ⟨C, Cs⟩
            simp [hpick] at h
            rcases h with ⟨hA, hrest⟩
            subst hA
            subst hrest
            rcases ih hpick with ⟨hmemA, huseful, hrestSubset, hcover⟩
            refine ⟨List.mem_cons_of_mem _ hmemA, huseful, ?_, ?_⟩
            · intro X hX
              rcases List.mem_cons.mp hX with rfl | hX
              · exact List.Mem.head _
              · exact List.mem_cons_of_mem _ (hrestSubset X hX)
            · intro X hX
              rcases List.mem_cons.mp hX with rfl | hX
              · exact Or.inr (List.Mem.head _)
              · rcases hcover X hX with rfl | hXin
                · exact Or.inl rfl
                · exact Or.inr (List.mem_cons_of_mem _ hXin)

theorem pickUsefulUnionArm_spec_none
    (h : pickUsefulUnionArm atoms = none) :
    ∀ A, A ∈ atoms → usefulUnionArm A = false := by
  induction atoms with
  | nil =>
      intro A hA
      cases hA
  | cons B Bs ih =>
      unfold pickUsefulUnionArm at h
      by_cases hB : usefulUnionArm B = true
      · simp [hB] at h
      · cases htail : pickUsefulUnionArm Bs with
        | none =>
            simp [hB, htail] at h
            intro A hA
            rcases List.mem_cons.mp hA with hEq | hA
            · subst A
              cases hUB : usefulUnionArm B <;> simp [hUB] at hB ⊢
            · exact ih htail A hA
        | some pair =>
            simp [hB, htail] at h

theorem pickUsefulUnionArm_length
    (h : pickUsefulUnionArm atoms = some (A, rest)) :
    rest.length + 1 = atoms.length := by
  induction atoms generalizing A rest with
  | nil =>
      simp [pickUsefulUnionArm] at h
  | cons B Bs ih =>
      unfold pickUsefulUnionArm at h
      by_cases hB : usefulUnionArm B = true
      · simp [hB] at h
        rcases h with ⟨rfl, rfl⟩
        simp
      · simp [hB] at h
        cases hpick : pickUsefulUnionArm Bs with
        | none =>
            simp [hpick] at h
        | some pair =>
            rcases pair with ⟨C, Cs⟩
            simp [hpick] at h
            rcases h with ⟨rfl, rfl⟩
            have ih' : Cs.length + 1 = Bs.length := ih hpick
            simp [ih']

theorem pickUsefulUnionArm_sizeSum
    (h : pickUsefulUnionArm atoms = some (A, rest)) :
    tySizeSum rest + A.size = tySizeSum atoms := by
  induction atoms generalizing A rest with
  | nil =>
      simp [pickUsefulUnionArm] at h
  | cons B Bs ih =>
      unfold pickUsefulUnionArm at h
      by_cases hB : usefulUnionArm B = true
      · simp [hB] at h
        rcases h with ⟨rfl, rfl⟩
        simp [tySizeSum, Nat.add_comm]
      · simp [hB] at h
        cases hpick : pickUsefulUnionArm Bs with
        | none =>
            simp [hpick] at h
        | some pair =>
            rcases pair with ⟨C, Cs⟩
            simp [hpick] at h
            rcases h with ⟨rfl, rfl⟩
            have ih' : tySizeSum Cs + C.size = tySizeSum Bs := ih hpick
            simp [tySizeSum, Nat.add_assoc, Nat.add_comm] at ih' ⊢
            omega

theorem unionAtomsFold_size_formula
    (h : atoms ≠ []) :
    (Ty.unionAtomsFold atoms).size = tySizeSum atoms + atoms.length - 1 := by
  induction atoms with
  | nil =>
      cases h rfl
  | cons A As ih =>
      cases As with
      | nil =>
          simp [Ty.unionAtomsFold, tySizeSum]
      | cons B Bs =>
          have htail : B :: Bs ≠ [] := by simp
          have ih' := ih htail
          simp [Ty.unionAtomsFold, tySizeSum, ih', Ty.size]
          omega

theorem pickUsefulUnionArm_atomic_rest_size
    (hpick : pickUsefulUnionArm atoms = some (A, rest))
    (hrest : rest ≠ [])
    (hA : A.size = 1) :
    (Ty.unionAtomsFold rest).size + 2 = (Ty.unionAtomsFold atoms).size := by
  have hsum : tySizeSum rest + A.size = tySizeSum atoms :=
    pickUsefulUnionArm_sizeSum hpick
  have hlen : rest.length + 1 = atoms.length :=
    pickUsefulUnionArm_length hpick
  have hsizeRest :
      (Ty.unionAtomsFold rest).size = tySizeSum rest + rest.length - 1 :=
    unionAtomsFold_size_formula hrest
  have hatoms_ne : atoms ≠ [] := by
    intro hatoms_nil
    simp [pickUsefulUnionArm, hatoms_nil] at hpick
  have hsizeAtoms :
      (Ty.unionAtomsFold atoms).size = tySizeSum atoms + atoms.length - 1 :=
    unionAtomsFold_size_formula hatoms_ne
  have hrest_sum_pos : 1 ≤ tySizeSum rest + rest.length := by
    cases rest with
    | nil =>
        cases hrest rfl
    | cons B Bs =>
        have hBsize : 1 ≤ B.size := Ty.size_pos (T := B)
        simp [tySizeSum]
        omega
  have hsum' : tySizeSum atoms = tySizeSum rest + 1 := by
    simpa [hA, Nat.add_comm] using hsum.symm
  calc
    (Ty.unionAtomsFold rest).size + 2
        = (tySizeSum rest + rest.length - 1) + 2 := by
            rw [hsizeRest]
    _ = tySizeSum rest + rest.length + 1 := by
          omega
    _ = tySizeSum atoms + atoms.length - 1 := by
          rw [hsum', ← hlen]
          omega
    _ = (Ty.unionAtomsFold atoms).size := by
          rw [hsizeAtoms]

theorem subtype_self_interAtomsFold
    (huf : T.unionFree) :
    IsSubtype ct T (Ty.interAtomsFold T.interAtoms) := by
  induction T with
  | class_ | negClass | callable | bottom =>
      simp [Ty.unionFree, Ty.interAtoms, Ty.interAtomsFold] at huf ⊢
      exact .refl
  | union T U =>
      cases huf
  | intersection T U ihT ihU =>
      rcases huf with ⟨hufT, hufU⟩
      exact .trans
        (.interIntro
          (.interLeft (ihT hufT))
          (.interRight (ihU hufU)))
        (interAtomsFold_inter_to_append (ct := ct) (atoms₁ := T.interAtoms) (atoms₂ := U.interAtoms))

theorem interAtomsFold_subtype_self
    (huf : T.unionFree) :
    IsSubtype ct (Ty.interAtomsFold T.interAtoms) T := by
  induction T with
  | class_ | negClass | callable | bottom =>
      simp [Ty.unionFree, Ty.interAtoms, Ty.interAtomsFold] at huf ⊢
      exact .refl
  | union T U =>
      cases huf
  | intersection T U ihT ihU =>
      rcases huf with ⟨hufT, hufU⟩
      exact .trans
        (interAtomsFold_append_to_inter (ct := ct) (atoms₁ := T.interAtoms) (atoms₂ := U.interAtoms))
        (.interIntro
          (.interLeft (ihT hufT))
          (.interRight (ihU hufU)))

theorem interAtoms_projection
    (huf : T.unionFree)
    (hmem : A ∈ T.interAtoms) :
    IsSubtype ct T A :=
  .trans (subtype_self_interAtomsFold (ct := ct) (T := T) huf)
    (interAtomsFold_projection (ct := ct) (A := A) (atoms := T.interAtoms) hmem)

def callableAtomTy (pr : Ty × Ty) : Ty :=
  .callable pr.1 pr.2

theorem callableAtomTy_size (pr : Ty × Ty) :
    (callableAtomTy pr).size = 1 + pr.1.size + pr.2.size := by
  cases pr
  simp [callableAtomTy, Ty.size]

theorem interAtoms_callable_projection
    (huf : T.unionFree)
    (callAtoms : List (Ty × Ty))
    (hsub : ∀ pr, pr ∈ callAtoms → callableAtomTy pr ∈ T.interAtoms) :
    IsSubtype ct T (Ty.interAtomsFold (callAtoms.map callableAtomTy)) := by
  refine subtype_interAtomsFold_intro (ct := ct) (T := T) ?_
  intro A hA
  rcases List.mem_map.mp hA with ⟨pr, hpr, rfl⟩
  exact interAtoms_projection (ct := ct) (T := T) (A := callableAtomTy pr) huf (hsub pr hpr)

def callableParamsUnion : List (Ty × Ty) → Ty
  | [] => .bottom
  | [pr] => pr.1
  | pr :: prs => .union pr.1 (callableParamsUnion prs)

def callableReturnsInter : List (Ty × Ty) → Ty
  | [] => .class_ objectClass
  | [pr] => pr.2
  | pr :: prs => .intersection pr.2 (callableReturnsInter prs)

theorem callableParamsUnion_size_formula
    (hcall : callAtoms ≠ []) :
    (callableParamsUnion callAtoms).size + 1 =
      tySizeSum (callAtoms.map Prod.fst) + callAtoms.length := by
  induction callAtoms with
  | nil =>
      cases hcall rfl
  | cons pr prs ih =>
      cases prs with
      | nil =>
          simp [callableParamsUnion, tySizeSum]
      | cons pr₂ prs₂ =>
          have htail : pr₂ :: prs₂ ≠ [] := by simp
          cases pr with
          | mk P R =>
              have ih' := ih htail
              have ih'' :
                  (callableParamsUnion (pr₂ :: prs₂)).size + 1 =
                    pr₂.fst.size + tySizeSum (List.map Prod.fst prs₂) + (prs₂.length + 1) := by
                simpa [tySizeSum, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih'
              simp [callableParamsUnion, tySizeSum, Ty.size]
              omega

theorem callableReturnsInter_size_formula
    (hcall : callAtoms ≠ []) :
    (callableReturnsInter callAtoms).size + 1 =
      tySizeSum (callAtoms.map Prod.snd) + callAtoms.length := by
  induction callAtoms with
  | nil =>
      cases hcall rfl
  | cons pr prs ih =>
      cases prs with
      | nil =>
          simp [callableReturnsInter, tySizeSum]
      | cons pr₂ prs₂ =>
          have htail : pr₂ :: prs₂ ≠ [] := by simp
          cases pr with
          | mk P R =>
              have ih' := ih htail
              have ih'' :
                  (callableReturnsInter (pr₂ :: prs₂)).size + 1 =
                    pr₂.snd.size + tySizeSum (List.map Prod.snd prs₂) + (prs₂.length + 1) := by
                simpa [tySizeSum, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih'
              simp [callableReturnsInter, tySizeSum, Ty.size]
              omega

theorem tySizeSum_map_callableAtoms
    (callAtoms : List (Ty × Ty)) :
    tySizeSum (callAtoms.map callableAtomTy) =
      tySizeSum (callAtoms.map Prod.fst) +
        tySizeSum (callAtoms.map Prod.snd) +
        callAtoms.length := by
  induction callAtoms with
  | nil =>
      simp [tySizeSum]
  | cons pr prs ih =>
      cases pr
      simp [tySizeSum, callableAtomTy_size, ih]
      omega

theorem callableParamsUnion_size_le_callAtoms
    (hcall : callAtoms ≠ []) :
    (callableParamsUnion callAtoms).size ≤
      tySizeSum (callAtoms.map callableAtomTy) := by
  have hsize := callableParamsUnion_size_formula (callAtoms := callAtoms) hcall
  have hsum := tySizeSum_map_callableAtoms callAtoms
  omega

theorem callableReturnsInter_size_le_callAtoms
    (hcall : callAtoms ≠ []) :
    (callableReturnsInter callAtoms).size ≤
      tySizeSum (callAtoms.map callableAtomTy) := by
  have hsize := callableReturnsInter_size_formula (callAtoms := callAtoms) hcall
  have hsum := tySizeSum_map_callableAtoms callAtoms
  omega

theorem callableParamsUnion_contains
    (hmem : pr ∈ callAtoms) :
    IsSubtype ct pr.1 (callableParamsUnion callAtoms) := by
  induction callAtoms with
  | nil =>
      cases hmem
  | cons hd tl ih =>
      cases tl with
      | nil =>
          simp at hmem
          rcases hmem with rfl
          exact .refl
      | cons hd₂ tl₂ =>
          simp [callableParamsUnion] at hmem ⊢
          rcases hmem with rfl | hmem
          · exact .unionLeft .refl
          · have htail : pr ∈ hd₂ :: tl₂ := by simpa using hmem
            exact .trans (ih htail) (.unionRight .refl)

theorem callableReturnsInter_projects
    (hmem : pr ∈ callAtoms) :
    IsSubtype ct (callableReturnsInter callAtoms) pr.2 := by
  induction callAtoms with
  | nil =>
      cases hmem
  | cons hd tl ih =>
      cases tl with
      | nil =>
          simp at hmem
          rcases hmem with rfl
          exact .refl
      | cons hd₂ tl₂ =>
          simp [callableReturnsInter] at hmem ⊢
          rcases hmem with rfl | hmem
          · exact .interLeft .refl
          · have htail : pr ∈ hd₂ :: tl₂ := by simpa using hmem
            exact .trans (.interRight .refl) (ih htail)

theorem callableParamsUnion_wellFormed
    (hall : ∀ pr, pr ∈ callAtoms → WellFormedTy ct pr.1) :
    WellFormedTy ct (callableParamsUnion callAtoms) := by
  induction callAtoms with
  | nil =>
      simp [callableParamsUnion]
      exact .bottom
  | cons hd tl ih =>
      cases tl with
      | nil =>
          simpa [callableParamsUnion] using hall hd (by simp)
      | cons hd₂ tl₂ =>
          simp [callableParamsUnion]
          exact .union
            (hall hd (by simp))
            (ih (fun pr hpr => hall pr (by simp [hpr])))

theorem callableReturnsInter_wellFormed
    (hwfct : WellFormedClassTable ct)
    (hall : ∀ pr, pr ∈ callAtoms → WellFormedTy ct pr.2) :
    WellFormedTy ct (callableReturnsInter callAtoms) := by
  induction callAtoms with
  | nil =>
      simp [callableReturnsInter]
      exact wellFormed_object_type (ct := ct) hwfct
  | cons hd tl ih =>
      cases tl with
      | nil =>
          simpa [callableReturnsInter] using hall hd (by simp)
      | cons hd₂ tl₂ =>
          simp [callableReturnsInter]
          exact .intersection
            (hall hd (by simp))
            (ih (fun pr hpr => hall pr (by simp [hpr])))

theorem boundMethodObj_denotes_callable_of_mem
    (hwfct : WellFormedClassTable ct)
    (hmem : pr ∈ callAtoms) :
    Ty.semDenotes ct (.callable pr.1 pr.2)
      (boundMethodObj (ct := ct) hwfct
        (callableParamsUnion callAtoms) (callableReturnsInter callAtoms)) := by
  simp [boundMethodObj, Ty.semDenotes]
  exact ⟨callableParamsUnion_contains (ct := ct) (pr := pr) (callAtoms := callAtoms) hmem,
    callableReturnsInter_projects (ct := ct) (pr := pr) (callAtoms := callAtoms) hmem⟩

theorem callable_atoms_summary
    (hcall : callAtoms ≠ []) :
    IsSubtype ct
      (Ty.interAtomsFold (callAtoms.map callableAtomTy))
      (.callable (callableParamsUnion callAtoms) (callableReturnsInter callAtoms)) := by
  cases callAtoms with
  | nil => cases hcall rfl
  | cons pr rest =>
      cases rest with
      | nil =>
          cases pr
          simp [callableParamsUnion, callableReturnsInter, callableAtomTy, Ty.interAtomsFold]
          exact .refl
      | cons pr₂ rest₂ =>
          cases pr with
          | mk P R =>
              have htail : pr₂ :: rest₂ ≠ [] := by simp
              have ih := callable_atoms_summary
                (ct := ct)
                (callAtoms := pr₂ :: rest₂)
                htail
              simpa [callableParamsUnion, callableReturnsInter, callableAtomTy, Ty.interAtomsFold] using
                (.trans
                  (.interIntro
                    (.interLeft .refl)
                    (.interRight ih))
                  .callableInterUnion)

theorem source_projects_callable_summary
    (huf : T.unionFree)
    (callAtoms : List (Ty × Ty))
    (hcall : callAtoms ≠ [])
    (hsub : ∀ pr, pr ∈ callAtoms → callableAtomTy pr ∈ T.interAtoms) :
    IsSubtype ct T
      (.callable (callableParamsUnion callAtoms) (callableReturnsInter callAtoms)) :=
  .trans
    (interAtoms_callable_projection (ct := ct) (T := T) huf callAtoms hsub)
    (callable_atoms_summary (ct := ct) (callAtoms := callAtoms) hcall)

