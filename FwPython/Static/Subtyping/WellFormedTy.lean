import FwPython.Static.Subtyping.Core

/-! ## `WellFormedTy` helper lemmas -/

theorem WellFormedTy.class_find
    (hwf : WellFormedTy ct (.class_ C)) :
    ∃ cls mro, findClass ct C = some cls ∧ ComputeMro ct cls mro := by
  cases hwf with
  | class_ hfind hmro => exact ⟨_, _, hfind, hmro⟩

theorem WellFormedTy.class_find_ne_none
    (hwf : WellFormedTy ct (.class_ C)) :
    findClass ct C ≠ none := by
  cases hwf with
  | class_ hfind _ =>
      rw [hfind]
      simp

theorem WellFormedTy.negClass_find
    (hwf : WellFormedTy ct (.negClass C)) :
    ∃ cls mro, findClass ct C = some cls ∧ ComputeMro ct cls mro := by
  cases hwf with
  | negClass hfind hmro => exact ⟨_, _, hfind, hmro⟩

theorem WellFormedTy.negClass_find_ne_none
    (hwf : WellFormedTy ct (.negClass C)) :
    findClass ct C ≠ none := by
  cases hwf with
  | negClass hfind _ =>
      rw [hfind]
      simp

theorem WellFormedTy.union_left
    (hwf : WellFormedTy ct (.union T U)) :
    WellFormedTy ct T := by
  cases hwf with
  | union hwfT _ => exact hwfT

theorem WellFormedTy.union_right
    (hwf : WellFormedTy ct (.union T U)) :
    WellFormedTy ct U := by
  cases hwf with
  | union _ hwfU => exact hwfU

theorem WellFormedTy.intersection_left
    (hwf : WellFormedTy ct (.intersection T U)) :
    WellFormedTy ct T := by
  cases hwf with
  | intersection hwfT _ => exact hwfT

theorem WellFormedTy.intersection_right
    (hwf : WellFormedTy ct (.intersection T U)) :
    WellFormedTy ct U := by
  cases hwf with
  | intersection _ hwfU => exact hwfU

theorem WellFormedTy.callable_param
    (hwf : WellFormedTy ct (.callable P R)) :
    WellFormedTy ct P := by
  cases hwf with
  | callable hwfP _ => exact hwfP

theorem WellFormedTy.callable_return
    (hwf : WellFormedTy ct (.callable P R)) :
    WellFormedTy ct R := by
  cases hwf with
  | callable _ hwfR => exact hwfR

theorem WellFormedTy.class_of_neg
    (hwf : WellFormedTy ct (.negClass C)) :
    WellFormedTy ct (.class_ C) := by
  rcases hwf.negClass_find with ⟨cls, mro, hfind, hmro⟩
  exact .class_ hfind hmro

theorem WellFormedTy.neg_of_class
    (hwf : WellFormedTy ct (.class_ C)) :
    WellFormedTy ct (.negClass C) := by
  rcases hwf.class_find with ⟨cls, mro, hfind, hmro⟩
  exact .negClass hfind hmro
