set_option autoImplicit false

/-! # List subsequences

`subsequences` lists every way to delete source entries while retaining order,
including the empty list. `nonemptySubsets` filters out that empty list. Both
enumerations treat repeated entries as distinct occurrences. For example,
selecting the first or second entry of `[A, A]` gives two copies of `[A]`. The
proofs show that every source sublist is enumerated and that each entry in an
enumerated list came from the source.
-/

/-- Lists obtained by deleting source entries, retaining order and counting repeated occurrences separately. -/
def subsequences {α : Type} : List α → List (List α)
  | [] => [[]]
  | head :: tail => subsequences tail ++ (subsequences tail).map (head :: ·)

/-- A list is enumerated exactly when it is a positional sublist of the source. -/
theorem mem_subsequences {α : Type} {chosen entries : List α} :
    chosen ∈ subsequences entries ↔ chosen.Sublist entries := by
  induction entries generalizing chosen with
  | nil => simp [subsequences]
  | cons head tail ih =>
      constructor
      · intro member
        simp only [subsequences, List.mem_append, List.mem_map] at member
        rcases member with member | ⟨_, member, rfl⟩
        · exact .cons head (ih.mp member)
        · exact .cons₂ head (ih.mp member)
      · intro included
        cases included with
        | cons _ sublist => exact List.mem_append_left _ (ih.mpr sublist)
        | cons₂ _ sublist => exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih.mpr sublist, rfl⟩)

/-- All nonempty subsequences of the source list, preserving order and repeated entries. -/
def nonemptySubsets {α : Type} (source : List α) : List (List α) :=
  (subsequences source).filter (fun subset => !subset.isEmpty)

/-- Membership in nonemptySubsets means being an enumerated subsequence other than the empty list. -/
theorem mem_nonemptySubsets {α : Type} {source subset : List α} :
    subset ∈ nonemptySubsets source ↔ subset ∈ subsequences source ∧ subset ≠ [] := by
  simp only [nonemptySubsets, List.mem_filter, Bool.not_eq_true', List.isEmpty_eq_false_iff]

/-- The only nonempty subsequence of a singleton source is that singleton. -/
theorem nonemptySubsets_singleton {α : Type} (entry : α) :
    nonemptySubsets [entry] = [[entry]] := rfl
