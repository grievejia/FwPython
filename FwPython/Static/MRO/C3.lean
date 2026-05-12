import FwPython.Common.Identifier

/-! # C3 merge machinery

Definitions and properties for the C3 linearization merge step. -/

/-- Constructive Boolean membership test for identifiers. -/
def containsIdentifier (x : Identifier) : List Identifier → Bool
  | [] => false
  | y :: ys => if y = x then true else containsIdentifier x ys

/-- Boolean membership reflects propositional membership. -/
theorem containsIdentifier_true_of_mem
    {x : Identifier} {l : List Identifier}
    (h : x ∈ l) :
    containsIdentifier x l = true := by
  induction l with
  | nil =>
      cases h
  | cons y ys ih =>
      rcases List.mem_cons.mp h with rfl | hmem
      · simp [containsIdentifier]
      · by_cases hyx : y = x
        · simp [containsIdentifier, hyx]
        · simp [containsIdentifier, hyx, ih hmem]

/-- Boolean membership soundly implies propositional membership. -/
theorem mem_of_containsIdentifier_true
    {x : Identifier} {l : List Identifier}
    (h : containsIdentifier x l = true) :
    x ∈ l := by
  induction l with
  | nil =>
      simp [containsIdentifier] at h
  | cons y ys ih =>
      by_cases hyx : y = x
      · simp [hyx]
      · simp [containsIdentifier, hyx] at h
        exact List.mem_cons_of_mem _ (ih h)

/-- Check if an identifier appears in the tail (non-head elements) of any list. -/
def inTailOfAny (x : Identifier) (lists : List (List Identifier)) : Bool :=
  lists.any fun l => match l with
    | [] => false
    | _ :: rest => containsIdentifier x rest

/-- Find the first valid merge candidate: a head of some non-empty list
    that does not appear in the tail of any list. Returns `none` if no
    valid head exists (inconsistent hierarchy). -/
def findGoodHead (lists : List (List Identifier)) : Option Identifier :=
  lists.findSome? fun l => match l with
    | [] => none
    | h :: _ => if inTailOfAny h lists then none else some h

/-- Remove an element from the head of every list where it appears as head. -/
def removeFromHeads (x : Identifier) (lists : List (List Identifier)) : List (List Identifier) :=
  lists.map fun l => match l with
    | [] => []
    | h :: rest => if h = x then rest else h :: rest

/-- Total number of elements across all lists — used as fuel for `c3MergeAux`. -/
def totalLength (lists : List (List Identifier)) : Nat :=
  lists.foldl (fun acc l => acc + l.length) 0

/-- C3 merge with explicit fuel. Each successful merge step removes one element,
    so `totalLength` is always sufficient fuel. -/
def c3MergeAux : Nat → List (List Identifier) → Option (List Identifier)
  | 0, lists => if lists.all List.isEmpty then some [] else none
  | n + 1, lists =>
    if lists.all List.isEmpty then some []
    else match findGoodHead lists with
      | none => none
      | some h => do
        let rest ← c3MergeAux n (removeFromHeads h lists)
        return h :: rest

/-- C3 merge: merge a list of linearizations into a single consistent order.
    Returns `none` when no consistent merge exists. -/
def c3Merge (lists : List (List Identifier)) : Option (List Identifier) :=
  c3MergeAux (totalLength lists) lists

/-! ## C3 merge properties -/

/-- If `x` is in some list in `lists` and `x ≠ h`, then `x` remains in some
    list in `removeFromHeads h lists`. -/
theorem mem_removeFromHeads_of_mem
    {lists : List (List Identifier)} {l : List Identifier} {x h : Identifier}
    (hlists : l ∈ lists) (hx : x ∈ l) (hne : x ≠ h) :
    ∃ l', l' ∈ removeFromHeads h lists ∧ x ∈ l' := by
  induction lists with
  | nil => exact absurd hlists List.not_mem_nil
  | cons l₀ rest ih =>
    rcases List.mem_cons.mp hlists with rfl | hmem
    · unfold removeFromHeads
      simp only [List.map, List.mem_cons]
      cases l with
      | nil => exact absurd hx List.not_mem_nil
      | cons hd tl =>
        by_cases hhd : hd = h
        · rcases List.mem_cons.mp hx with rfl | htl
          · exact absurd hhd hne
          · exact ⟨tl, Or.inl (by simp [hhd]), htl⟩
        · exact ⟨hd :: tl, Or.inl (by simp [hhd]), hx⟩
    · obtain ⟨l', hl', hxl'⟩ := ih hmem
      exact ⟨l', List.mem_cons_of_mem _ hl', hxl'⟩

/-- If `l'` is in `removeFromHeads h lists` and `x ∈ l'`, then `x` was in some list in `lists`. -/
theorem mem_of_mem_removeFromHeads
    {lists : List (List Identifier)} {l' : List Identifier} {x h : Identifier}
    (hl' : l' ∈ removeFromHeads h lists) (hx : x ∈ l') :
    ∃ l, l ∈ lists ∧ x ∈ l := by
  induction lists with
  | nil => simp [removeFromHeads] at hl'
  | cons l₀ rest ih =>
    simp only [removeFromHeads, List.map, List.mem_cons] at hl'
    rcases hl' with rfl | hmem
    · cases l₀ with
      | nil => exact ⟨[], List.Mem.head _, hx⟩
      | cons hd tl =>
        refine ⟨hd :: tl, List.Mem.head _, ?_⟩
        simp only at hx; split at hx
        · exact List.mem_cons_of_mem _ hx
        · exact hx
    · obtain ⟨l, hl, hxl⟩ := ih hmem
      exact ⟨l, List.mem_cons_of_mem _ hl, hxl⟩

/-- Completeness: if `c3MergeAux` succeeds, every element of every input list
    appears in the output. -/
theorem c3MergeAux_complete
    {n : Nat} {lists : List (List Identifier)} {result : List Identifier}
    (h : c3MergeAux n lists = some result) :
    ∀ l, l ∈ lists → ∀ x, x ∈ l → x ∈ result := by
  induction n generalizing lists result with
  | zero =>
    simp [c3MergeAux] at h
    obtain ⟨hempty, rfl⟩ := h
    intro l hl x hx
    rw [hempty l hl] at hx; exact absurd hx List.not_mem_nil
  | succ n ih =>
    unfold c3MergeAux at h
    split at h
    · -- all empty
      simp at h; subst h
      intro l hl x hx
      have := List.all_eq_true.mp ‹_› l hl
      simp [List.isEmpty_iff] at this
      rw [this] at hx; exact absurd hx List.not_mem_nil
    · -- not all empty; findGoodHead
      cases hfgh : findGoodHead lists with
      | none => simp [hfgh] at h
      | some gh =>
        simp [hfgh] at h
        cases hrest : c3MergeAux n (removeFromHeads gh lists) with
        | none => simp [hrest] at h
        | some rest =>
          simp [hrest] at h; subst h
          intro l hl x hx
          simp only [List.mem_cons]
          by_cases hxgh : x = gh
          · exact Or.inl hxgh
          · have ih' := ih hrest
            obtain ⟨l', hl', hxl'⟩ := mem_removeFromHeads_of_mem hl hx hxgh
            exact Or.inr (ih' l' hl' x hxl')

/-- Completeness for `c3Merge`. -/
theorem c3Merge_complete
    {lists : List (List Identifier)} {result : List Identifier}
    (h : c3Merge lists = some result) :
    ∀ l, l ∈ lists → ∀ x, x ∈ l → x ∈ result :=
  c3MergeAux_complete h

/-- `findGoodHead` returns a head of some list. -/
theorem findGoodHead_mem
    {lists : List (List Identifier)} {gh : Identifier}
    (hgh : findGoodHead lists = some gh) :
    ∃ l, l ∈ lists ∧ gh ∈ l := by
  unfold findGoodHead at hgh
  rw [List.findSome?_eq_some_iff] at hgh
  obtain ⟨l₁, a, l₂, heq, hsome, -⟩ := hgh
  cases a with
  | nil => simp at hsome
  | cons hd tl =>
    simp only at hsome
    split at hsome
    · exact absurd hsome (by simp)
    · simp at hsome; subst hsome
      exact ⟨hd :: tl, by subst heq; exact List.mem_append_right _ (List.Mem.head _), List.Mem.head _⟩

/-- Soundness: if x is in c3Merge output, it came from some input. -/
theorem c3MergeAux_sound
    {n : Nat} {lists : List (List Identifier)} {result : List Identifier}
    (h : c3MergeAux n lists = some result) :
    ∀ x, x ∈ result → ∃ l, l ∈ lists ∧ x ∈ l := by
  induction n generalizing lists result with
  | zero =>
    simp [c3MergeAux] at h
    obtain ⟨-, rfl⟩ := h
    intro x hx; exact absurd hx List.not_mem_nil
  | succ n ih =>
    unfold c3MergeAux at h
    split at h
    · simp at h; subst h; intro x hx; exact absurd hx List.not_mem_nil
    · cases hfgh : findGoodHead lists with
      | none => simp [hfgh] at h
      | some gh =>
        simp [hfgh] at h
        cases hrest : c3MergeAux n (removeFromHeads gh lists) with
        | none => simp [hrest] at h
        | some rest =>
          simp [hrest] at h; subst h
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hmem
          · -- x = gh, so gh was the head of some list
            exact findGoodHead_mem hfgh
          · -- x ∈ rest, use IH
            obtain ⟨l', hl', hxl'⟩ := ih hrest x hmem
            exact mem_of_mem_removeFromHeads hl' hxl'

/-- Soundness for `c3Merge`. -/
theorem c3Merge_sound
    {lists : List (List Identifier)} {result : List Identifier}
    (h : c3Merge lists = some result) :
    ∀ x, x ∈ result → ∃ l, l ∈ lists ∧ x ∈ l :=
  c3MergeAux_sound h

/-! ## List ordering -/

/-- Check if `x` appears before `y` in a list. -/
def appearsBefore (x y : Identifier) : List Identifier → Bool
  | [] => false
  | h :: t => if h = x then containsIdentifier y t else appearsBefore x y t

/-- If `x` appears before `y`, then `x` is in the list. -/
theorem appearsBefore_left_mem {x y : Identifier} {l : List Identifier}
    (h : appearsBefore x y l = true) : x ∈ l := by
  induction l with
  | nil => simp [appearsBefore] at h
  | cons _ _ ih =>
    simp only [appearsBefore] at h; split at h
    next heq => exact heq ▸ .head _
    next => exact .tail _ (ih h)

/-- If `x` appears before `y`, then `y` is in the list. -/
theorem appearsBefore_right_mem {x y : Identifier} {l : List Identifier}
    (h : appearsBefore x y l = true) : y ∈ l := by
  induction l with
  | nil => simp [appearsBefore] at h
  | cons _ _ ih =>
    simp only [appearsBefore] at h; split at h
    · exact .tail _ (mem_of_containsIdentifier_true h)
    · exact .tail _ (ih h)

/-! ## C3 merge order preservation -/

/-- Skipping a head that doesn't match `x` preserves `appearsBefore`. -/
theorem appearsBefore_cons_ne {x y hd : Identifier} {tl : List Identifier}
    (hne : hd ≠ x) :
    appearsBefore x y (hd :: tl) = appearsBefore x y tl := by
  simp [appearsBefore, hne]

/-- `findGoodHead` only picks elements not in any tail. -/
private theorem findGoodHead_not_inTailOfAny
    {lists : List (List Identifier)} {gh : Identifier}
    (hgh : findGoodHead lists = some gh) :
    inTailOfAny gh lists = false := by
  unfold findGoodHead at hgh
  rw [List.findSome?_eq_some_iff] at hgh
  obtain ⟨_, a, _, -, hsome, -⟩ := hgh
  cases a with
  | nil => simp at hsome
  | cons hd _ =>
    simp only at hsome; split at hsome
    · simp at hsome
    · next h =>
      simp only [Option.some.injEq] at hsome; rw [← hsome]
      exact Bool.eq_false_iff.mpr h

/-- If `inTailOfAny x` is false, `x` is not in the tail of any list. -/
private theorem not_in_tail_of_not_inTailOfAny
    {x : Identifier} {lists : List (List Identifier)}
    (h : inTailOfAny x lists = false)
    {hd : Identifier} {tl : List Identifier}
    (hl : (hd :: tl) ∈ lists) :
    x ∉ tl := by
  intro hmem
  have : inTailOfAny x lists = true :=
    List.any_eq_true.mpr ⟨hd :: tl, hl,
      containsIdentifier_true_of_mem hmem⟩
  simp [this] at h

/-- Order is preserved through `removeFromHeads` for elements other than the removed head. -/
private theorem appearsBefore_removeFromHeads
    {x y gh : Identifier} {lists : List (List Identifier)}
    {l : List Identifier} (hl : l ∈ lists)
    (hab : appearsBefore x y l = true) (hne : x ≠ gh) :
    ∃ l', l' ∈ removeFromHeads gh lists ∧ appearsBefore x y l' = true := by
  let f : List Identifier → List Identifier :=
    fun l => match l with | [] => [] | h :: rest => if h = gh then rest else h :: rest
  have hfl : f l ∈ removeFromHeads gh lists := by
    show f l ∈ lists.map f; exact List.mem_map_of_mem hl
  refine ⟨f l, hfl, ?_⟩
  cases l with
  | nil => simp [appearsBefore] at hab
  | cons hd tl =>
    show appearsBefore x y (if hd = gh then tl else hd :: tl) = true
    split
    · next hhd =>
        have hdx : hd ≠ x := by
          intro hEq
          exact hne (hEq.symm.trans hhd)
        rwa [appearsBefore_cons_ne hdx] at hab
    · exact hab

/-- C3 merge preserves the relative order of elements within each input list. -/
theorem c3MergeAux_order_preserving
    {n : Nat} {lists : List (List Identifier)} {result : List Identifier}
    (h : c3MergeAux n lists = some result) :
    ∀ l, l ∈ lists → ∀ x y, appearsBefore x y l = true → appearsBefore x y result = true := by
  induction n generalizing lists result with
  | zero =>
    simp [c3MergeAux] at h; obtain ⟨hempty, rfl⟩ := h
    intro l hl; rw [hempty l hl]; intro _ _ h; simp [appearsBefore] at h
  | succ n ih =>
    unfold c3MergeAux at h; split at h
    · simp at h; subst h
      intro l hl; rw [List.all_eq_true.mp ‹_› l hl |> List.isEmpty_iff.mp]
      intro _ _ h; simp [appearsBefore] at h
    · cases hfgh : findGoodHead lists with
      | none => simp [hfgh] at h
      | some gh =>
        simp [hfgh] at h
        cases hrest : c3MergeAux n (removeFromHeads gh lists) with
        | none => simp [hrest] at h
        | some rest =>
          simp [hrest] at h; subst h
          have hgood := findGoodHead_not_inTailOfAny hfgh
          intro l hl x y hab
          by_cases hxgh : x = gh
          · have hab' : appearsBefore gh y l = true := by
              simpa [hxgh] using hab
            have hy_ne : y ≠ gh := by
              intro hy_eq
              have hab'' : appearsBefore gh gh l = true := by
                simpa [hy_eq] using hab'
              cases l with
              | nil => simp [appearsBefore] at hab''
              | cons hd tl =>
                have hnt : gh ∉ tl := not_in_tail_of_not_inTailOfAny hgood hl
                by_cases hhd : hd = gh
                · have htail : gh ∈ tl := by
                    subst hd
                    exact mem_of_containsIdentifier_true (by simpa [appearsBefore] using hab'')
                  exact absurd htail hnt
                · have hleft : gh ∈ hd :: tl := appearsBefore_left_mem hab''
                  rcases List.mem_cons.mp hleft with hhead | hmem
                  · exact absurd hhead.symm hhd
                  · exact absurd hmem hnt
            obtain ⟨l', hl', hyl'⟩ := mem_removeFromHeads_of_mem hl (appearsBefore_right_mem hab') hy_ne
            unfold appearsBefore
            rw [if_pos hxgh.symm]
            exact containsIdentifier_true_of_mem (c3MergeAux_complete hrest l' hl' y hyl')
          · rw [appearsBefore_cons_ne (fun h => hxgh h.symm)]
            obtain ⟨l', hl', hab'⟩ := appearsBefore_removeFromHeads hl hab hxgh
            exact ih hrest l' hl' x y hab'

/-- C3 merge preserves the relative order of elements within each input list. -/
theorem c3Merge_order_preserving
    {lists : List (List Identifier)} {result : List Identifier}
    (h : c3Merge lists = some result) :
    ∀ l, l ∈ lists → ∀ x y, appearsBefore x y l = true → appearsBefore x y result = true :=
  c3MergeAux_order_preserving h
