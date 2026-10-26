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
  (lists.map List.length).sum

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

/-- Each input list is retained in the output, in its original order. -/
private theorem c3MergeAux_sublist {fuel : Nat} {lists : List (List Identifier)} {result : List Identifier}
    (merged : c3MergeAux fuel lists = some result) :
    ∀ input, input ∈ lists → input.Sublist result := by
  induction fuel generalizing lists result with
  | zero =>
    simp [c3MergeAux] at merged
    obtain ⟨empty, rfl⟩ := merged
    intro input member
    rw [empty input member]
    exact .slnil
  | succ fuel ih =>
    unfold c3MergeAux at merged
    split at merged
    · simp at merged; subst merged
      intro input member
      rw [List.isEmpty_iff.mp (List.all_eq_true.mp ‹_› input member)]
      exact .slnil
    · cases chosen : findGoodHead lists with
      | none => simp [chosen] at merged
      | some head =>
        cases restMerged : c3MergeAux fuel (removeFromHeads head lists) with
        | none => simp [chosen, restMerged] at merged
        | some rest =>
          simp [chosen, restMerged] at merged; subst merged
          intro input member
          let remove : List Identifier → List Identifier := fun list => match list with
            | [] => []
            | first :: tail => if first = head then tail else first :: tail
          have residual : remove input ∈ removeFromHeads head lists :=
            List.mem_map.mpr ⟨input, member, rfl⟩
          cases input with
          | nil => exact List.nil_sublist _
          | cons first tail =>
            by_cases same : first = head
            · subst first
              exact .cons₂ head (ih restMerged tail (by simpa [remove, removeFromHeads] using residual))
            · exact .cons head (ih restMerged (first :: tail)
                (by simpa [remove, removeFromHeads, same] using residual))

/-- A successful C3 merge contains every input list in its original order. -/
theorem c3Merge_sublist {lists : List (List Identifier)} {result : List Identifier}
    (merged : c3Merge lists = some result) :
    ∀ input, input ∈ lists → input.Sublist result := c3MergeAux_sublist merged

/-- Completeness for `c3Merge`. -/
theorem c3Merge_complete
    {lists : List (List Identifier)} {result : List Identifier}
    (h : c3Merge lists = some result) :
    ∀ l, l ∈ lists → ∀ x, x ∈ l → x ∈ result :=
  fun input member _ occurs => (c3Merge_sublist h input member).subset occurs

/-- A selected name is an input's head and occurs in no input tail. -/
theorem findGoodHead_spec {lists : List (List Identifier)} {head : Identifier}
    (chosen : findGoodHead lists = some head) :
    (∃ tail, head :: tail ∈ lists) ∧ (∀ input, input ∈ lists → head ∉ input.tail) := by
  unfold findGoodHead at chosen
  rw [List.findSome?_eq_some_iff] at chosen
  obtain ⟨_, input, _, equal, found, _⟩ := chosen
  cases input with
  | nil => simp at found
  | cons first tail =>
    simp only at found
    split at found
    · simp at found
    · next absent =>
      simp only [Option.some.injEq] at found
      subst head
      refine ⟨⟨tail, by rw [equal]; exact List.mem_append_right _ (List.mem_cons_self ..)⟩, ?_⟩
      intro input member present
      cases input with
      | nil => cases present
      | cons other rest =>
        have yes : inTailOfAny first lists = true :=
          List.any_eq_true.mpr ⟨other :: rest, member, containsIdentifier_true_of_mem present⟩
        exact absent yes

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
          · -- The selected head came from an input.
            obtain ⟨tail, member⟩ := (findGoodHead_spec hfgh).1
            exact ⟨x :: tail, member, .head _⟩
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

/-- Retaining a list in a larger list preserves the order of its named members. -/
theorem appearsBefore_sublist {source target : List Identifier} {x y : Identifier}
    (included : source.Sublist target) (ordered : appearsBefore x y source = true) :
    appearsBefore x y target = true := by
  induction included with
  | slnil => simp [appearsBefore] at ordered
  | cons first included ih =>
    by_cases same : first = x
    · simp only [appearsBefore, same, ite_true]
      exact containsIdentifier_true_of_mem (included.subset (appearsBefore_right_mem ordered))
    · simpa [appearsBefore, same] using ih ordered
  | cons₂ first included ih =>
    by_cases same : first = x
    · have present : y ∈ _ := mem_of_containsIdentifier_true (by simpa [appearsBefore, same] using ordered)
      simp only [appearsBefore, same, ite_true]
      exact containsIdentifier_true_of_mem (included.subset present)
    · simp only [appearsBefore, same, ite_false] at ordered ⊢
      exact ih ordered

/-- C3 merge preserves the relative order of elements within each input list. -/
theorem c3Merge_order_preserving
    {lists : List (List Identifier)} {result : List Identifier}
    (h : c3Merge lists = some result) :
    ∀ l, l ∈ lists → ∀ x y, appearsBefore x y l = true → appearsBefore x y result = true :=
  fun input member _ _ ordered => appearsBefore_sublist (c3Merge_sublist h input member) ordered

/-! ## Existence of a common order

A common order is a list without repeated names that contains every input
list as a sublist. C3 merge computes a common order when one exists; the theorems below prove
this and show that a successful result contains every input list in order.
In subtyping, `hasValidClassOrder` runs the merge to check whether the listed
class MROs share a common order. -/

/-- A successful merge repeats no selected name. -/
private theorem c3MergeAux_nodup {fuel : Nat} {lists : List (List Identifier)} {result : List Identifier}
    (merged : c3MergeAux fuel lists = some result) : result.Nodup := by
  induction fuel generalizing lists result with
  | zero =>
    simp [c3MergeAux] at merged
    obtain ⟨_, rfl⟩ := merged
    exact List.nodup_nil
  | succ fuel ih =>
    unfold c3MergeAux at merged
    split at merged
    · simp at merged; subst merged; exact List.nodup_nil
    · cases chosen : findGoodHead lists with
      | none => simp [chosen] at merged
      | some head =>
        cases restMerged : c3MergeAux fuel (removeFromHeads head lists) with
        | none => simp [chosen, restMerged] at merged
        | some rest =>
          simp [chosen, restMerged] at merged; subst merged
          refine List.nodup_cons.mpr ⟨?_, ih restMerged⟩
          intro occurs
          obtain ⟨residual, member, occurs⟩ := c3MergeAux_sound restMerged head occurs
          obtain ⟨input, inputMember, equal⟩ := List.mem_map.mp member
          have good := (findGoodHead_spec chosen).2
          cases input with
          | nil => simp at equal; subst residual; cases occurs
          | cons first tail =>
            have absent : head ∉ tail := good (first :: tail) inputMember
            by_cases same : first = head
            · simp [same] at equal
              subst residual
              exact absent occurs
            · simp [same] at equal
              subst residual
              exact (List.mem_cons.mp occurs).elim (fun eq => same eq.symm) absent

/-- The first name in a distinct common order cannot occur in an input tail. -/
private theorem head_absent_tail {head : Identifier} {tail input : List Identifier}
    (distinct : (head :: tail).Nodup) (sublist : input.Sublist (head :: tail)) :
    head ∉ input.tail := by
  cases input with
  | nil => simp
  | cons first rest =>
    intro member
    exact (List.nodup_cons.mp distinct).1
      (sublist.of_cons_cons.subset member)

/-- A nonempty family with a distinct common order has a valid C3 head. -/
private theorem good_exists (order : List Identifier) (distinct : order.Nodup)
    (lists : List (List Identifier))
    (inputs : ∀ input, input ∈ lists → input.Sublist order)
    (nonempty : lists.all List.isEmpty ≠ true) : findGoodHead lists ≠ none := by
  induction order generalizing lists with
  | nil =>
    intro _
    apply nonempty
    apply List.all_eq_true.mpr
    intro input member
    have := inputs input member
    have empty : input = [] := List.sublist_nil.mp this
    simp [empty]
  | cons head tail ih =>
    by_cases occurs : ∃ input, input ∈ lists ∧ head ∈ input
    · obtain ⟨input, member, occurs⟩ := occurs
      have starts : ∃ rest, input = head :: rest := by
        have sub := inputs input member
        cases sub with
        | cons _ sub => exact ((List.nodup_cons.mp distinct).1 (sub.subset occurs)).elim
        | cons₂ _ sub => exact ⟨_, rfl⟩
      obtain ⟨rest, rfl⟩ := starts
      have good : inTailOfAny head lists = false := by
        apply Bool.eq_false_iff.mpr
        intro yes
        obtain ⟨other, otherMember, occurs⟩ := List.any_eq_true.mp yes
        cases other with
        | nil => simp at occurs
        | cons first rest =>
          exact head_absent_tail distinct (inputs _ otherMember)
            (mem_of_containsIdentifier_true occurs)
      intro noHead
      have allNone := List.findSome?_eq_none_iff.mp noHead
      have rejected := allNone (head :: rest) member
      simp [good] at rejected
    · apply ih (List.nodup_cons.mp distinct).2 lists ?_ nonempty
      intro input member
      have sub := inputs input member
      cases sub with
      | cons _ sub => exact sub
      | cons₂ _ sub => exact (occurs ⟨_, member, .head _⟩).elim

/-- The total input length is the first list length plus the remaining lengths. -/
private theorem totalLength_cons (input : List Identifier) (lists : List (List Identifier)) :
    totalLength (input :: lists) = input.length + totalLength lists := rfl

/-- Head removal processes the first input and the remaining inputs independently. -/
private theorem removal_cons (head : Identifier) (input : List Identifier)
    (rest : List (List Identifier)) :
    removeFromHeads head (input :: rest) =
      (match input with | [] => [] | first :: tail => if first = head then tail else first :: tail)
        :: removeFromHeads head rest := rfl

/-- Head removal cannot increase the total input length. -/
private theorem removal_le (head : Identifier) (lists : List (List Identifier)) :
    totalLength (removeFromHeads head lists) ≤ totalLength lists := by
  induction lists with
  | nil => simp [removeFromHeads, totalLength]
  | cons input rest ih =>
    rw [removal_cons, totalLength_cons, totalLength_cons]
    cases input with
    | nil => simpa using ih
    | cons first tail =>
      by_cases same : first = head <;> simp only [same, ite_true, ite_false, List.length_cons] <;> omega

/-- Removing a head that occurs in an input strictly decreases the total length. -/
private theorem removal_lt (head : Identifier) (lists : List (List Identifier))
    (occurs : ∃ tail, head :: tail ∈ lists) :
    totalLength (removeFromHeads head lists) < totalLength lists := by
  induction lists with
  | nil => obtain ⟨_, impossible⟩ := occurs; cases impossible
  | cons input rest ih =>
    obtain ⟨tail, member⟩ := occurs
    rcases List.mem_cons.mp member with eq | member
    · subst input
      have le := removal_le head rest
      rw [removal_cons, totalLength_cons, totalLength_cons]
      simp only [ite_true, List.length_cons]
      omega
    · have lt := ih ⟨tail, member⟩
      rw [removal_cons, totalLength_cons, totalLength_cons]
      cases input with
      | nil => simpa using lt
      | cons first tail =>
        by_cases same : first = head <;> simp only [same, ite_true, ite_false, List.length_cons] <;> omega

/-- Removing a valid C3 head preserves a common order for the residual inputs. -/
private theorem residual_common (order : List Identifier)
    (lists : List (List Identifier))
    (inputs : ∀ input, input ∈ lists → input.Sublist order)
    (head : Identifier) (good : ∀ input, input ∈ lists → head ∉ input.tail) :
    ∀ input, input ∈ removeFromHeads head lists →
      input.Sublist (order.filter (fun name => name != head)) := by
  intro residual member
  obtain ⟨input, inputMember, rfl⟩ := List.mem_map.mp member
  have sub := (inputs input inputMember).filter (fun name => name != head)
  cases input with
  | nil => exact List.nil_sublist _
  | cons first tail =>
    have absent : head ∉ tail := good (first :: tail) inputMember
    have filtered : tail.filter (fun name => name != head) = tail := by
      apply List.filter_eq_self.mpr
      intro name member
      have different : name ≠ head := fun eq => absent (eq ▸ member)
      simpa using different
    by_cases same : first = head
    · simpa [same, filtered] using sub
    · simpa [same, filtered] using sub

/-- Sufficient fuel makes C3 succeed when a distinct common order contains all inputs. -/
private theorem c3MergeAux_of_common (fuel : Nat) (lists : List (List Identifier))
    (enough : totalLength lists ≤ fuel) (order : List Identifier) (distinct : order.Nodup)
    (inputs : ∀ input, input ∈ lists → input.Sublist order) :
    (c3MergeAux fuel lists).isSome = true := by
  induction fuel generalizing lists order with
  | zero =>
    have empty : lists.all List.isEmpty = true := by
      apply List.all_eq_true.mpr
      intro input member
      have zero : totalLength lists = 0 := by omega
      have allEmpty : ∀ list, totalLength list = 0 → ∀ input, input ∈ list → input = [] := by
        intro list
        induction list with
        | nil => intro _ _ impossible; cases impossible
        | cons first rest ih =>
          intro lengthZero input member
          rw [totalLength_cons] at lengthZero
          rcases List.mem_cons.mp member with rfl | member
          · exact List.eq_nil_of_length_eq_zero (by omega)
          · exact ih (by omega) input member
      have := allEmpty lists zero input member
      simp [this]
    simp [c3MergeAux, empty]
  | succ fuel ih =>
    by_cases empty : lists.all List.isEmpty = true
    · simp [c3MergeAux, empty]
    · have existsHead := good_exists order distinct lists inputs empty
      cases chosen : findGoodHead lists with
      | none => exact (existsHead chosen).elim
      | some head =>
        obtain ⟨occurs, good⟩ := findGoodHead_spec chosen
        have lt := removal_lt head lists occurs
        have distinctRest := distinct.sublist (List.filter_sublist (p := fun name => name != head))
        have recursive := ih (removeFromHeads head lists) (by omega)
          (order.filter (fun name => name != head)) distinctRest
          (residual_common order lists inputs head good)
        cases restMerged : c3MergeAux fuel (removeFromHeads head lists) with
        | none => simp [restMerged] at recursive
        | some rest => simp [c3MergeAux, empty, chosen, restMerged]

/-- Successful C3 merges contain no repeated class names. -/
theorem c3Merge_nodup {lists : List (List Identifier)} {result : List Identifier}
    (merged : c3Merge lists = some result) : result.Nodup := c3MergeAux_nodup merged

/-- C3 succeeds when one distinct-name order preserves every input list. -/
theorem c3Merge_of_common_order {lists : List (List Identifier)}
    (order : List Identifier) (distinct : order.Nodup)
    (inputs : ∀ input, input ∈ lists → input.Sublist order) :
    (c3Merge lists).isSome = true :=
  c3MergeAux_of_common (totalLength lists) lists (Nat.le_refl _) order distinct inputs

/-- If one input is a distinct order containing every other input as a sublist,
C3 returns that exact order. -/
theorem c3Merge_of_full_order {lists : List (List Identifier)}
    (order : List Identifier) (distinct : order.Nodup)
    (inputs : ∀ input, input ∈ lists → input.Sublist order)
    (full : order ∈ lists) : c3Merge lists = some order := by
  have success := c3Merge_of_common_order order distinct inputs
  cases merged : c3Merge lists with
  | none => simp [merged] at success
  | some result =>
      have containsOrder := c3Merge_sublist merged order full
      have equal : order = result := by
        have resultDistinct := c3Merge_nodup merged
        have members (value : Identifier) (present : value ∈ result) : value ∈ order := by
          obtain ⟨input, member, present⟩ := c3Merge_sound merged value present
          exact (inputs input member).subset present
        -- A distinct list has no extra entries if every name is already in its sublist.
        clear distinct inputs full merged success
        induction containsOrder with
        | slnil => rfl
        | cons head included =>
            have present := members head (List.mem_cons_self ..)
            exact False.elim ((List.nodup_cons.mp resultDistinct).1 (included.subset present))
        | cons₂ head _ ih =>
            congr 1
            apply ih (List.nodup_cons.mp resultDistinct).2
            intro value present
            rcases List.mem_cons.mp (members value (List.mem_cons_of_mem head present)) with equal | member
            · subst value
              exact False.elim ((List.nodup_cons.mp resultDistinct).1 present)
            · exact member
      exact congrArg some equal.symm
