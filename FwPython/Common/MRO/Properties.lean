import FwPython.Common.MRO.Core

/-! # MRO membership, inherited order, and method-lookup propagation

These properties apply to any method payload. -/

/-- Object is always a member of every MRO. -/
theorem mro_contains_object {Method : Type}
    {ct : ClassTableDecl Method} {c : ClassDecl Method} {mro : List Identifier}
    (hmro : ComputeMro (Method := Method) ct c mro) : objectClass ∈ mro := by
  exact ComputeMro.rec
    (motive_1 := fun _ _ parentMros _ => ∀ m, m ∈ parentMros → objectClass ∈ m)
    (motive_2 := fun _ _ mro _ => objectClass ∈ mro)
    (fun _ hm => absurd hm List.not_mem_nil)
    (fun _ _ _ ih_mro ih_rest m hmem => by
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact ih_mro
      · exact ih_rest m hmem')
    (fun hnil => by
      have ⟨_, hname⟩ := (resolvedBases_nil_iff _).mp hnil
      simp [hname])
    (fun {bases} {_} {parentMros} {_} {_}
         _ hne hall hmerge ih_parents => by
      apply List.mem_cons_of_mem
      have hpm_ne : parentMros ≠ [] := by
        have := allParentMros_length hall
        intro h; rw [h] at this; simp at this; exact hne this
      obtain ⟨pm, _, rfl⟩ := List.exists_cons_of_ne_nil hpm_ne
      exact c3Merge_complete hmerge pm (List.mem_append_left _ (List.Mem.head _)) _
        (ih_parents pm (List.Mem.head _)))
    hmro

/-- An ancestor's complete MRO occurs in the child's MRO in the same order. -/
theorem mro_sublist {Method : Type}
    (ct : ClassTableDecl Method) (c a : ClassDecl Method)
    (mro_c mro_a : List Identifier)
    (hfc : findClass ct c.name = some c)
    (hmc : ComputeMro ct c mro_c)
    (hfa : findClass ct a.name = some a)
    (hma : ComputeMro ct a mro_a)
    (ha : a.name ∈ mro_c) : mro_a.Sublist mro_c := by
  have key := ComputeMro.rec
    (motive_1 := fun ct _ parentMros _ =>
      ∀ pm, pm ∈ parentMros →
      ∀ (a : ClassDecl Method) (mro_a : List Identifier),
        findClass ct a.name = some a → ComputeMro ct a mro_a →
        a.name ∈ pm → mro_a.Sublist pm)
    (motive_2 := fun ct c mro _ =>
      ∀ (a : ClassDecl Method) (mro_a : List Identifier),
        findClass ct c.name = some c →
        findClass ct a.name = some a → ComputeMro ct a mro_a →
        a.name ∈ mro → mro_a.Sublist mro)
    (fun _ hm => absurd hm List.not_mem_nil)
    (fun {_} {_} {_} {_} {_} {_}
         hfind _ _ ih_mro ih_rest pm hmem a' mro_a' hfa' hma' ha'mem => by
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact ih_mro a' mro_a' (findClass_self hfind) hfa' hma' ha'mem
      · exact ih_rest pm hmem' a' mro_a' hfa' hma' ha'mem)
    (fun {_} {_} hnil a' mro_a' hfc' hfa' hma' ha'mem => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha'mem
      rw [ha'mem] at hfa'
      rw [hfc'] at hfa'; cases hfa'
      have := determinism hma' (ComputeMro.root hnil)
      rw [this]
      exact .refl _)
    (fun {_} {_} {_} {_} {_}
         hbases hne hall hmerge ih_parents a' mro_a' hfc' hfa' hma' ha'mem => by
      simp only [List.mem_cons] at ha'mem
      cases ha'mem with
      | inl ha'eq =>
        rw [ha'eq] at hfa'
        rw [hfc'] at hfa'; cases hfa'
        rw [determinism hma' (ComputeMro.step hbases hne hall hmerge)]
        exact .refl _
      | inr ha'in_merged =>
        obtain ⟨l, hl, ha'l⟩ := c3Merge_sound hmerge a'.name ha'in_merged
        rcases List.mem_append.mp hl with hl_pm | hl_bases
        · exact .cons _ ((ih_parents l hl_pm a' mro_a' hfa' hma' ha'l).trans
            (c3Merge_sublist hmerge l (List.mem_append_left _ hl_pm)))
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl_bases
          subst hl_bases
          obtain ⟨a'cls, a'pmro, hfa'cls, hmro_a'cls, ha'pmro_mem⟩ :=
            allParentMros_mem hall ha'l
          rw [hfa'] at hfa'cls; cases hfa'cls
          rw [← determinism hmro_a'cls hma']
          exact .cons _ (c3Merge_sublist hmerge a'pmro (List.mem_append_left _ ha'pmro_mem)))
    hmc
  exact key a mro_a hfc hfa hma ha

/-- Transitivity of MRO membership: if `a.name` appears in the MRO of `c`,
    and `b` appears in the MRO of `a`, then `b` appears in the MRO of `c`. -/
theorem mro_mem_trans {Method : Type}
    (ct : ClassTableDecl Method) (c a : ClassDecl Method)
    (mro_c mro_a : List Identifier) (b : Identifier)
    (hfc : findClass ct c.name = some c)
    (hmc : ComputeMro ct c mro_c)
    (hfa : findClass ct a.name = some a)
    (hma : ComputeMro ct a mro_a)
    (ha : a.name ∈ mro_c)
    (hb : b ∈ mro_a) :
    b ∈ mro_c :=
  (mro_sublist ct c a mro_c mro_a hfc hmc hfa hma ha).subset hb

/-- A selected class's MRO contains each class name at most once. -/
theorem mro_nodup {Method : Type} {ct : ClassTableDecl Method}
    {c : ClassDecl Method} {mro : List Identifier}
    (selected : findClass ct c.name = some c)
    (computed : ComputeMro ct c mro) : mro.Nodup := by
  cases computed with
  | root => simp
  | step bases nonempty parents merged =>
    refine List.nodup_cons.mpr ⟨?_, c3Merge_nodup merged⟩
    intro repeated
    obtain ⟨input, inputMember, occurs⟩ := c3Merge_sound merged c.name repeated
    rcases List.mem_append.mp inputMember with parentMember | baseMember
    · have parentSelected := AllParentMros.rec
        (motive_1 := fun table _ mros _ => ∀ input, input ∈ mros →
          ∃ declaration, findClass table declaration.name = some declaration ∧
            ComputeMro table declaration input)
        (motive_2 := fun _ _ _ _ => True)
        (fun _ impossible => absurd impossible List.not_mem_nil)
        (fun lookup computed _ _ ih input member => by
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨_, findClass_self lookup, computed⟩
          · exact ih input member)
        (fun _ => trivial) (fun _ _ _ _ _ => trivial) parents
      obtain ⟨parent, parentLookup, parentComputed⟩ := parentSelected input parentMember
      have sub := (mro_sublist ct parent c input _ parentLookup parentComputed selected
          (.step bases nonempty parents merged) occurs).trans
        (c3Merge_sublist merged input (List.mem_append_left _ parentMember))
      have := sub.length_le
      simp only [List.length_cons] at this
      omega
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at baseMember
      subst input
      obtain ⟨actual, parentMro, actualLookup, parentComputed, parentMember⟩ := allParentMros_mem parents occurs
      rw [selected] at actualLookup
      cases actualLookup
      have same := determinism (.step bases nonempty parents merged) parentComputed
      have sub := c3Merge_sublist merged parentMro (List.mem_append_left _ parentMember)
      rw [← same] at sub
      have := sub.length_le
      simp only [List.length_cons] at this
      omega

/-- Every member of an MRO corresponds to a class with a valid MRO,
    given that all classes in the table have valid MROs. -/
theorem mro_member_wellFormedClass {Method : Type}
    {ct : ClassTableDecl Method} {c : ClassDecl Method}
    {mro : List Identifier} {a : Identifier}
    (hall : ∀ cname c, findClass ct cname = some c → ∃ mro, ComputeMro ct c mro)
    (hfc : findClass ct c.name = some c)
    (hmro : ComputeMro ct c mro)
    (hmem : a ∈ mro) :
    ∃ acls amro, findClass ct a = some acls ∧ ComputeMro ct acls amro := by
  have key := ComputeMro.rec
    (motive_1 := fun ct _ parentMros _ =>
      (∀ cname c, findClass ct cname = some c → ∃ mro, ComputeMro ct c mro) →
      ∀ pm, pm ∈ parentMros → ∀ a, a ∈ pm →
        ∃ acls amro, findClass ct a = some acls ∧ ComputeMro ct acls amro)
    (motive_2 := fun ct c mro _ =>
      (∀ cname c, findClass ct cname = some c → ∃ mro, ComputeMro ct c mro) →
      findClass ct c.name = some c →
      ∀ a, a ∈ mro →
        ∃ acls amro, findClass ct a = some acls ∧ ComputeMro ct acls amro)
    (fun _ _ hm => absurd hm List.not_mem_nil)
    (fun {_} {_} {_} {_} {_} {_}
         hfind _ _ ih_mro ih_rest hall' pm hmem a' ha'mem => by
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact ih_mro hall' (findClass_self hfind) a' ha'mem
      · exact ih_rest hall' pm hmem' a' ha'mem)
    (fun {_} {c'} _ hall' hfc' a' ha' => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha'
      rw [ha']
      obtain ⟨amro, hamro⟩ := hall' c'.name c' hfc'
      exact ⟨c', amro, hfc', hamro⟩)
    (fun {_} {_} {_} {_} {c'}
         _ _ hallp hmerge ih_parents hall' hfc' a' ha' => by
      rcases List.mem_cons.mp ha' with rfl | ha'merged
      · obtain ⟨amro, hamro⟩ := hall' c'.name c' hfc'
        exact ⟨c', amro, hfc', hamro⟩
      · obtain ⟨l, hl, ha'l⟩ := c3Merge_sound hmerge a' ha'merged
        rcases List.mem_append.mp hl with hl_pm | hl_bases
        · exact ih_parents hall' l hl_pm a' ha'l
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl_bases
          subst hl_bases
          obtain ⟨a'cls, _, hfa'cls, _, _⟩ := allParentMros_mem hallp ha'l
          obtain ⟨amro, hamro⟩ := hall' a' a'cls hfa'cls
          exact ⟨a'cls, amro, hfa'cls, hamro⟩)
    hmro
  exact key hall hfc a hmem

/-! ## Method lookup propagation -/

private theorem findMethodInMro_cons_of_rest {Ty : Type} {Expr : Type}
    {ct : ClassTableDecl (MethodDecl Ty Expr)}
    {rest : List Identifier} {cname mname : Identifier}
    {m : MethodDecl Ty Expr}
    (h : findMethodInMro ct rest mname = some m) :
    ∃ m', findMethodInMro ct (cname :: rest) mname = some m' := by
  simp only [findMethodInMro, findMemberInHierarchy]; split
  · exact ⟨m, h⟩
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨m, h⟩

/-- If a method exists in an ancestor's MRO, it exists (possibly overridden)
    in any descendant's MRO that includes the ancestor. -/
theorem findMethodInMro_of_ancestor {Ty : Type} {Expr : Type}
    {ct : ClassTableDecl (MethodDecl Ty Expr)}
    {cls : ClassDecl (MethodDecl Ty Expr)} {mro : List Identifier}
    (hmro : ComputeMro ct cls mro)
    (hfc : findClass ct cls.name = some cls)
    {aname : Identifier} (hmem : aname ∈ mro)
    {acls : ClassDecl (MethodDecl Ty Expr)} {amro : List Identifier}
    (hfa : findClass ct aname = some acls)
    (hmroa : ComputeMro ct acls amro)
    {mname : Identifier} {m : MethodDecl Ty Expr}
    (hmethod : findMethodInMro ct amro mname = some m) :
    ∃ m', findMethodInMro ct mro mname = some m' := by
  obtain ⟨dname, d, hd_in_amro, hfd, hm_in_d⟩ := findMethodInMro_provenance hmethod
  have hd_in_mro : dname ∈ mro := by
    have hacls_name := findClass_name hfa
    rw [← hacls_name] at hmem
    exact mro_mem_trans ct cls acls mro amro dname hfc hmro
      (findClass_self hfa) hmroa hmem hd_in_amro
  suffices ∀ mro', dname ∈ mro' → findClass ct dname = some d →
    (∃ m'', m'' ∈ d.methods ∧ m''.name = mname) →
    ∃ m', findMethodInMro ct mro' mname = some m' by
    exact this mro hd_in_mro hfd ⟨m, hm_in_d, findMethodInMro_name hmethod⟩
  intro mro' hd_in hmro'_fd hm_exists
  induction mro' with
  | nil => exact absurd hd_in List.not_mem_nil
  | cons cname rest ih =>
    simp only [findMethodInMro, findMemberInHierarchy]
    split
    · next hfc_none =>
      rcases List.mem_cons.mp hd_in with rfl | hrest
      · simp [hmro'_fd] at hfc_none
      · exact ih hrest
    · next hfc' =>
      split
      · exact ⟨_, rfl⟩
      · next hmethod_none =>
        rcases List.mem_cons.mp hd_in with rfl | hrest
        · rw [hfc'] at hmro'_fd; cases hmro'_fd
          obtain ⟨m'', hm''_in, hm''_name⟩ := hm_exists
          have hnone : m''.name ≠ mname :=
            (findByName_eq_none_iff.mp (by
              simpa [findMethodInList] using hmethod_none)) m'' hm''_in
          exact False.elim <| hnone hm''_name
        · exact ih hrest

/-- Successful MRO lookup decomposes the MRO at the first defining class. -/
theorem findMethodInMro_first_definer {Ty : Type} {Expr : Type}
    {ct : ClassTableDecl (MethodDecl Ty Expr)}
    {mro : List Identifier} {methodName : Identifier} {m : MethodDecl Ty Expr}
    (h : findMethodInMro ct mro methodName = some m) :
    ∃ pre definerName suf d,
      mro = pre ++ definerName :: suf ∧
        findClass ct definerName = some d ∧
        findMethodInList d.methods methodName = some m ∧
        (∀ cname ∈ pre, ∀ c, findClass ct cname = some c →
          findMethodInList c.methods methodName = none) := by
  induction mro with
  | nil => simp [findMethodInMro, findMemberInHierarchy] at h
  | cons cname rest ih =>
    cases hfind : findClass ct cname with
    | none =>
        obtain ⟨pre, definerName, suf, d, hmro, hdef, hmethod, hprefix⟩ :=
          ih (by simpa [findMethodInMro, findMemberInHierarchy, hfind] using h)
        refine ⟨cname :: pre, definerName, suf, d, by simp [hmro], hdef, hmethod, ?_⟩
        intro cname' hmem c hclass
        cases hmem with
        | head => rw [hfind] at hclass; cases hclass
        | tail _ hmem => exact hprefix cname' hmem c hclass
    | some c =>
        cases hmethod : findMethodInList c.methods methodName with
        | none =>
            obtain ⟨pre, definerName, suf, d, hmro, hdef, hmethod', hprefix⟩ :=
              ih (by
                simpa [findMethodInMro, findMemberInHierarchy, hfind, hmethod]
                  using h)
            refine ⟨cname :: pre, definerName, suf, d, by simp [hmro], hdef, hmethod', ?_⟩
            intro cname' hmem c' hclass
            cases hmem with
            | head => rw [hfind] at hclass; cases hclass; exact hmethod
            | tail _ hmem => exact hprefix cname' hmem c' hclass
        | some m' =>
            have hm' : m' = m := by
              simpa [findMethodInMro, findMemberInHierarchy, hfind, hmethod]
                using h
            subst hm'
            exact ⟨[], cname, rest, c, rfl, hfind, hmethod, nofun⟩

private theorem definer_mem_prefix_of_shorter
    {α : Type} {prefix₁ prefix₂ suffix₁ suffix₂ : List α} {definer₁ definer₂ : α}
    (h : prefix₁ ++ definer₁ :: suffix₁ = prefix₂ ++ definer₂ :: suffix₂)
    (hlen : prefix₂.length < prefix₁.length) :
    definer₂ ∈ prefix₁ := by
  induction prefix₁ generalizing prefix₂ with
  | nil => cases hlen
  | cons a prefix₁ ih =>
      cases prefix₂ with
      | nil =>
          have hhead : a = definer₂ := (List.cons.inj h).1
          simp [hhead]
      | cons _ prefix₂ =>
          have hrest : prefix₁ ++ definer₁ :: suffix₁ = prefix₂ ++ definer₂ :: suffix₂ :=
            (List.cons.inj h).2
          have hlen' : prefix₂.length < prefix₁.length := by
            exact Nat.succ_lt_succ_iff.mp hlen
          exact .tail _ (ih hrest hlen')

private theorem definer_eq_of_same_length
    {α : Type} {prefix₁ prefix₂ suffix₁ suffix₂ : List α} {definer₁ definer₂ : α}
    (h : prefix₁ ++ definer₁ :: suffix₁ = prefix₂ ++ definer₂ :: suffix₂)
    (hlen : prefix₁.length = prefix₂.length) :
    definer₁ = definer₂ := by
  induction prefix₁ generalizing prefix₂ with
  | nil =>
      cases prefix₂ with
      | nil => exact (List.cons.inj h).1
      | cons _ _ => cases hlen
  | cons _ prefix₁ ih =>
      cases prefix₂ with
      | nil => cases hlen
      | cons _ prefix₂ =>
          have hrest : prefix₁ ++ definer₁ :: suffix₁ = prefix₂ ++ definer₂ :: suffix₂ :=
            (List.cons.inj h).2
          have hlen' : prefix₁.length = prefix₂.length := by
            exact Nat.succ.inj hlen
          exact ih hrest hlen'

/-- The first defining class in an MRO decomposition is unique. -/
theorem findMethodInMro_first_definer_unique {Ty : Type} {Expr : Type}
    {ct : ClassTableDecl (MethodDecl Ty Expr)}
    {mro : List Identifier}
    {prefix₁ prefix₂ suffix₁ suffix₂ : List Identifier}
    {definer₁ definer₂ methodName : Identifier}
    {d₁ d₂ : ClassDecl (MethodDecl Ty Expr)} {m₁ m₂ : MethodDecl Ty Expr}
    (h₁ : mro = prefix₁ ++ definer₁ :: suffix₁)
    (hprefix₁ : ∀ cname ∈ prefix₁, ∀ c, findClass ct cname = some c →
      findMethodInList c.methods methodName = none)
    (hfind₁ : findClass ct definer₁ = some d₁)
    (hmethod₁ : findMethodInList d₁.methods methodName = some m₁)
    (h₂ : mro = prefix₂ ++ definer₂ :: suffix₂)
    (hprefix₂ : ∀ cname ∈ prefix₂, ∀ c, findClass ct cname = some c →
      findMethodInList c.methods methodName = none)
    (hfind₂ : findClass ct definer₂ = some d₂)
    (hmethod₂ : findMethodInList d₂.methods methodName = some m₂) :
    definer₁ = definer₂ := by
  have heq : prefix₁ ++ definer₁ :: suffix₁ = prefix₂ ++ definer₂ :: suffix₂ :=
    h₁.symm.trans h₂
  have hlen : prefix₁.length = prefix₂.length := by
    by_cases hEq : prefix₁.length = prefix₂.length
    · exact hEq
    · rcases (by omega : prefix₁.length < prefix₂.length ∨ prefix₂.length < prefix₁.length)
        with hlt | hgt
      · have hmem : definer₁ ∈ prefix₂ :=
          definer_mem_prefix_of_shorter heq.symm hlt
        have hnone := hprefix₂ definer₁ hmem d₁ hfind₁
        rw [hmethod₁] at hnone; cases hnone
      · have hmem : definer₂ ∈ prefix₁ :=
          definer_mem_prefix_of_shorter heq hgt
        have hnone := hprefix₁ definer₂ hmem d₂ hfind₂
        rw [hmethod₂] at hnone; cases hnone
  exact definer_eq_of_same_length heq hlen
