import FwPython.Static.MRO.Properties
import FwPython.Gradual.Embedding
import FwPython.Gradual.ClassTable
import FwPython.Builtins

/-! # Gradual MRO: shared inductive instantiated at `GMethod`, plus gradual-only
executable search and erase/embed bridge lemmas. -/

abbrev GAllParentMros := AllParentMros (Method := GMethod)

abbrev GComputeMro := ComputeMro (Method := GMethod)

/-! ## Executable MRO search -/

mutual
/-- Fuel-bounded executable gradual MRO computation for a single class name. -/
def computeGMroFuel? : GClassTable → Nat → Identifier → Option (List Identifier)
  | _, 0, _ => none
  | gct, fuel + 1, cname =>
      match findGClass gct cname with
      | none => none
      | some cls =>
          match cls.resolvedBases with
          | [] => some [cls.name]
          | b :: rest =>
              let bases := b :: rest
              match computeAllParentMrosFuel? gct fuel bases with
              | none => none
              | some parentMros =>
                  match c3Merge (parentMros ++ [bases]) with
                  | none => none
                  | some mergedSuffix => some (cls.name :: mergedSuffix)
termination_by _gct fuel _cname => (fuel, 0)

/-- Fuel-bounded executable gradual MRO computation for every direct base. -/
def computeAllParentMrosFuel? :
    GClassTable → Nat → List Identifier → Option (List (List Identifier))
  | _, _, [] => some []
  | gct, fuel, bname :: rest =>
      match computeGMroFuel? gct fuel bname, computeAllParentMrosFuel? gct fuel rest with
      | some mro, some restMros => some (mro :: restMros)
      | _, _ => none
termination_by _gct fuel bases => (fuel, bases.length.succ)
end

/-- The executable gradual MRO search uses `gct.length` as global fuel. -/
def computeGMro? (gct : GClassTable) (cname : Identifier) : Option (List Identifier) :=
  computeGMroFuel? gct gct.length cname

/-- The executable parent-MRO search uses `gct.length` as global fuel. -/
def computeAllParentMros? (gct : GClassTable) (bases : List Identifier) :
    Option (List (List Identifier)) :=
  computeAllParentMrosFuel? gct gct.length bases

/-! ## Lookup helpers -/

theorem findGClass_name (h : findGClass ct cname = some c) : c.name = cname :=
  findClass_name h

theorem findGClass_self (h : findGClass ct cname = some c) :
    findGClass ct c.name = some c :=
  findClass_self h

/-! ## Executable-search soundness and proof heights -/

private theorem computeMroFuel_sound_pair (gct : GClassTable) :
    ∀ fuel,
      (∀ cname mro,
        computeGMroFuel? gct fuel cname = some mro →
          ∃ cls, findGClass gct cname = some cls ∧ GComputeMro gct cls mro) ∧
      (∀ bases parentMros,
        computeAllParentMrosFuel? gct fuel bases = some parentMros →
          GAllParentMros gct bases parentMros)
  | 0 =>
      ⟨
        by
          intro cname mro hcomp
          simp [computeGMroFuel?] at hcomp,
        by
          intro bases parentMros hcomp
          induction bases generalizing parentMros with
          | nil =>
              simp [computeAllParentMrosFuel?] at hcomp
              cases hcomp
              exact .nil
          | cons b rest ih =>
              simp [computeAllParentMrosFuel?, computeGMroFuel?] at hcomp
      ⟩
  | fuel + 1 =>
      let ⟨ihMro, ihParents⟩ := computeMroFuel_sound_pair gct fuel
      let hMro :
          ∀ cname mro,
            computeGMroFuel? gct (fuel + 1) cname = some mro →
              ∃ cls, findGClass gct cname = some cls ∧ GComputeMro gct cls mro := by
        intro cname mro hcomp
        simp [computeGMroFuel?] at hcomp
        cases hfind : findGClass gct cname with
        | none =>
            simp [hfind] at hcomp
        | some cls =>
            cases hbases : cls.resolvedBases with
            | nil =>
                simp [hfind, hbases] at hcomp
                cases hcomp
                exact ⟨cls, rfl, .root hbases⟩
            | cons b rest =>
                cases hparents : computeAllParentMrosFuel? gct fuel (b :: rest) with
                | none =>
                    simp [hfind, hbases, hparents] at hcomp
                | some parentMros =>
                    cases hmerge : c3Merge (parentMros ++ [b :: rest]) with
                    | none =>
                        simp [hfind, hbases, hparents, hmerge] at hcomp
                    | some mergedSuffix =>
                        simp [hfind, hbases, hparents, hmerge] at hcomp
                        cases hcomp
                        exact ⟨cls, rfl, .step hbases (by simp) (ihParents _ _ hparents) hmerge⟩
      let hParents :
          ∀ bases parentMros,
            computeAllParentMrosFuel? gct (fuel + 1) bases = some parentMros →
              GAllParentMros gct bases parentMros := by
        intro bases parentMros hcomp
        induction bases generalizing parentMros with
        | nil =>
            simp [computeAllParentMrosFuel?] at hcomp
            cases hcomp
            exact .nil
        | cons b rest ih =>
            simp [computeAllParentMrosFuel?] at hcomp
            cases hgmro : computeGMroFuel? gct (fuel + 1) b with
            | none =>
                simp [hgmro] at hcomp
            | some mro =>
                cases hrest : computeAllParentMrosFuel? gct (fuel + 1) rest with
                | none =>
                    simp [hgmro, hrest] at hcomp
                | some restMros =>
                    simp [hgmro, hrest] at hcomp
                    cases hcomp
                    obtain ⟨bcls, hfind, hmro⟩ := hMro _ _ hgmro
                    exact .cons hfind hmro (ih _ hrest)
      ⟨hMro, hParents⟩

theorem computeGMroFuel?_sound
    (hcomp : computeGMroFuel? gct fuel cname = some mro) :
    ∃ cls, findGClass gct cname = some cls ∧ GComputeMro gct cls mro :=
  (computeMroFuel_sound_pair gct fuel).1 _ _ hcomp

theorem computeAllParentMrosFuel?_sound
    (hcomp : computeAllParentMrosFuel? gct fuel bases = some parentMros) :
    GAllParentMros gct bases parentMros :=
  (computeMroFuel_sound_pair gct fuel).2 _ _ hcomp

theorem computeGMro?_sound
    (hcomp : computeGMro? gct cname = some mro) :
    ∃ cls, findGClass gct cname = some cls ∧ GComputeMro gct cls mro :=
  computeGMroFuel?_sound hcomp

theorem computeAllParentMros?_sound
    (hcomp : computeAllParentMros? gct bases = some parentMros) :
    GAllParentMros gct bases parentMros :=
  computeAllParentMrosFuel?_sound hcomp

mutual
/-- Exact recursive replay budget for an `GAllParentMros` derivation. -/
inductive GAllParentMrosHeight :
    GClassTable → List Identifier → List (List Identifier) → Nat → Prop where
  | nil :
      GAllParentMrosHeight ct [] [] 0
  | cons :
      findGClass ct bname = some bcls →
      GComputeMroHeight ct bcls mro fuelHead →
      GAllParentMrosHeight ct rest restMros fuelRest →
      GAllParentMrosHeight ct (bname :: rest) (mro :: restMros) (max fuelHead fuelRest)

/-- Exact recursive replay budget for a `GComputeMro` derivation. -/
inductive GComputeMroHeight :
    GClassTable → GClass → List Identifier → Nat → Prop where
  | root :
      c.resolvedBases = [] →
      GComputeMroHeight ct c [c.name] 1
  | step :
      c.resolvedBases = bases →
      bases ≠ [] →
      GAllParentMrosHeight ct bases parentMros fuelParents →
      c3Merge (parentMros ++ [bases]) = some mergedSuffix →
      GComputeMroHeight ct c (c.name :: mergedSuffix) (Nat.succ fuelParents)
end

mutual
theorem gAllParentMros_height
    (hall : GAllParentMros ct bases parentMros) :
    ∃ fuel, GAllParentMrosHeight ct bases parentMros fuel :=
  AllParentMros.rec
    (motive_1 := fun ct bases parentMros _ =>
      ∃ fuel, GAllParentMrosHeight ct bases parentMros fuel)
    (motive_2 := fun ct c mro _ =>
      ∃ fuel, GComputeMroHeight ct c mro fuel)
    ⟨0, .nil⟩
    (fun hfind _ _ ihMro ihRest => by
      rcases ihMro with ⟨fuelHead, hhHead⟩
      rcases ihRest with ⟨fuelRest, hhRest⟩
      exact ⟨max fuelHead fuelRest, .cons hfind hhHead hhRest⟩)
    (fun hnil => ⟨1, .root hnil⟩)
    (fun hbases hne _ hmerge ihParents => by
      rcases ihParents with ⟨fuelParents, hhParents⟩
      exact ⟨Nat.succ fuelParents, .step hbases hne hhParents hmerge⟩)
    hall

theorem gComputeMro_height
    (hmro : GComputeMro ct c mro) :
    ∃ fuel, GComputeMroHeight ct c mro fuel :=
  ComputeMro.rec
    (motive_1 := fun ct bases parentMros _ =>
      ∃ fuel, GAllParentMrosHeight ct bases parentMros fuel)
    (motive_2 := fun ct c mro _ =>
      ∃ fuel, GComputeMroHeight ct c mro fuel)
    ⟨0, .nil⟩
    (fun hfind _ _ ihMro ihRest => by
      rcases ihMro with ⟨fuelHead, hhHead⟩
      rcases ihRest with ⟨fuelRest, hhRest⟩
      exact ⟨max fuelHead fuelRest, .cons hfind hhHead hhRest⟩)
    (fun hnil => ⟨1, .root hnil⟩)
    (fun hbases hne _ hmerge ihParents => by
      rcases ihParents with ⟨fuelParents, hhParents⟩
      exact ⟨Nat.succ fuelParents, .step hbases hne hhParents hmerge⟩)
    hmro
end

mutual
private theorem gAllParentMros_of_height
    (hh : GAllParentMrosHeight ct bases parentMros fuel) :
    GAllParentMros ct bases parentMros :=
  GAllParentMrosHeight.rec
    (motive_1 := fun ct bases parentMros _ _ => GAllParentMros ct bases parentMros)
    (motive_2 := fun ct c mro _ _ => GComputeMro ct c mro)
    .nil
    (fun hfind _ _ ihMro ihRest => .cons hfind ihMro ihRest)
    (fun hnil => .root hnil)
    (fun hbases hne _ hmerge ihParents => .step hbases hne ihParents hmerge)
    hh

private theorem gComputeMro_of_height
    (hh : GComputeMroHeight ct c mro fuel) :
    GComputeMro ct c mro :=
  GComputeMroHeight.rec
    (motive_1 := fun ct bases parentMros _ _ => GAllParentMros ct bases parentMros)
    (motive_2 := fun ct c mro _ _ => GComputeMro ct c mro)
    .nil
    (fun hfind _ _ ihMro ihRest => .cons hfind ihMro ihRest)
    (fun hnil => .root hnil)
    (fun hbases hne _ hmerge ihParents => .step hbases hne ihParents hmerge)
    hh
end

mutual
theorem computeAllParentMrosFuel?_complete_of_height
    (hh : GAllParentMrosHeight gct bases parentMros fuelHeight)
    (hle : fuelHeight ≤ fuel) :
    computeAllParentMrosFuel? gct fuel bases = some parentMros := by
  have key := GAllParentMrosHeight.rec
    (motive_1 := fun gct bases parentMros fuelHeight _ =>
      ∀ fuel, fuelHeight ≤ fuel → computeAllParentMrosFuel? gct fuel bases = some parentMros)
    (motive_2 := fun gct c mro fuelHeight _ =>
      ∀ fuel cname, findGClass gct cname = some c →
        fuelHeight ≤ fuel → computeGMroFuel? gct fuel cname = some mro)
    (fun fuel _ => by simp [computeAllParentMrosFuel?])
    (fun hfind _ _ ihMro ihRest fuel hle => by
      have hhead : _ ≤ fuel := Nat.le_trans (Nat.le_max_left _ _) hle
      have hrest : _ ≤ fuel := Nat.le_trans (Nat.le_max_right _ _) hle
      simp [computeAllParentMrosFuel?,
        ihMro _ _ hfind hhead,
        ihRest _ hrest])
    (fun hnil fuel cname hfind hle => by
      cases fuel with
      | zero =>
          cases hle
      | succ fuel =>
          simp [computeGMroFuel?, hfind, hnil])
    (fun {bases} {ct} {parentMros} {fuelParents} {mergedSuffix} {c}
         hbases hne _ hmerge ihParents fuel cname hfind hle => by
      cases fuel with
      | zero =>
          cases hle
      | succ fuel =>
          have hparents : fuelParents ≤ fuel := Nat.succ_le_succ_iff.mp hle
          cases bases with
          | nil =>
              exact (hne rfl).elim
          | cons b rest =>
              simp [computeGMroFuel?, hfind, hbases, ihParents _ hparents, hmerge])
    hh
  exact key _ hle

theorem computeGMroFuel?_complete_of_height
    (hfind : findGClass gct cname = some cls)
    (hh : GComputeMroHeight gct cls mro fuelHeight)
    (hle : fuelHeight ≤ fuel) :
    computeGMroFuel? gct fuel cname = some mro := by
  have key := GComputeMroHeight.rec
    (motive_1 := fun gct bases parentMros fuelHeight _ =>
      ∀ fuel, fuelHeight ≤ fuel → computeAllParentMrosFuel? gct fuel bases = some parentMros)
    (motive_2 := fun gct c mro fuelHeight _ =>
      ∀ fuel cname, findGClass gct cname = some c →
        fuelHeight ≤ fuel → computeGMroFuel? gct fuel cname = some mro)
    (fun fuel _ => by simp [computeAllParentMrosFuel?])
    (fun hfind _ _ ihMro ihRest fuel hle => by
      have hhead : _ ≤ fuel := Nat.le_trans (Nat.le_max_left _ _) hle
      have hrest : _ ≤ fuel := Nat.le_trans (Nat.le_max_right _ _) hle
      simp [computeAllParentMrosFuel?,
        ihMro _ _ hfind hhead,
        ihRest _ hrest])
    (fun hnil fuel cname hfind hle => by
      cases fuel with
      | zero =>
          cases hle
      | succ fuel =>
          simp [computeGMroFuel?, hfind, hnil])
    (fun {bases} {ct} {parentMros} {fuelParents} {mergedSuffix} {c}
         hbases hne _ hmerge ihParents fuel cname hfind hle => by
      cases fuel with
      | zero =>
          cases hle
      | succ fuel =>
          have hparents : fuelParents ≤ fuel := Nat.succ_le_succ_iff.mp hle
          cases bases with
          | nil =>
              exact (hne rfl).elim
          | cons b rest =>
              simp [computeGMroFuel?, hfind, hbases, ihParents _ hparents, hmerge])
    hh
  exact key _ _ hfind hle
end

/-- Forward MRO bridge: gradual MRO implies fully static MRO on the erased table. -/
theorem gComputeMro_eraseClassTable
    (h : GComputeMro gct gc mro) :
    ComputeMro (eraseClassTable gct) (eraseClass gc) mro :=
  ComputeMro.rec
    (motive_1 := fun gct bases parentMros _ =>
      AllParentMros (eraseClassTable gct) bases parentMros)
    (motive_2 := fun gct gc mro _ =>
      ComputeMro (eraseClassTable gct) (eraseClass gc) mro)
    .nil
    (fun hfind _ _ ihMro ihRest => .cons (findClass_eraseClassTable hfind) ihMro ihRest)
    (fun hnil => .root (by simpa using hnil))
    (fun hbases hne _ hmerge ihParents =>
      .step (by simpa using hbases) hne ihParents hmerge)
    h

/-- Forward MRO bridge for embedded class tables. -/
theorem computeGMro_embedClassTable
    (h : ComputeMro ct c mro) :
    GComputeMro (embedClassTable ct) (embedClass c) mro :=
  ComputeMro.rec
    (motive_1 := fun ct bases parentMros _ =>
      GAllParentMros (embedClassTable ct) bases parentMros)
    (motive_2 := fun ct c mro _ =>
      GComputeMro (embedClassTable ct) (embedClass c) mro)
    .nil
    (fun hfind _ _ ihMro ihRest =>
      .cons (findGClass_embedClassTable hfind) ihMro ihRest)
    (fun hnil => .root (by simpa using hnil))
    (fun hbases hne _ hmerge ihParents =>
      .step (by simpa using hbases) hne ihParents hmerge)
    h

private theorem gDirectBase_mem_mro
    (hmro : GComputeMro gct c mro)
    (hb : bname ∈ c.resolvedBases) :
    bname ∈ mro := by
  cases hmro with
  | root hnil =>
      rw [hnil] at hb
      exact absurd hb List.not_mem_nil
  | step hbases _ _ hmerge =>
      rw [hbases] at hb
      exact List.mem_cons_of_mem _ <|
        c3Merge_complete hmerge _ (List.mem_append_right _ (List.Mem.head _)) _ hb

private theorem gParent_mro_excludes_self
    (hfindC : findGClass gct c.name = some c)
    (hmroC : GComputeMro gct c mroC)
    (hb : bname ∈ c.resolvedBases)
    (hfindB : findGClass gct bname = some bcls)
    (hmroB : GComputeMro gct bcls mroB) :
    c.name ∉ mroB := by
  intro hcInB
  have hfindCE : findClass (eraseClassTable gct) c.name = some (eraseClass c) :=
    findClass_eraseClassTable hfindC
  have hfindBE : findClass (eraseClassTable gct) bname = some (eraseClass bcls) :=
    findClass_eraseClassTable hfindB
  have hmroCE := gComputeMro_eraseClassTable hmroC
  have hmroBE := gComputeMro_eraseClassTable hmroB
  have hbInC : bname ∈ mroC := gDirectBase_mem_mro hmroC hb
  have hEq : c.name = bname :=
    mro_member_antisymm
      (ct := eraseClassTable gct)
      hfindCE hmroCE hfindBE hmroBE hbInC hcInB
  have hnoSelf : c.name ∉ c.resolvedBases := by
    have := (mro_acyclic (ct := eraseClassTable gct) hfindCE hmroCE).1
    simpa using this
  exact hnoSelf (by simpa [hEq] using hb)

private def HasGChainInfo (gct : GClassTable)
    (fuel : Nat) (headName : Identifier) (mro : List Identifier) : Prop :=
  ∃ chain : List Identifier,
    chain.length = fuel ∧
    chain.head? = some headName ∧
    chain.Nodup ∧
    (∀ x, x ∈ chain → ∃ cls, findGClass gct x = some cls) ∧
    (∀ x, x ∈ chain → x ∈ mro)

private def HasGParentChainWitness (gct : GClassTable)
    (bases : List Identifier) (parentMros : List (List Identifier)) (fuel : Nat) : Prop :=
  ∃ bname bcls pmro, ∃ chain : List Identifier,
    findGClass gct bname = some bcls ∧
    GComputeMroHeight gct bcls pmro fuel ∧
    bname ∈ bases ∧
    pmro ∈ parentMros ∧
    chain.length = fuel ∧
    chain.head? = some bname ∧
    chain.Nodup ∧
    (∀ x, x ∈ chain → ∃ cls, findGClass gct x = some cls) ∧
    (∀ x, x ∈ chain → x ∈ pmro)

private def gComputeMroHeight_chain
    (hfind : findGClass gct c.name = some c)
    (hh : GComputeMroHeight gct c mro fuel) :
    HasGChainInfo gct fuel c.name mro := by
  have key := GComputeMroHeight.rec
    (motive_1 := fun gct bases parentMros fuel _ =>
      fuel = 0 ∧ bases = [] ∧ parentMros = [] ∨
        HasGParentChainWitness gct bases parentMros fuel)
    (motive_2 := fun gct c mro fuel _ =>
      findGClass gct c.name = some c → HasGChainInfo gct fuel c.name mro)
    (Or.inl ⟨rfl, rfl, rfl⟩)
    (fun {ct} {bname} {bcls} {mro} {fuelHead} {rest} {restMros} {fuelRest}
         hfind hhHead _ ihMro ihRest => by
      have infoHead : HasGChainInfo ct fuelHead bname mro := by
        simpa [findGClass_name hfind] using ihMro (findGClass_self hfind)
      rcases infoHead with ⟨chainHead, hlenHead, hheadHead, hnodupHead, hfoundHead, hmemHead⟩
      by_cases hle : fuelRest ≤ fuelHead
      · refine Or.inr ?_
        simpa [Nat.max_eq_left hle] using
          (show HasGParentChainWitness ct (bname :: rest) (mro :: restMros) fuelHead from
            ⟨bname, bcls, mro, chainHead, hfind, hhHead, List.Mem.head _, List.Mem.head _,
              hlenHead, hheadHead, hnodupHead, hfoundHead, hmemHead⟩)
      · have hlt : fuelHead < fuelRest := Nat.lt_of_not_ge hle
        rcases ihRest with ⟨hzero, _, _⟩ |
            ⟨bnameRest, bclsRest, pmroRest, chainRest, hfindRest, hhRest,
              hbaseRest, hpmroRest, hlenRest, hheadRest, hnodupRest, hfoundRest, hmemRest⟩
        · simp [hzero] at hlt
        · refine Or.inr ?_
          simpa [Nat.max_eq_right (Nat.le_of_lt hlt)] using
            (show HasGParentChainWitness ct (bname :: rest) (mro :: restMros) fuelRest from
              ⟨bnameRest, bclsRest, pmroRest, chainRest, hfindRest, hhRest,
                List.mem_cons_of_mem _ hbaseRest, List.mem_cons_of_mem _ hpmroRest,
                hlenRest, hheadRest, hnodupRest, hfoundRest, hmemRest⟩))
    (fun {ct} {c} hnil hfindC => by
      refine ⟨[c.name], rfl, rfl, by simp, ?_, ?_⟩
      · intro x hx
        simp at hx
        subst hx
        exact ⟨c, hfindC⟩
      · intro x hx
        simpa using hx)
    (fun {bases} {ct} {parentMros} {fuelParents} {mergedSuffix} {c}
         hbases hne hhParents hmerge ihParents hfindC => by
      let hmroC : GComputeMro ct c (c.name :: mergedSuffix) :=
        .step hbases hne (gAllParentMros_of_height hhParents) hmerge
      rcases ihParents with ⟨_, hbasesNil, _⟩ |
          ⟨bname, bcls, pmro, chain, hfindB, hhB, hbase, hpmro, hlen, hhead, hnodup, hfound, hmem⟩
      · exact False.elim (hne hbasesNil)
      · have hnotin : c.name ∉ chain := by
          intro hcIn
          exact
            (gParent_mro_excludes_self
              hfindC hmroC (by simpa [hbases] using hbase) hfindB (gComputeMro_of_height hhB))
              (hmem _ hcIn)
        refine ⟨c.name :: chain, by simp [hlen], rfl, ?_, ?_, ?_⟩
        · exact List.nodup_cons.mpr ⟨hnotin, hnodup⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨c, hfindC⟩
          · exact hfound x hx
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.Mem.head _
          · exact List.mem_cons_of_mem _ <|
              c3Merge_complete hmerge pmro (List.mem_append_left _ hpmro) _ (hmem _ hx))
    hh
  exact key hfind

private theorem mem_names_of_findGClass
    (hfind : findGClass gct cname = some c) :
    cname ∈ gct.map ClassDecl.name := by
  have hmem : c ∈ gct := findClass_mem hfind
  rw [← findGClass_name hfind]
  exact List.mem_map_of_mem (f := ClassDecl.name) hmem

private theorem splitAtMem
    {x : Identifier} :
    ∀ {ys : List Identifier}, x ∈ ys →
      ∃ ys₁ ys₂, ys = ys₁ ++ x :: ys₂
  | [], h => by
      cases h
  | y :: ys, h => by
      cases h with
      | head =>
          exact ⟨[], ys, rfl⟩
      | tail _ htail =>
          obtain ⟨ys₁, ys₂, hsplit⟩ := splitAtMem htail
          exact ⟨y :: ys₁, ys₂, by simp [hsplit]⟩

private theorem nodup_length_le_of_subset
    {xs ys : List Identifier}
    (hxs : xs.Nodup)
    (hsub : ∀ x, x ∈ xs → x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil =>
      simp
  | cons x xs ih =>
      have hx_notin : x ∉ xs := (List.nodup_cons.mp hxs).1
      have hxs' : xs.Nodup := (List.nodup_cons.mp hxs).2
      have hy : x ∈ ys := hsub x (List.Mem.head _)
      obtain ⟨ys₁, ys₂, hsplit⟩ := splitAtMem hy
      have hsub' : ∀ z, z ∈ xs → z ∈ ys₁ ++ ys₂ := by
        intro z hz
        have hzys : z ∈ ys₁ ++ x :: ys₂ := by
          rw [← hsplit]
          exact hsub z (List.Mem.tail _ hz)
        have hzx : z ≠ x := by
          intro hzx
          exact hx_notin (hzx.symm ▸ hz)
        simp [List.mem_append, hzx] at hzys ⊢
        exact hzys
      have hlen := ih hxs' hsub'
      have hlen' : xs.length + 1 ≤ ys.length := by
        have hplus := Nat.add_le_add_right hlen 1
        have hplus' : xs.length + 1 ≤ ys₁.length + ys₂.length + 1 := by
          simpa [List.length_append, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hplus
        simpa [hsplit, List.length_append, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hplus'
      exact hlen'

theorem gComputeMro_height_le_tableSize
    (hfind : findGClass gct c.name = some c)
    (hh : GComputeMroHeight gct c mro fuel) :
    fuel ≤ gct.length := by
  rcases gComputeMroHeight_chain hfind hh with ⟨chain, hlen, _, hnodup, hfound, _⟩
  have hsubset : ∀ x, x ∈ chain → x ∈ gct.map ClassDecl.name := by
    intro x hx
    rcases hfound x hx with ⟨cls, hfindx⟩
    exact mem_names_of_findGClass hfindx
  have hlen' : chain.length ≤ (gct.map ClassDecl.name).length :=
    nodup_length_le_of_subset hnodup hsubset
  simpa [hlen] using hlen'

theorem computeGMro?_complete
    (hfind : findGClass gct cname = some cls)
    (hmro : GComputeMro gct cls mro) :
    computeGMro? gct cname = some mro := by
  obtain ⟨fuel, hh⟩ := gComputeMro_height hmro
  exact computeGMroFuel?_complete_of_height hfind hh
    (gComputeMro_height_le_tableSize (findGClass_self hfind) hh)

/-! ## Main theorems -/

/-- Determinism: the gradual MRO of a class is unique. -/
theorem gComputeMro_determinism (h1 : GComputeMro ct c mro₁)
    (h2 : GComputeMro ct c mro₂) : mro₁ = mro₂ :=
  determinism h1 h2
