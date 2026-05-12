import FwPython.Static.Subtyping.Core

/-! ## Legacy abstract carrier -/

/-- Compatibility carrier for the pre-swap abstract semantics. -/
inductive AbstractObject where
  | ordinary : Identifier → AbstractObject
  | boundMethod : Ty → Ty → AbstractObject

/-- Compatibility runtime-class projection for `AbstractObject`. -/
def AbstractObject.runtimeClass : AbstractObject → Identifier
  | .ordinary cname => cname
  | .boundMethod _ _ => boundMethodClass

/-! ## Semantic carrier

`SemObject` is the only semantic runtime carrier. It distinguishes:
- ordinary heap objects with a chosen current class witness;
- fresh open-world ordinary objects, represented by a nonempty family of
  possible current-class seeds;
- bound methods, whose runtime class is always `BoundMethod` and whose
  callable signature is stored directly.

The shape-specific structures retain the class/MRO witnesses needed for
semantic transport lemmas. -/

/-- Concrete witness data for one fresh-current-class seed. -/
structure FreshSeedInfo (ct : ClassTable) (s : Identifier) where
  cls : Class
  mro : List Identifier
  hfind : findClass ct s = some cls
  hmro : ComputeMro ct cls mro

/-- Ordinary object whose exact current class is known. -/
structure CurrentOrd (ct : ClassTable) where
  cname : Identifier
  cls : Class
  mro : List Identifier
  hfind : findClass ct cname = some cls
  hmro : ComputeMro ct cls mro

/-- Open-world ordinary object described by a nonempty family of possible
current-class seeds. -/
structure FreshOrd (ct : ClassTable) where
  seeds : List Identifier
  seeds_ne : seeds ≠ []
  seeds_nodup : seeds.Nodup
  seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s
  seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s

/-- Bound-method semantic object. Its runtime class is always `BoundMethod`,
and its MRO witness is therefore pinned to that class. -/
structure BoundMethodOrd (ct : ClassTable) where
  actualParam : Ty
  actualReturn : Ty
  cls : Class
  mro : List Identifier
  hfind : findClass ct boundMethodClass = some cls
  hmro : ComputeMro ct cls mro

/-- The unified semantic runtime carrier. -/
inductive SemObject (ct : ClassTable) where
  | ordinaryCurrent : CurrentOrd ct → SemObject ct
  | ordinaryFresh : FreshOrd ct → SemObject ct
  | boundMethod : BoundMethodOrd ct → SemObject ct

def CurrentOrd.hasAncestor (cur : CurrentOrd ct) (C : Identifier) : Prop :=
  C ∈ cur.mro

def FreshOrd.hasAncestor (fr : FreshOrd ct) (C : Identifier) : Prop :=
  ∃ s hs, C ∈ (fr.seedWitness s hs).mro

def BoundMethodOrd.hasAncestor (bm : BoundMethodOrd ct) (C : Identifier) : Prop :=
  C ∈ bm.mro

def SemObject.hasAncestor : SemObject ct → Identifier → Prop
  | .ordinaryCurrent cur => cur.hasAncestor
  | .ordinaryFresh fr => fr.hasAncestor
  | .boundMethod bm => bm.hasAncestor

private theorem FreshOrd.hasAncestor_iff_any (fr : FreshOrd ct) (C : Identifier) :
    fr.hasAncestor C ↔
      fr.seeds.attach.any (fun s => decide (C ∈ (fr.seedWitness s.1 s.2).mro)) = true := by
  refine ⟨fun ⟨s, hs, hmem⟩ => List.any_eq_true.mpr ⟨⟨s, hs⟩, List.mem_attach _ _, by simp [hmem]⟩,
          fun hany => ?_⟩
  rcases List.any_eq_true.mp hany with ⟨s, _, hs⟩
  exact ⟨s.1, s.2, by simpa using hs⟩

instance (cur : CurrentOrd ct) (C : Identifier) : Decidable (cur.hasAncestor C) :=
  inferInstanceAs (Decidable (C ∈ cur.mro))

instance (fr : FreshOrd ct) (C : Identifier) : Decidable (fr.hasAncestor C) :=
  decidable_of_decidable_of_iff (FreshOrd.hasAncestor_iff_any fr C).symm

instance (bm : BoundMethodOrd ct) (C : Identifier) : Decidable (bm.hasAncestor C) :=
  inferInstanceAs (Decidable (C ∈ bm.mro))

instance (obj : SemObject ct) (C : Identifier) : Decidable (obj.hasAncestor C) := by
  cases obj <;> simp [SemObject.hasAncestor] <;> infer_instance

theorem CurrentOrd.self_mem (cur : CurrentOrd ct) :
    cur.hasAncestor cur.cname := by
  simpa [CurrentOrd.hasAncestor, findClass_name cur.hfind] using mro_self_mem cur.hmro

theorem CurrentOrd.object_mem (cur : CurrentOrd ct) :
    cur.hasAncestor objectClass := by
  simpa [CurrentOrd.hasAncestor] using mro_contains_object cur.hmro

theorem CurrentOrd.hasAncestor_closed (cur : CurrentOrd ct)
    (hanc : cur.hasAncestor A)
    (hfind : findClass ct A = some acls) (hmro : ComputeMro ct acls amro) (hmem : B ∈ amro) :
    cur.hasAncestor B :=
  mro_mem_trans ct cur.cls acls cur.mro amro B
    (findClass_self cur.hfind) cur.hmro (findClass_self hfind) hmro
    (by simpa [findClass_name hfind] using hanc) hmem

theorem FreshOrd.object_mem (fr : FreshOrd ct) : fr.hasAncestor objectClass :=
  let ⟨s, hs⟩ := List.exists_mem_of_ne_nil fr.seeds fr.seeds_ne
  ⟨s, hs, mro_contains_object (fr.seedWitness s hs).hmro⟩

theorem FreshOrd.no_leaf_builtin_ancestor (fr : FreshOrd ct)
    (hleaf : LeafBuiltin ct B) : ¬ fr.hasAncestor B := by
  rintro ⟨s, hs, hmem⟩
  let info := fr.seedWitness s hs
  have hs_eq := LeafBuiltin.sealed hleaf s info.cls info.mro info.hfind info.hmro hmem
  exact fr.seed_nonleaf s hs (hs_eq ▸ hleaf)

theorem FreshOrd.hasAncestor_closed (fr : FreshOrd ct)
    (hanc : fr.hasAncestor A)
    (hfind : findClass ct A = some acls) (hmro : ComputeMro ct acls amro) (hmem : B ∈ amro) :
    fr.hasAncestor B := by
  rcases hanc with ⟨s, hs, hmemA⟩
  let info := fr.seedWitness s hs
  exact ⟨s, hs, mro_mem_trans ct info.cls acls info.mro amro B
    (findClass_self info.hfind) info.hmro (findClass_self hfind) hmro
    (by simpa [findClass_name hfind] using hmemA) hmem⟩

theorem BoundMethodOrd.self_mem (bm : BoundMethodOrd ct) :
    bm.hasAncestor boundMethodClass := by
  simpa [BoundMethodOrd.hasAncestor, findClass_name bm.hfind] using mro_self_mem bm.hmro

theorem BoundMethodOrd.object_mem (bm : BoundMethodOrd ct) :
    bm.hasAncestor objectClass := by
  simpa [BoundMethodOrd.hasAncestor] using mro_contains_object bm.hmro

theorem BoundMethodOrd.hasAncestor_closed (bm : BoundMethodOrd ct)
    (hanc : bm.hasAncestor A)
    (hfind : findClass ct A = some acls) (hmro : ComputeMro ct acls amro) (hmem : B ∈ amro) :
    bm.hasAncestor B :=
  mro_mem_trans ct bm.cls acls bm.mro amro B
    (findClass_self bm.hfind) bm.hmro (findClass_self hfind) hmro
    (by simpa [findClass_name hfind] using hanc) hmem
