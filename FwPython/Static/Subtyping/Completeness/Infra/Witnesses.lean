import FwPython.Static.Subtyping.Core
import FwPython.Static.Subtyping.Lattice
import FwPython.Static.Subtyping.AbstractSemantics
import FwPython.Static.Subtyping.SemObject
import FwPython.Static.Subtyping.Inversion
import FwPython.Static.Subtyping.Negation
import FwPython.Static.Subtyping.WellFormedTy
import FwPython.Static.TypeSystem.Invariants
import FwPython.Static.MRO.Properties

/-! ## Constructive completeness infrastructure -/

/-! ### Built-in leaves and canonical semantic objects -/

@[simp] theorem objectClass_ne_boolClass : objectClass ≠ boolClass := by
  decide

@[simp] theorem objectClass_ne_noneClass : objectClass ≠ noneClass := by
  decide

@[simp] theorem objectClass_ne_boundMethodClass : objectClass ≠ boundMethodClass := by
  decide

@[simp] theorem boolClass_ne_noneClass : boolClass ≠ noneClass := by
  decide

@[simp] theorem boolClass_ne_boundMethodClass : boolClass ≠ boundMethodClass := by
  decide

@[simp] theorem noneClass_ne_boundMethodClass : noneClass ≠ boundMethodClass := by
  decide

theorem leafBuiltin_iff_builtinName (hwfct : WellFormedClassTable ct) :
    LeafBuiltin ct C ↔ C = boolClass ∨ C = noneClass ∨ C = boundMethodClass := by
  refine ⟨?_, ?_⟩
  · intro hleaf
    cases hleaf with
    | bool => exact Or.inl rfl
    | none => exact Or.inr (Or.inl rfl)
    | boundMethod => exact Or.inr (Or.inr rfl)
  · intro hC
    rcases hC with rfl | hC
    · exact leafBuiltin_bool hwfct
    · rcases hC with rfl | rfl
      · exact leafBuiltin_none hwfct
      · exact leafBuiltin_boundMethod hwfct

instance builtinLeafDecidable (hwfct : WellFormedClassTable ct) :
    Decidable (LeafBuiltin ct C) := by
  by_cases hbool : C = boolClass
  · exact isTrue ((leafBuiltin_iff_builtinName (ct := ct) (C := C) hwfct).2 (Or.inl hbool))
  · by_cases hnone : C = noneClass
    · exact isTrue ((leafBuiltin_iff_builtinName (ct := ct) (C := C) hwfct).2 (Or.inr (Or.inl hnone)))
    · by_cases hbm : C = boundMethodClass
      · exact isTrue ((leafBuiltin_iff_builtinName (ct := ct) (C := C) hwfct).2 (Or.inr (Or.inr hbm)))
      · exact isFalse (fun hleaf =>
          match (leafBuiltin_iff_builtinName (ct := ct) (C := C) hwfct).1 hleaf with
          | Or.inl hC => hbool hC
          | Or.inr (Or.inl hC) => hnone hC
          | Or.inr (Or.inr hC) => hbm hC)

theorem object_not_leaf (hwfct : WellFormedClassTable ct) :
    ¬ LeafBuiltin ct objectClass := by
  intro hleaf
  rcases (leafBuiltin_iff_builtinName (ct := ct) (C := objectClass) hwfct).1 hleaf with
    hobj | hobj | hobj
  · exact objectClass_ne_boolClass hobj
  · exact objectClass_ne_noneClass hobj
  · exact objectClass_ne_boundMethodClass hobj

theorem mro_of_object (hwfct : WellFormedClassTable ct) :
    ComputeMro ct hwfct.objectExists.cls [objectClass] := by
  simpa [findClass_name hwfct.objectExists.hfind] using
    (ComputeMro.root ((resolvedBases_nil_iff _).2
      ⟨hwfct.objectExists.hbases, findClass_name hwfct.objectExists.hfind⟩) :
        ComputeMro ct hwfct.objectExists.cls [hwfct.objectExists.cls.name])

theorem object_mro_unique (hwfct : WellFormedClassTable ct)
    (hmro : ComputeMro ct hwfct.objectExists.cls mro) :
    mro = [objectClass] := by
  simpa [findClass_name hwfct.objectExists.hfind] using
    determinism hmro (mro_of_object (ct := ct) hwfct)

def wfLookup
    (hwfct : WellFormedClassTable ct) (C : Identifier)
    (hne : findClass ct C ≠ none) :
    ClassLookupWitness ct C := by
  cases hfind : findClass ct C with
  | none => exact absurd hfind hne
  | some cls =>
      let hmro := hwfct.allMrosExist C cls hfind
      exact ⟨cls, hmro.mro, hfind, hmro.hmro⟩

def wfClassLookup
    (hwfct : WellFormedClassTable ct)
    (hwf : WellFormedTy ct (.class_ C)) :
    ClassLookupWitness ct C :=
  wfLookup hwfct C hwf.class_find_ne_none

def wfNegLookup
    (hwfct : WellFormedClassTable ct)
    (hwf : WellFormedTy ct (.negClass C)) :
    ClassLookupWitness ct C :=
  wfLookup hwfct C hwf.negClass_find_ne_none

def currentObjOf (cname : Identifier)
    (hfind : findClass ct cname = some cls)
    (hmro : ComputeMro ct cls mro) :
    SemObject ct :=
  .ordinaryCurrent { cname, cls, mro, hfind, hmro }

def freshSeedsObj
    (seeds : List Identifier)
    (hseeds_ne : seeds ≠ [])
    (hseeds_nodup : seeds.Nodup)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s) :
    SemObject ct :=
  .ordinaryFresh
    { seeds, seeds_ne := hseeds_ne, seeds_nodup := hseeds_nodup,
      seedWitness, seed_nonleaf }

def freshSingletonObj
    (seed : Identifier)
    (hfind : findClass ct seed = some cls)
    (hmro : ComputeMro ct cls mro)
    (hnonleaf : ¬ LeafBuiltin ct seed) :
    SemObject ct :=
  freshSeedsObj
    [seed]
    (by simp)
    (by simp)
    (fun s hs => by
      simp at hs
      subst hs
      exact ⟨cls, mro, hfind, hmro⟩)
    (fun s hs => by
      simp at hs
      subst hs
      exact hnonleaf)

def boundMethodObj (hwfct : WellFormedClassTable ct) (P R : Ty) :
    SemObject ct :=
  .boundMethod
    { actualParam := P
      actualReturn := R
      cls := hwfct.boundMethodExists.cls
      mro := hwfct.boundMethodExists.mro
      hfind := hwfct.boundMethodExists.hfind
      hmro := hwfct.boundMethodExists.hmro }

theorem currentObjOf_denotes_class
    (hfind : findClass ct C = some cls)
    (hmro : ComputeMro ct cls mro) :
    Ty.semDenotes ct (.class_ D) (currentObjOf (ct := ct) C hfind hmro) ↔ D ∈ mro := by
  simp [currentObjOf, Ty.semDenotes, SemObject.hasAncestor, CurrentOrd.hasAncestor]

theorem currentObjOf_denotes_neg_iff
    (hfind : findClass ct C = some cls)
    (hmro : ComputeMro ct cls mro) :
    Ty.semDenotes ct (.negClass D) (currentObjOf (ct := ct) C hfind hmro) ↔ D ∉ mro := by
  simp [currentObjOf, Ty.semDenotes, SemObject.hasAncestor, CurrentOrd.hasAncestor]

theorem currentObjOf_not_denotes_callable
    (hfind : findClass ct C = some cls)
    (hmro : ComputeMro ct cls mro) :
    ¬ Ty.semDenotes ct (.callable P R) (currentObjOf (ct := ct) C hfind hmro) := by
  simp [currentObjOf, Ty.semDenotes]

theorem freshSeedsObj_denotes_class_iff
    (seeds : List Identifier)
    (hseeds_ne : seeds ≠ [])
    (hseeds_nodup : seeds.Nodup)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s) :
    Ty.semDenotes ct (.class_ C)
      (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf) ↔
      ∃ s hs, C ∈ (seedWitness s hs).mro := by
  simp [freshSeedsObj, Ty.semDenotes, SemObject.hasAncestor, FreshOrd.hasAncestor]

theorem freshSeedsObj_denotes_neg_iff
    (seeds : List Identifier)
    (hseeds_ne : seeds ≠ [])
    (hseeds_nodup : seeds.Nodup)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s) :
    Ty.semDenotes ct (.negClass C)
      (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf) ↔
      ¬ ∃ s hs, C ∈ (seedWitness s hs).mro := by
  rfl

theorem freshSeedsObj_denotes_neg_leaf
    (seeds : List Identifier)
    (hseeds_ne : seeds ≠ [])
    (hseeds_nodup : seeds.Nodup)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s)
    (hleaf : LeafBuiltin ct B) :
    Ty.semDenotes ct (.negClass B)
      (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf) := by
  rw [freshSeedsObj_denotes_neg_iff]
  rintro ⟨s, hs, hmem⟩
  let info := seedWitness s hs
  have hs_eq := LeafBuiltin.sealed hleaf s info.cls info.mro info.hfind info.hmro hmem
  exact seed_nonleaf s hs (hs_eq ▸ hleaf)

theorem freshSeedsObj_not_denotes_callable
    (seeds : List Identifier)
    (hseeds_ne : seeds ≠ [])
    (hseeds_nodup : seeds.Nodup)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s) :
    ¬ Ty.semDenotes ct (.callable P R)
      (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf) := by
  simp [freshSeedsObj, Ty.semDenotes]

theorem boundMethodObj_denotes_callable_self (hwfct : WellFormedClassTable ct) :
    Ty.semDenotes ct (.callable P R) (boundMethodObj (ct := ct) hwfct P R) := by
  simpa [boundMethodObj] using
    boundMethod_denotes_callable_self
      { actualParam := P
        actualReturn := R
        cls := hwfct.boundMethodExists.cls
        mro := hwfct.boundMethodExists.mro
        hfind := hwfct.boundMethodExists.hfind
        hmro := hwfct.boundMethodExists.hmro }

theorem boundMethodObj_denotes_class_iff (hwfct : WellFormedClassTable ct) :
    Ty.semDenotes ct (.class_ C) (boundMethodObj (ct := ct) hwfct P R) ↔
      C ∈ hwfct.boundMethodExists.mro := by
  simp [boundMethodObj, Ty.semDenotes, SemObject.hasAncestor, BoundMethodOrd.hasAncestor]

theorem boundMethodObj_denotes_neg_iff (hwfct : WellFormedClassTable ct) :
    Ty.semDenotes ct (.negClass C) (boundMethodObj (ct := ct) hwfct P R) ↔
      C ∉ hwfct.boundMethodExists.mro := by
  simp [boundMethodObj, Ty.semDenotes, SemObject.hasAncestor, BoundMethodOrd.hasAncestor]

theorem object_current_denotes_neg_nonobject (hwfct : WellFormedClassTable ct)
    (hC : C ≠ objectClass) :
    Ty.semDenotes ct (.negClass C)
      (currentObjOf (ct := ct) objectClass hwfct.objectExists.hfind (mro_of_object (ct := ct) hwfct)) := by
  simp [currentObjOf, Ty.semDenotes, SemObject.hasAncestor, CurrentOrd.hasAncestor, hC]

theorem object_fresh_denotes_neg_nonobject (hwfct : WellFormedClassTable ct)
    (hC : C ≠ objectClass) :
    Ty.semDenotes ct (.negClass C)
      (freshSingletonObj (ct := ct)
        objectClass
        hwfct.objectExists.hfind
        (mro_of_object (ct := ct) hwfct)
        (object_not_leaf (ct := ct) hwfct)) := by
  simp [freshSingletonObj, freshSeedsObj, Ty.semDenotes, SemObject.hasAncestor,
    FreshOrd.hasAncestor, hC]

theorem object_current_not_denotes_class_nonobject (hwfct : WellFormedClassTable ct)
    (hC : C ≠ objectClass) :
    ¬ Ty.semDenotes ct (.class_ C)
      (currentObjOf (ct := ct) objectClass hwfct.objectExists.hfind (mro_of_object (ct := ct) hwfct)) := by
  simp [currentObjOf, Ty.semDenotes, SemObject.hasAncestor, CurrentOrd.hasAncestor, hC]

theorem object_current_not_denotes_callable (hwfct : WellFormedClassTable ct) :
    ¬ Ty.semDenotes ct (.callable P R)
      (currentObjOf (ct := ct) objectClass hwfct.objectExists.hfind (mro_of_object (ct := ct) hwfct)) := by
  exact currentObjOf_not_denotes_callable
    (ct := ct)
    (C := objectClass)
    (cls := hwfct.objectExists.cls)
    (mro := [objectClass])
    hwfct.objectExists.hfind
    (mro_of_object (ct := ct) hwfct)

