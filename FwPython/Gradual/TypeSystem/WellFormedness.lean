import FwPython.Gradual.TypeSystem.Context
import FwPython.Gradual.MRO.Compute
import FwPython.Static.Subtyping.WellFormedTy
import FwPython.Gradual.Invariants

/-! # Valid gradual annotations

A valid gradual annotation uses known class names with valid MROs.
Type packages store this proof together with the annotation.
Their lower and upper bounds form validated static type packages.
Erasing method annotations preserves class lookup and MROs.
This supplies the hierarchy used to compare those bounds. -/

/-- A gradual type is well-formed under a gradual class table if every class
    name it mentions exists in the class table and has a valid MRO.
    `any` is always well-formed (it represents the unknown fully static type). -/
inductive WellFormedGTy : GClassTable → GTy → Prop where
  /-- The unknown annotation contains no class name. -/
  | any : WellFormedGTy gct .any
  /-- The empty type contains no class name. -/
  | bottom : WellFormedGTy gct .bottom
  /-- A named class has a declaration and a valid method resolution order. -/
  | class_ :
      findGClass gct cname = some c →
      GComputeMro gct c mro →
      WellFormedGTy gct (.class_ cname)
  /-- Both the function input and its result use valid annotations. -/
  | callable :
      WellFormedGTy gct P →
      WellFormedGTy gct R →
      WellFormedGTy gct (.callable P R)
  /-- Both alternatives of the union use valid annotations. -/
  | union :
      WellFormedGTy gct T →
      WellFormedGTy gct U →
      WellFormedGTy gct (.union T U)
  /-- Both parts of the intersection use valid annotations. -/
  | intersection :
      WellFormedGTy gct T →
      WellFormedGTy gct U →
      WellFormedGTy gct (.intersection T U)
  /-- The excluded class has a declaration and a valid method resolution order. -/
  | negClass :
      findGClass gct cname = some c →
      GComputeMro gct c mro →
      WellFormedGTy gct (.negClass cname)

/-- A gradual annotation with proof that its named classes and their MROs are valid. -/
structure WellFormedGradualType (table : GClassTable) where
  /-- The gradual type annotation represented by this package. -/
  raw : GTy
  /-- Proof that every named class exists and has a valid MRO in the table. -/
  wellFormed : WellFormedGTy table raw
  deriving DecidableEq

namespace WellFormedGradualType

/-- The unknown annotation contains no class names. -/
def any : WellFormedGradualType table := ⟨.any, .any⟩

/-- The empty annotation contains no class names. -/
def bottom : WellFormedGradualType table := ⟨.bottom, .bottom⟩

/-- A union of valid annotations is valid. -/
def union (left right : WellFormedGradualType table) : WellFormedGradualType table :=
  ⟨.union left.raw right.raw, .union left.wellFormed right.wellFormed⟩

/-- An intersection of valid annotations is valid. -/
def intersection (left right : WellFormedGradualType table) : WellFormedGradualType table :=
  ⟨.intersection left.raw right.raw, .intersection left.wellFormed right.wellFormed⟩

end WellFormedGradualType

/-! ## Type environment update helpers -/

theorem gTyEnv_update_lookup_eq
    {Γ : GTyEnv} {x : Identifier} (S : GTy)
    (hx : ∃ G, Γ.lookup x = some G) :
    (Γ.update x S).lookup x = some S :=
  namedEnv_update_lookup_eq S hx

theorem gTyEnv_update_lookup_ne
    {Γ : GTyEnv} {x y : Identifier} (S : GTy)
    (hne : y ≠ x) :
    (Γ.update x S).lookup y = Γ.lookup y :=
  namedEnv_update_lookup_ne S hne

open FwPython.Static.Subtyping

/-- Both bounds use only known class names.
Function inputs exchange the two bounds, so the proof establishes them together. -/
theorem WellFormedGTy.boundsNamesKnown
    (structural : WellFormedClassHierarchy (eraseClassTable gct))
    (valid : WellFormedGTy gct G) :
    WellFormedTy (eraseClassTable gct) (lowerBound G) ∧
    WellFormedTy (eraseClassTable gct) (upperBound G) := by
  induction valid with
  | any => exact ⟨.bottom, WellFormedTy.object structural⟩
  | bottom => exact ⟨.bottom, .bottom⟩
  | class_ lookup _ =>
      have valid := WellFormedTy.class_of_lookup (findClass_eraseClassTable lookup)
      exact ⟨valid, valid⟩
  | negClass lookup _ =>
      have valid := WellFormedTy.negClass_of_lookup (findClass_eraseClassTable lookup)
      exact ⟨valid, valid⟩
  | callable _ _ input result =>
      exact ⟨.callable input.2 result.1, .callable input.1 result.2⟩
  | union _ _ left right => exact ⟨.union left.1 right.1, .union left.2 right.2⟩
  | intersection _ _ left right =>
      exact ⟨.intersection left.1 right.1, .intersection left.2 right.2⟩

/-- The lower bound as a validated static type. -/
def lowerBoundType (structural : WellFormedClassHierarchy (eraseClassTable gct))
    (valid : WellFormedGTy gct G) : WellFormedType ((eraseClassTable gct).map ClassDecl.name) :=
  ⟨lowerBound G, (valid.boundsNamesKnown structural).1⟩

/-- The upper bound as a validated static type. -/
def upperBoundType (structural : WellFormedClassHierarchy (eraseClassTable gct))
    (valid : WellFormedGTy gct G) : WellFormedType ((eraseClassTable gct).map ClassDecl.name) :=
  ⟨upperBound G, (valid.boundsNamesKnown structural).2⟩

/-! ## Well-formed class-table bridge -/

/-- Erasure preserves the selected nominal hierarchy and builtin sealing evidence.
Erasure changes only method signatures, so lookup results, MROs, and sealing transfer unchanged. -/
def eraseClassTable_structural {gct : GClassTable}
    (wf : WellFormedGClassTable gct) : WellFormedClassHierarchy (eraseClassTable gct) :=
  let erase := fun cname (witness : GClassLookupWitness gct cname) =>
    (⟨eraseClass witness.cls, witness.mro, findClass_eraseClassTable witness.hfind,
      gComputeMro_eraseClassTable witness.hmro⟩ : ClassLookupWitness (eraseClassTable gct) cname)
  { objectExists := ⟨eraseClass wf.objectExists.cls, findClass_eraseClassTable wf.objectExists.hfind,
      by simpa [eraseClass] using wf.objectExists.hbases⟩
    boolExists := erase _ wf.boolExists
    noneExists := erase _ wf.noneExists
    boundMethodExists := erase _ wf.boundMethodExists
    allMrosExist := by
      intro cname c hfind
      cases hgc : findGClass gct cname with
      | none => simp [findClass_eraseClassTable_eq, hgc] at hfind
      | some gc =>
          have hErase : eraseClass gc = c := by simpa [findClass_eraseClassTable_eq, hgc] using hfind
          subst hErase
          exact ⟨(wf.allMrosExist cname gc hgc).mro, gComputeMro_eraseClassTable (wf.allMrosExist cname gc hgc).hmro⟩
    sealedLeaf := by
      intro builtin sealed cname c mro hfc hmro hmem
      obtain ⟨gc, hgc, rfl⟩ := findGClass_of_findClass_eraseClassTable hfc
      let gradualMro := (wf.allMrosExist cname gc hgc).hmro
      cases determinism (gComputeMro_eraseClassTable gradualMro) hmro
      simpa using wf.sealedLeaf builtin sealed cname gc _ hgc gradualMro hmem }

/-- Name validity of either bound establishes validity of the gradual annotation.
Neither bound drops a named atom, including atoms inside function inputs. -/
theorem wellFormedGTy_of_boundsNamesKnown (tableValid : WellFormedGClassTable gct) (G : GTy) :
    (WellFormedTy (eraseClassTable gct) (lowerBound G) →
      WellFormedGTy gct G) ∧
    (WellFormedTy (eraseClassTable gct) (upperBound G) →
      WellFormedGTy gct G) := by
  have selected (name : Identifier)
      (known : name ∈ (eraseClassTable gct).map ClassDecl.name) :
      ∃ declaration mro, findGClass gct name = some declaration ∧
        GComputeMro gct declaration mro := by
    let witness := (eraseClassTable_structural tableValid).lookupKnown name known
    obtain ⟨declaration, lookup, _⟩ := findGClass_of_findClass_eraseClassTable witness.hfind
    exact ⟨declaration, (tableValid.allMrosExist _ _ lookup).mro, lookup,
      (tableValid.allMrosExist _ _ lookup).hmro⟩
  induction G with
  | any => exact ⟨fun _ => .any, fun _ => .any⟩
  | bottom => exact ⟨fun _ => .bottom, fun _ => .bottom⟩
  | class_ name =>
      constructor <;> intro known <;> cases known with
      | class_ known =>
          obtain ⟨_, _, lookup, computed⟩ := selected name known
          exact .class_ lookup computed
  | negClass name =>
      constructor <;> intro known <;> cases known with
      | negClass known =>
          obtain ⟨_, _, lookup, computed⟩ := selected name known
          exact .negClass lookup computed
  | callable _ _ ihInput ihResult =>
      constructor <;> intro known <;> cases known with
      | callable inputKnown resultKnown =>
          first
          | exact .callable (ihInput.2 inputKnown) (ihResult.1 resultKnown)
          | exact .callable (ihInput.1 inputKnown) (ihResult.2 resultKnown)
  | union _ _ ihLeft ihRight =>
      constructor <;> intro known <;> cases known with
      | union leftKnown rightKnown =>
          first
          | exact .union (ihLeft.1 leftKnown) (ihRight.1 rightKnown)
          | exact .union (ihLeft.2 leftKnown) (ihRight.2 rightKnown)
  | intersection _ _ ihLeft ihRight =>
      constructor <;> intro known <;> cases known with
      | intersection leftKnown rightKnown =>
          first
          | exact .intersection (ihLeft.1 leftKnown) (ihRight.1 rightKnown)
          | exact .intersection (ihLeft.2 leftKnown) (ihRight.2 rightKnown)
