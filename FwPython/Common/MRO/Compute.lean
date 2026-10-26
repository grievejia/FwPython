import FwPython.Common.MRO.Core

namespace Common.MRO

/-! # Executable MRO Search

Fuel-bounded executable C3 MRO computation, parameterized over the class-table
method payload. Completeness bounds that depend on language-specific
well-formedness invariants live with those instantiations. -/

mutual
/-- Fuel-bounded executable MRO computation for a single class name. -/
def computeMroFuel? {Method : Type} :
    ClassTableDecl Method → Nat → Identifier → Option (List Identifier)
  | _, 0, _ => none
  | ct, fuel + 1, cname =>
      match findClass ct cname with
      | none => none
      | some cls =>
          match cls.resolvedBases with
          | [] => some [cls.name]
          | b :: rest =>
              let bases := b :: rest
              match computeAllParentMrosFuel? ct fuel bases with
              | none => none
              | some parentMros =>
                  match c3Merge (parentMros ++ [bases]) with
                  | none => none
                  | some mergedSuffix => some (cls.name :: mergedSuffix)
termination_by _ct fuel _cname => (fuel, 0)

/-- Fuel-bounded executable MRO computation for every direct base. -/
def computeAllParentMrosFuel? {Method : Type} :
    ClassTableDecl Method → Nat → List Identifier → Option (List (List Identifier))
  | _, _, [] => some []
  | ct, fuel, bname :: rest =>
      match computeMroFuel? ct fuel bname, computeAllParentMrosFuel? ct fuel rest with
      | some mro, some restMros => some (mro :: restMros)
      | _, _ => none
termination_by _ct fuel bases => (fuel, bases.length.succ)
end

/-- The executable MRO search uses table length as global fuel. -/
def computeMro? {Method : Type} (ct : ClassTableDecl Method)
    (cname : Identifier) : Option (List Identifier) :=
  computeMroFuel? ct ct.length cname

/-- The executable parent-MRO search uses table length as global fuel. -/
def computeAllParentMros? {Method : Type} (ct : ClassTableDecl Method)
    (bases : List Identifier) : Option (List (List Identifier)) :=
  computeAllParentMrosFuel? ct ct.length bases

private theorem computeMroFuel_sound_pair {Method : Type}
    (ct : ClassTableDecl Method) :
    ∀ fuel,
      (∀ cname mro,
        computeMroFuel? ct fuel cname = some mro →
          ∃ cls, findClass ct cname = some cls ∧ ComputeMro ct cls mro) ∧
      (∀ bases parentMros,
        computeAllParentMrosFuel? ct fuel bases = some parentMros →
          AllParentMros ct bases parentMros)
  | 0 =>
      ⟨
        by
          intro cname mro hcomp
          simp [computeMroFuel?] at hcomp,
        by
          intro bases parentMros hcomp
          induction bases generalizing parentMros with
          | nil =>
              simp [computeAllParentMrosFuel?] at hcomp
              cases hcomp
              exact .nil
          | cons b rest ih =>
              simp [computeAllParentMrosFuel?, computeMroFuel?] at hcomp
      ⟩
  | fuel + 1 =>
      let ⟨ihMro, ihParents⟩ := computeMroFuel_sound_pair ct fuel
      let hMro :
          ∀ cname mro,
            computeMroFuel? ct (fuel + 1) cname = some mro →
              ∃ cls, findClass ct cname = some cls ∧ ComputeMro ct cls mro := by
        intro cname mro hcomp
        simp [computeMroFuel?] at hcomp
        cases hfind : findClass ct cname with
        | none =>
            simp [hfind] at hcomp
        | some cls =>
            cases hbases : cls.resolvedBases with
            | nil =>
                simp [hfind, hbases] at hcomp
                cases hcomp
                exact ⟨cls, rfl, .root hbases⟩
            | cons b rest =>
                cases hparents : computeAllParentMrosFuel? ct fuel (b :: rest) with
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
            computeAllParentMrosFuel? ct (fuel + 1) bases = some parentMros →
              AllParentMros ct bases parentMros := by
        intro bases parentMros hcomp
        induction bases generalizing parentMros with
        | nil =>
            simp [computeAllParentMrosFuel?] at hcomp
            cases hcomp
            exact .nil
        | cons b rest ih =>
            simp [computeAllParentMrosFuel?] at hcomp
            cases hmro : computeMroFuel? ct (fuel + 1) b with
            | none =>
                simp [hmro] at hcomp
            | some mro =>
                cases hrest : computeAllParentMrosFuel? ct (fuel + 1) rest with
                | none =>
                    simp [hmro, hrest] at hcomp
                | some restMros =>
                    simp [hmro, hrest] at hcomp
                    cases hcomp
                    obtain ⟨bcls, hfind, hmro'⟩ := hMro _ _ hmro
                    exact .cons hfind hmro' (ih _ hrest)
      ⟨hMro, hParents⟩

theorem computeMroFuel?_sound {Method : Type}
    {ct : ClassTableDecl Method}
    (hcomp : computeMroFuel? ct fuel cname = some mro) :
    ∃ cls, findClass ct cname = some cls ∧ ComputeMro ct cls mro :=
  (computeMroFuel_sound_pair ct fuel).1 _ _ hcomp

theorem computeAllParentMrosFuel?_sound {Method : Type}
    {ct : ClassTableDecl Method}
    (hcomp : computeAllParentMrosFuel? ct fuel bases = some parentMros) :
    AllParentMros ct bases parentMros :=
  (computeMroFuel_sound_pair ct fuel).2 _ _ hcomp

theorem computeMro?_sound {Method : Type}
    {ct : ClassTableDecl Method}
    (hcomp : computeMro? ct cname = some mro) :
    ∃ cls, findClass ct cname = some cls ∧ ComputeMro ct cls mro :=
  computeMroFuel?_sound hcomp

theorem computeAllParentMros?_sound {Method : Type}
    {ct : ClassTableDecl Method}
    (hcomp : computeAllParentMros? ct bases = some parentMros) :
    AllParentMros ct bases parentMros :=
  computeAllParentMrosFuel?_sound hcomp

end Common.MRO
