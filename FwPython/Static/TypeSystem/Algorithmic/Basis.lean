import FwPython.Static.TypeSystem.TypingLemmas

/-! ## Intersection closure for inferred types

`HasType.interIntro` combines two typings of the same expression, so a finite
inference basis must also cover their intersection. Closing valid candidate
packages under nonempty intersection supplies these cases while preserving
name validity. The checker can then pass each candidate's proof directly to
`WellFormedType.subtypeDecidable`, and completeness proves that the resulting
list contains a package below each declarative result type.
-/

variable {ct : ClassTable} {structural : WellFormedClassHierarchy ct}

open FwPython.Static.Subtyping

/-- Include each valid candidate and every nonempty intersection of candidates. -/
private def saturateIntersections : List (WellFormedType names) → List (WellFormedType names)
  | [] => []
  | head :: rest =>
      let saturated := saturateIntersections rest
      head :: saturated.map (WellFormedType.intersection head) ++ saturated

/-- A package in the closure is the head, an intersection with the head, or a tail member. -/
private theorem mem_saturateIntersections_cons :
    U ∈ saturateIntersections (head :: rest) ↔
      U = head ∨ (∃ V, V ∈ saturateIntersections rest ∧
        U = WellFormedType.intersection head V) ∨
      U ∈ saturateIntersections rest := by
  simp [saturateIntersections, eq_comm]

/-- A closure member is the first candidate, an intersection with it,
or a type built from later candidates. -/
private inductive ConsSlot (head : WellFormedType names) (rest : List (WellFormedType names)) : WellFormedType names → Prop where
  /-- The first candidate itself. -/
  | isHead : ConsSlot head rest head
  /-- The first candidate intersected with a requirement from the remaining candidates. -/
  | withHead (V : WellFormedType names) (hV : V ∈ saturateIntersections rest) :
      ConsSlot head rest (WellFormedType.intersection head V)
  /-- A requirement formed entirely from the remaining candidates. -/
  | fromRest (V : WellFormedType names) (hV : V ∈ saturateIntersections rest) : ConsSlot head rest V

/-- Classify a closure member by whether it includes the first candidate. -/
private theorem consSlot_of_mem
    (hmem : U ∈ saturateIntersections (head :: rest)) : ConsSlot head rest U := by
  rcases mem_saturateIntersections_cons.mp hmem with rfl | ⟨V, hV, rfl⟩ | hmem
  · exact .isHead
  · exact .withHead V hV
  · exact .fromRest U hmem

/-- Each classified candidate belongs to the intersection closure. -/
private theorem mem_of_consSlot
    (h : ConsSlot head rest U) : U ∈ saturateIntersections (head :: rest) := by
  cases h with
  | isHead => simp [saturateIntersections]
  | withHead V hV => exact mem_saturateIntersections_cons.mpr (Or.inr (Or.inl ⟨V, hV, rfl⟩))
  | fromRest _ hV => exact mem_saturateIntersections_cons.mpr (Or.inr (Or.inr hV))

/-- The package closure contains a type below the intersection of any two members. -/
private theorem saturateIntersections_intersection_cover
    {B : List (WellFormedType (ct.map ClassDecl.name))}
    {S T : WellFormedType (ct.map ClassDecl.name)}
    (hS : S ∈ saturateIntersections B)
    (hT : T ∈ saturateIntersections B) :
    ∃ U, U ∈ saturateIntersections B ∧
      IsSubtype structural U.raw (.intersection S.raw T.raw) := by
  induction B generalizing S T with
  | nil => cases hS
  | cons head rest ih =>
      have headValid := head.namesKnown
      have headRefl : IsSubtype structural head.raw head.raw := .refl headValid
      cases consSlot_of_mem hS with
      | isHead =>
          cases consSlot_of_mem hT with
          | isHead => exact ⟨head, by simp [saturateIntersections], .interIntro headRefl headRefl⟩
          | withHead T' hT' =>
              have validT := T'.namesKnown
              exact ⟨WellFormedType.intersection head T', mem_of_consSlot (.withHead T' hT'),
                .interIntro (.interLeft headRefl validT) (.refl (.intersection headValid validT))⟩
          | fromRest _ hT' =>
              have validT := T.namesKnown
              exact ⟨WellFormedType.intersection head T, mem_of_consSlot (.withHead T hT'),
                .interMono headRefl (.refl validT)⟩
      | withHead S' hS' =>
          cases consSlot_of_mem hT with
          | isHead =>
              have validS := S'.namesKnown
              exact ⟨WellFormedType.intersection head S', mem_of_consSlot (.withHead S' hS'),
                .interIntro (.refl (.intersection headValid validS)) (.interLeft headRefl validS)⟩
          | withHead T' hT' =>
              obtain ⟨U', hU', hsub'⟩ := ih hS' hT'
              obtain ⟨toS, toT⟩ := subtype_inter_iff.mp hsub'
              exact ⟨WellFormedType.intersection head U', mem_of_consSlot (.withHead U' hU'),
                .interIntro
                  (.interMono headRefl toS)
                  (.interMono headRefl toT)⟩
          | fromRest T' hT' =>
              obtain ⟨U', hU', hsub'⟩ := ih hS' hT'
              obtain ⟨toS, toT⟩ := subtype_inter_iff.mp hsub'
              exact ⟨WellFormedType.intersection head U', mem_of_consSlot (.withHead U' hU'),
                .interIntro
                  (.interMono headRefl toS)
                  (.interRight toT headValid)⟩
      | fromRest _ hS' =>
          cases consSlot_of_mem hT with
          | isHead =>
              have validS := S.namesKnown
              exact ⟨WellFormedType.intersection head S, mem_of_consSlot (.withHead S hS'),
                .interIntro (.interRight (.refl validS) headValid) (.interLeft headRefl validS)⟩
          | withHead T' hT' =>
              obtain ⟨U', hU', hsub'⟩ := ih hS' hT'
              obtain ⟨toS, toT⟩ := subtype_inter_iff.mp hsub'
              exact ⟨WellFormedType.intersection head U', mem_of_consSlot (.withHead U' hU'),
                .interIntro (.interRight toS headValid)
                  (.interMono headRefl toT)⟩
          | fromRest T' hT' =>
              obtain ⟨U', hU', hsub'⟩ := ih hS' hT'
              exact ⟨U', mem_of_consSlot (.fromRest U' hU'), hsub'⟩

/-- Valid candidate types and their expression typing proofs.
Intersection closure supplies the additional types needed by `HasType.interIntro`. -/
structure InferredBasis {ct : ClassTable} (structural : WellFormedClassHierarchy ct)
    (Γ : TyEnv) (e : Expr) where
  /-- Valid types computed for this expression before intersection closure. -/
  candidates : List (WellFormedType (ct.map ClassDecl.name))
  /-- The expression has the raw annotation of each candidate. -/
  sound : ∀ type ∈ candidates, HasType structural Γ e type.raw

namespace InferredBasis

/-- Valid candidates closed under nonempty intersection. -/
def types (basis : InferredBasis structural Γ e) : List (WellFormedType (ct.map ClassDecl.name)) :=
  saturateIntersections basis.candidates

/-- A single candidate is already closed under nonempty intersection. -/
@[simp] theorem types_singleton (type : WellFormedType (ct.map ClassDecl.name))
    (sound : ∀ candidate ∈ [type], HasType structural Γ e candidate.raw) :
    (InferredBasis.mk [type] sound).types = [type] := rfl

/-- Each packaged candidate is a declarative type of the expression. -/
theorem types_sound (basis : InferredBasis structural Γ e)
    (member : type ∈ basis.types) : HasType structural Γ e type.raw := by
  have closureSound (candidates : List (WellFormedType (ct.map ClassDecl.name)))
      (sound : ∀ candidate ∈ candidates, HasType structural Γ e candidate.raw) :
      ∀ candidate ∈ saturateIntersections candidates, HasType structural Γ e candidate.raw := by
    induction candidates with
    | nil => intro candidate member; cases member
    | cons head rest ih =>
        intro candidate member
        have headSound := sound head (.head _)
        have restSound := ih (fun candidate member => sound candidate (.tail _ member))
        rcases mem_saturateIntersections_cons.mp member with rfl | ⟨other, listed, rfl⟩ | listed
        · exact headSound
        · exact .interIntro headSound (restSound other listed)
        · exact restSound candidate listed
  exact closureSound basis.candidates basis.sound type member

/-- Every original candidate occurs in the intersection closure. -/
theorem candidate_member (basis : InferredBasis structural Γ e)
    (member : type ∈ basis.candidates) : type ∈ basis.types := by
  have included (candidates : List (WellFormedType (ct.map ClassDecl.name))) :
      ∀ candidate ∈ candidates, candidate ∈ saturateIntersections candidates := by
    induction candidates with
    | nil => intro candidate member; cases member
    | cons head rest ih =>
        intro candidate member
        rcases List.mem_cons.mp member with rfl | listed
        · exact mem_saturateIntersections_cons.mpr (Or.inl rfl)
        · exact mem_saturateIntersections_cons.mpr (Or.inr (Or.inr (ih candidate listed)))
  exact included basis.candidates type member

/-- Any two candidate packages have an intersection covered by a candidate package. -/
theorem intersection_cover (basis : InferredBasis structural Γ e)
    (left : S ∈ basis.types) (right : T ∈ basis.types) :
    ∃ U, U ∈ basis.types ∧ IsSubtype structural U.raw (.intersection S.raw T.raw) :=
  saturateIntersections_intersection_cover left right

end InferredBasis
