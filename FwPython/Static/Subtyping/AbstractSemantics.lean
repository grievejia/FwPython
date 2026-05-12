import FwPython.Static.Subtyping.Core
import FwPython.Static.Subtyping.Carrier

/-! ## Direct semantic subtyping

`SemSubtype` is plain denotation preservation over `SemObject`. The
class/exact/negative fragment is fully semantic. The callable branch keeps the
runtime method signature as stored subtype witnesses; the fully extensional
callable clause suggested by the design spike does not pass Lean's termination
checker because it would recurse on arbitrary runtime signature types. -/

/-- Semantic denotation over `SemObject`. -/
def Ty.semDenotes (ct : ClassTable) : Ty → SemObject ct → Prop
  | .class_ C, obj => obj.hasAncestor C
  | .negClass C, obj => ¬ obj.hasAncestor C
  | .callable P R, obj =>
      match obj with
      | .boundMethod bm =>
          IsSubtype ct P bm.actualParam ∧ IsSubtype ct bm.actualReturn R
      | _ => False
  | .union T U, obj => T.semDenotes ct obj ∨ U.semDenotes ct obj
  | .intersection T U, obj => T.semDenotes ct obj ∧ U.semDenotes ct obj
  | .bottom, _ => False

/-- Semantic subtyping is direct denotation preservation. -/
def SemSubtype (ct : ClassTable) (T U : Ty) : Prop :=
  ∀ obj, T.semDenotes ct obj → U.semDenotes ct obj

theorem SemSubtype.refl (T : Ty) : SemSubtype ct T T :=
  fun _ hden => hden

theorem SemSubtype.trans
    (hTU : SemSubtype ct T U) (hUV : SemSubtype ct U V) :
    SemSubtype ct T V :=
  fun obj hden => hUV obj (hTU obj hden)

theorem boundMethod_denotes_callable_self (bm : BoundMethodOrd ct) :
    Ty.semDenotes ct (.callable bm.actualParam bm.actualReturn) (.boundMethod bm) :=
  ⟨.refl, .refl⟩

theorem ordinaryCurrent_not_denotes_callable (cur : CurrentOrd ct) :
    ¬ Ty.semDenotes ct (.callable P R) (.ordinaryCurrent cur) := by simp [Ty.semDenotes]

theorem ordinaryFresh_not_denotes_callable (fr : FreshOrd ct) :
    ¬ Ty.semDenotes ct (.callable P R) (.ordinaryFresh fr) := by simp [Ty.semDenotes]

private theorem mro_eq_of_leaf_member
    {ct : ClassTable} {B cname : Identifier} {bcls cls : Class}
    {bmro mro : List Identifier}
    (hleaf : LeafBuiltin ct B)
    (hfindB : findClass ct B = some bcls)
    (hmroB : ComputeMro ct bcls bmro)
    (hfind : findClass ct cname = some cls)
    (hmro : ComputeMro ct cls mro)
    (hmem : B ∈ mro) :
    mro = bmro := by
  have hcname := LeafBuiltin.sealed hleaf _ _ _ hfind hmro hmem
  subst hcname
  rw [hfindB] at hfind
  cases hfind
  exact determinism hmro hmroB

theorem semSubtype_sound (hsub : IsSubtype ct T U) :
    SemSubtype ct T U := by
  intro obj hden
  induction hsub generalizing obj with
  | refl => exact hden
  | trans _ _ ihTU ihUV => exact ihUV _ (ihTU _ hden)
  | bottom => exact hden.elim
  | objectTop =>
      cases obj <;> rename_i o <;>
        simpa [Ty.semDenotes, SemObject.hasAncestor] using o.object_mem
  | interLeft _ ih => exact ih _ hden.1
  | interRight _ ih => exact ih _ hden.2
  | interIntro _ _ ihT ihU => exact ⟨ihT _ hden, ihU _ hden⟩
  | unionElim _ _ ihT ihU => exact hden.elim (ihT _) (ihU _)
  | unionLeft _ ih => exact Or.inl (ih _ hden)
  | unionRight _ ih => exact Or.inr (ih _ hden)
  | interUnionDistrib =>
      exact hden.2.elim (fun hU => Or.inl ⟨hden.1, hU⟩) (fun hV => Or.inr ⟨hden.1, hV⟩)
  | class_ hfind hmro hmem =>
      cases obj <;> rename_i o <;>
        simpa [Ty.semDenotes, SemObject.hasAncestor] using
          o.hasAncestor_closed hden hfind hmro hmem
  | callable hsubP hsubR _ _ =>
      cases obj with
      | ordinaryCurrent | ordinaryFresh => simp [Ty.semDenotes] at hden
      | boundMethod _ => exact ⟨.trans hsubP hden.1, .trans hden.2 hsubR⟩
  | callableBoundMethod _ _ =>
      cases obj with
      | ordinaryCurrent | ordinaryFresh => simp [Ty.semDenotes] at hden
      | boundMethod bm =>
          simpa [Ty.semDenotes, SemObject.hasAncestor, BoundMethodOrd.hasAncestor] using bm.self_mem
  | callableInterUnion =>
      cases obj with
      | ordinaryCurrent | ordinaryFresh => simp [Ty.semDenotes] at hden
      | boundMethod _ =>
          exact ⟨.unionElim hden.1.1 hden.2.1, .interIntro hden.1.2 hden.2.2⟩
  | @objectClassUnionNegClass C =>
      exact match (inferInstance : Decidable (obj.hasAncestor C)) with
        | isTrue hanc => Or.inl hanc
        | isFalse hanc => Or.inr hanc
  | @sealedClassNegClass B bcls bmro C hleaf hfindB hmroB hnotmem =>
      cases obj with
      | ordinaryFresh fr =>
          exact (fr.no_leaf_builtin_ancestor hleaf hden).elim
      | ordinaryCurrent cur =>
          have hmroEq := mro_eq_of_leaf_member hleaf hfindB hmroB cur.hfind cur.hmro hden
          simpa [Ty.semDenotes, SemObject.hasAncestor, CurrentOrd.hasAncestor, hmroEq] using hnotmem
      | boundMethod bm =>
          have hmroEq := mro_eq_of_leaf_member hleaf hfindB hmroB bm.hfind bm.hmro hden
          simpa [Ty.semDenotes, SemObject.hasAncestor, BoundMethodOrd.hasAncestor, hmroEq] using hnotmem
  | classSelfNegClassBottom => exact hden.2 hden.1

theorem semSubtype_denotes_subset (hsub : SemSubtype ct T U) :
    T.semDenotes ct obj → U.semDenotes ct obj :=
  hsub obj

theorem semDenotes_at_obj_sound (hsub : IsSubtype ct T U) :
    T.semDenotes ct obj → U.semDenotes ct obj :=
  semSubtype_denotes_subset (semSubtype_sound hsub)
