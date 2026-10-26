import FwPython.Static.Semantics.StateTyping
import FwPython.Static.TypeSystem.TypingLemmas
import FwPython.Static.TypeSystem.WellFormedness

/-! # Progress for Safe States

A safe non-final state can always take a step. -/

variable {ct : ClassTable}

namespace SmallStep

/-- Progress for a value + frame: the frame determines what step to take, regardless
    of how the frame's output type is wrapped by `sub` or `interIntro`. -/
private theorem progress_val_frame
    (hwf : WellTypedClassHierarchy ct)
    (hheap : HeapWellFormed ct heap)
    (hval : ValueHasType hwf.toWellFormedClassHierarchy heap v T)
    (hframe : FrameHasType hwf.toWellFormedClassHierarchy heap Γ T Γ' outTy f) :
    ∃ s', Step ct { heap, env, control := .val v, continuation := f :: k } s' := by
  induction hframe generalizing v with
  | attrAccess hfmt _ =>
    obtain ⟨oid, obj, hveq, hlookObj⟩ := canonical_class hval
    subst hveq
    obtain ⟨c, mro, hfindC, hmroC⟩ := hheap.classesExist _ _ hlookObj
    have hclsSub := objRef_class_subtype hwf hheap hval hlookObj hfindC hmroC
    obtain ⟨m, hmethodFound⟩ := typed_method_exists_on_runtime_receiver hwf
      hfmt hclsSub hfindC hmroC
    exact ⟨_, .returnAttrAccess hlookObj hfindC hmroC hmethodFound rfl⟩
  | attrAccessUnion hfmt1 hfmt2 _ =>
    obtain ⟨obj, hlookObj⟩ := objRef_has_heap_entry hval
    obtain ⟨c, mro, hfindC, hmroC⟩ := hheap.classesExist _ _ hlookObj
    have hclsDisj := objRef_union_class_decompose hwf hheap hval hlookObj hfindC hmroC
    rcases hclsDisj with hclsSub | hclsSub
    · obtain ⟨m, hmethodFound⟩ := typed_method_exists_on_runtime_receiver hwf
        hfmt1 hclsSub hfindC hmroC
      exact ⟨_, .returnAttrAccess hlookObj hfindC hmroC hmethodFound rfl⟩
    · obtain ⟨m, hmethodFound⟩ := typed_method_exists_on_runtime_receiver hwf
        hfmt2 hclsSub hfindC hmroC
      exact ⟨_, .returnAttrAccess hlookObj hfindC hmroC hmethodFound rfl⟩
  | callCallee _ _ =>
    obtain ⟨_, _, _, _, hveq, hlookCallee, _, _⟩ :=
      canonical_callable hwf hheap hval
    subst hveq
    exact ⟨_, .returnCallCallee hlookCallee⟩
  | awaitArgument _ _ _ =>
    exact ⟨_, .returnAwaitArgument⟩
  | cond _ _ _ =>
    obtain ⟨oid, obj, hveq, hlookObj⟩ := canonical_class hval
    subst hveq
    obtain ⟨c, mro, hfindC, hmroC⟩ := hheap.classesExist _ _ hlookObj
    have hclsSub := objRef_class_subtype hwf hheap hval hlookObj hfindC hmroC
    have hIsBool := bool_subtype_is_bool hwf hclsSub hfindC hmroC
    rcases hheap.boolExhaustive oid obj hlookObj hIsBool with rfl | rfl
    · exact ⟨_, .returnCondTrue⟩
    · exact ⟨_, .returnCondFalse⟩
  | returnTo _ =>
    exact ⟨_, .returnFromBody⟩
  | sub _ _ ih =>
    exact ih hval
  | interIntro _ _ hwfIn1 hwfIn2 ih1 _ =>
    exact ih1 (.sub hval (.interLeft (.refl hwfIn1) hwfIn2))

/-- Progress: every safe non-final state can take a step. -/
theorem progress
    (hwf : WellTypedClassHierarchy ct)
    (hsafe : StateSafe hwf.toWellFormedClassHierarchy heap env ctrl cont expectedType)
    (hnonfinal : finalResult? { heap, env, control := ctrl, continuation := cont } = none) :
    ∃ s', Step ct { heap, env, control := ctrl, continuation := cont } s' := by
  obtain ⟨Γ, outΓ, T, hheap, henv, hctrl, hcont⟩ := hsafe
  cases hctrl with
  | expr htype =>
    -- An expression can always be stepped (search rule or atomic rule)
    -- Case split on the expression
    rename_i e
    cases e with
    | attrAccess base attrName =>
      exact ⟨_, .focusAttrAccess⟩
    | call callee arg =>
      exact ⟨_, .focusCall⟩
    | cond condExpr thenBr elseBr =>
      cases condExpr with
      | isInstance x C =>
        -- isInstance conditions are handled by direct step rules
        cases hv : env.lookup x with
        | none => exact ⟨_, .condIsInstanceVarNotFound hv⟩
        | some v =>
          obtain ⟨oid⟩ := v
          obtain ⟨S, cls, hlookΓ, _⟩ := has_type_cond_isInstance_inv htype
          obtain ⟨v', henvLook, hvalTy⟩ := henv x S hlookΓ
          rw [hv] at henvLook; cases henvLook
          obtain ⟨obj, hlookHeap⟩ := objRef_has_heap_entry hvalTy
          obtain ⟨c, mro, hfind, hmro⟩ := hheap.classesExist _ _ hlookHeap
          by_cases hmem : C ∈ mro
          · exact ⟨_, .condIsInstanceTrue hv hlookHeap hfind hmro hmem⟩
          · exact ⟨_, .condIsInstanceFalse hv hlookHeap hfind hmro hmem⟩
      | _ => exact ⟨_, .focusCond (by intro x C; exact Expr.noConfusion)⟩
    | constNone =>
      exact ⟨_, .constNone⟩
    | constTrue =>
      exact ⟨_, .constTrue⟩
    | constFalse =>
      exact ⟨_, .constFalse⟩
    | var x =>
      cases hv : env.lookup x with
      | some v => exact ⟨_, .varSuccess hv⟩
      | none => exact ⟨_, .varError hv⟩
    | new cname =>
      cases hfc : findClass ct cname with
      | none => exact ⟨_, .newClassNotFound hfc⟩
      | some c =>
        by_cases hbool : cname = boolClass
        · exact ⟨_, .newBuiltinError hfc (.inl hbool)⟩
        · by_cases hnone : cname = noneClass
          · exact ⟨_, .newBuiltinError hfc (.inr (.inl hnone))⟩
          · by_cases hbm : cname = boundMethodClass
            · exact ⟨_, .newBuiltinError hfc (.inr (.inr hbm))⟩
            · exact ⟨_, .newSuccess hfc hbool hnone hbm rfl⟩
    | isInstance varName targetClass =>
      -- Need typing to show the variable is bound in env
      obtain ⟨⟨T', hlookΓ⟩, ⟨_, _⟩, _⟩ := has_type_isInstance_inv htype
      obtain ⟨v, henvLook, hvalTy⟩ := henv varName T' hlookΓ
      -- v must be .objRef oid since Value only has one constructor
      obtain ⟨oid⟩ := v
      obtain ⟨obj, hlookHeap⟩ := objRef_has_heap_entry hvalTy
      obtain ⟨c, mro, hfind, hmro⟩ := hheap.classesExist _ _ hlookHeap
      by_cases hmem : targetClass ∈ mro
      · exact ⟨_, .isInstanceTrue henvLook hlookHeap hfind hmro hmem⟩
      · exact ⟨_, .isInstanceFalse henvLook hlookHeap hfind hmro hmem⟩
  | val hval =>
    cases hcont with
    | nil => simp [finalResult?] at hnonfinal
    | cons hframe hrest =>
      exact progress_val_frame hwf hheap hval hframe

end SmallStep
