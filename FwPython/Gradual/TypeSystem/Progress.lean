import FwPython.Gradual.TypeSystem.Safety
import FwPython.Gradual.TypeSystem.Preservation
import FwPython.Gradual.Checked.Enforce
import FwPython.Gradual.Checked.Heap

/-! ## Progress for checked safe states

A safe non-final checked state can always take a step. Together with
preservation, this means well-typed checked programs never get stuck:
they either terminate normally, signal blame, or keep stepping. -/

variable {gct : GClassTable} {structural : WellFormedClassHierarchy (eraseClassTable gct)}

namespace Checked

/-! ### Helpers for progress -/

/-- A well-typed `isInstance` implies the variable is bound in the type env. -/
private theorem isInstance_extract_var_type
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G)
    (he : e = .isInstance x C) :
    ∃ T, Γ.lookup x = some T := by
  induction hty with
  | isInstance hlook _ => exact ⟨_, (CheckedExpr.isInstance.inj he).1 ▸ hlook⟩
  | _ => exact absurd he nofun

/-- A well-typed `cond (isInstance x C)` implies the variable is bound in the type env. -/
private theorem condIsInstance_extract_var_type
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G)
    (he : e = .cond (.isInstance x C) thenBr elseBr) :
    ∃ T, Γ.lookup x = some T := by
  induction hty with
  | condIsInstance hlook _ _ _ _ _ _ =>
    exact ⟨_, (CheckedExpr.isInstance.inj (CheckedExpr.cond.inj he).1).1 ▸ hlook⟩
  | cond hty_cond _ _ _ =>
    exact isInstance_extract_var_type hty_cond (CheckedExpr.cond.inj he).1
  | _ => exact absurd he nofun

/-- Progress: a safe state is either final or can take a step. -/
theorem checked_progress
    (hsafe : CheckedStateSafe gct cct heap env ctrl cont expectedType) :
    (∃ r, finalResult? { heap, env, control := ctrl, continuation := cont } = some r) ∨
    (∃ heap' env' ctrl' cont',
      Step gct cct { heap, env, control := ctrl, continuation := cont }
               { heap := heap', env := env', control := ctrl', continuation := cont' }) := by
  obtain ⟨Γ, outΓ, G, hwfct, hheap, halign, henv, hctrl, hcont⟩ := hsafe
  cases hctrl with
  | expr hty =>
    -- Expression: always has a step (focus or atomic).
    -- Case-split on the expression form.
    right
    -- Extract the expression from the state/control
    rename_i e
    cases e with
    | var x =>
      cases hlook : env.lookup x with
      | some v => exact ⟨_, _, _, _, .varSuccess hlook⟩
      | none => exact ⟨_, _, _, _, .varError hlook⟩
    | constNone => exact ⟨_, _, _, _, .constNone⟩
    | constTrue => exact ⟨_, _, _, _, .constTrue⟩
    | constFalse => exact ⟨_, _, _, _, .constFalse⟩
    | new cname =>
      cases hfind : findGClass gct cname with
      | none => exact ⟨_, _, _, _, .newClassNotFound hfind⟩
      | some c =>
        by_cases hb : cname = boolClass
        · exact ⟨_, _, _, _, .newBuiltinError hfind (.inl hb)⟩
        by_cases hn : cname = noneClass
        · exact ⟨_, _, _, _, .newBuiltinError hfind (.inr (.inl hn))⟩
        by_cases hbm : cname = boundMethodClass
        · exact ⟨_, _, _, _, .newBuiltinError hfind (.inr (.inr hbm))⟩
        exact ⟨_, _, _, _, .newSuccess hfind hb hn hbm rfl⟩
    | attrAccess _ _ => exact ⟨_, _, _, _, .focusAttrAccess⟩
    | call _ _ _ _ _ => exact ⟨_, _, _, _, .focusCall⟩
    | cond condExpr thenBr elseBr =>
      cases condExpr with
      | isInstance x C =>
        -- condIsInstance: need to check the variable and MRO
        cases hlookE : env.lookup x with
        | none => exact ⟨_, _, _, _, .condIsInstanceVarNotFound hlookE⟩
        | some v =>
          cases v with
          | objRef oid =>
            cases hlookH : heap.lookup oid with
            | none =>
              -- Contradiction: env typing gives a value with a type, which requires heap lookup
              obtain ⟨T, hlookΓ⟩ := condIsInstance_extract_var_type hty rfl
              obtain ⟨v', hvLook', hvalT⟩ := henv _ T hlookΓ
              obtain ⟨_, hlookObj⟩ := checkedValueWitness_objRef_lookup hvalT
                (Option.some.inj (hlookE.symm.trans hvLook')).symm
              cases hlookH.symm.trans hlookObj
            | some obj =>
              cases hfind : findGClass gct obj.className with
              | none =>
                obtain ⟨_, _, hfindC, _⟩ := hheap.classesExist _ _ hlookH
                simp [hfindC] at hfind
              | some c =>
                obtain ⟨_, mro, hfindC, hmro⟩ := hheap.classesExist _ _ hlookH
                obtain rfl := Option.some.inj (hfind.symm.trans hfindC)
                by_cases hmem : C ∈ mro
                · exact ⟨_, _, _, _, .condIsInstanceTrue hlookE hlookH hfind hmro hmem⟩
                · exact ⟨_, _, _, _, .condIsInstanceFalse hlookE hlookH hfind hmro hmem⟩
      | _ => exact ⟨_, _, _, _, .focusCond nofun⟩
    | isInstance x C =>
      cases hlookE : env.lookup x with
      | none => exact ⟨_, _, _, _, .isInstanceVarNotFound hlookE⟩
      | some v =>
        cases v with
        | objRef oid =>
          cases hlookH : heap.lookup oid with
          | none =>
            obtain ⟨T, hlookΓ⟩ := isInstance_extract_var_type hty rfl
            obtain ⟨v', hvLook', hvalT⟩ := henv _ T hlookΓ
            obtain ⟨_, hlookObj⟩ := checkedValueWitness_objRef_lookup hvalT
              (Option.some.inj (hlookE.symm.trans hvLook')).symm
            cases hlookH.symm.trans hlookObj
          | some obj =>
            cases hfind : findGClass gct obj.className with
            | none =>
              obtain ⟨_, _, hfindC, _⟩ := hheap.classesExist _ _ hlookH
              simp [hfindC] at hfind
            | some c =>
              obtain ⟨_, mro, hfindC, hmro⟩ := hheap.classesExist _ _ hlookH
              obtain rfl := Option.some.inj (hfind.symm.trans hfindC)
              by_cases hmem : C ∈ mro
              · exact ⟨_, _, _, _, .isInstanceTrue hlookE hlookH hfind hmro hmem⟩
              · exact ⟨_, _, _, _, .isInstanceFalse hlookE hlookH hfind hmro hmem⟩
    | enforce _ _ _ => exact ⟨_, _, _, _, .focusEnforce⟩
    | dynAttrAccess _ _ _ => exact ⟨_, _, _, _, .focusDynAttrAccess⟩
  | val hvty =>
    -- Value: final if continuation is empty, return rule otherwise
    rename_i v
    cases cont with
    | nil => exact .inl ⟨_, rfl⟩
    | cons f k =>
      right
      have hvshape := checkedValueWitness_toShape hvty
      have hvlook : ∀ oid, v = .objRef oid → ∃ obj, heap.lookup oid = some obj :=
        fun oid hv => checkedAnyShape_objRef_lookup hvshape hv
      cases f with
      | returnTo callerEnv =>
        exact ⟨_, _, _, _, .returnFromBody⟩
      | attrAccess attrName =>
        cases v with
        | objRef oid =>
          obtain ⟨obj, hlookH⟩ := hvlook _ rfl
          obtain ⟨c, mro, hfindC, hmro⟩ := hheap.classesExist _ _ hlookH
          cases hmeth : findCheckedMethodInMro cct mro attrName with
          | none => exact ⟨_, _, _, _, .returnAttrAccessNotFound hlookH hfindC hmro hmeth⟩
          | some cm => exact ⟨_, _, _, _, .returnAttrAccess hlookH hfindC hmro hmeth rfl⟩
      | dynAttrAccess attrName ℓ =>
        cases v with
        | objRef oid =>
          obtain ⟨obj, hlookH⟩ := hvlook _ rfl
          obtain ⟨c, mro, hfindC, hmro⟩ := hheap.classesExist _ _ hlookH
          cases hmeth : findCheckedMethodInMro cct mro attrName with
          | none => exact ⟨_, _, _, _, .returnDynAttrAccessNotFound hlookH hfindC hmro hmeth⟩
          | some cm => exact ⟨_, _, _, _, .returnDynAttrAccess hlookH hfindC hmro hmeth rfl⟩
      | callCallee arg paramTy returnTy returnObligation =>
        cases hcont with | cons hf hk =>
        cases hf with | callCallee _ _ _ _ _ _ =>
        match checkedValueWitness_callable_view hvty with
        | .objRefBoundMethod hlook _ _ => exact ⟨_, _, _, _, .returnCallCalleeBound hlook⟩
      | awaitArgument recvOid m returnTy returnObligation =>
        rcases enforceValue_total hheap (compileBoundaryTarget m.paramTy) v hvlook with
          henf | henf
        · exact ⟨_, _, _, _, .returnAwaitArgumentOk henf⟩
        · exact ⟨_, _, _, _, .returnAwaitArgumentBlame henf⟩
      | cond thenBr elseBr =>
        cases v with
        | objRef oid =>
          by_cases htrue : oid = trueOid
          · subst htrue; exact ⟨_, _, _, _, .returnCondTrue⟩
          by_cases hfalse : oid = falseOid
          · subst hfalse; exact ⟨_, _, _, _, .returnCondFalse⟩
          exact ⟨_, _, _, _, .returnCondNotBool htrue hfalse⟩
      | enforce c ℓ =>
        rcases enforceValue_total hheap (compileBoundaryTarget c) v hvlook with
          henf | henf
        · exact ⟨_, _, _, _, .returnEnforceOk henf⟩
        · exact ⟨_, _, _, _, .returnEnforceBlame henf⟩
  | blame =>
    -- Blame: final if continuation is empty, propagation otherwise
    cases cont with
    | nil => exact .inl ⟨_, rfl⟩
    | cons f k =>
      -- Blame propagation exists for each frame type
      right
      cases f with
      | attrAccess => exact ⟨_, _, _, _, .blameUnwindAttrAccess⟩
      | callCallee _ _ _ _ => exact ⟨_, _, _, _, .blameUnwindCallCallee⟩
      | awaitArgument _ _ _ _ => exact ⟨_, _, _, _, .blameUnwindAwaitArgument⟩
      | cond => exact ⟨_, _, _, _, .blameUnwindCond⟩
      | returnTo => exact ⟨_, _, _, _, .blameUnwindReturnTo⟩
      | enforce => exact ⟨_, _, _, _, .blameUnwindEnforce⟩
      | dynAttrAccess => exact ⟨_, _, _, _, .blameUnwindDynAttrAccess⟩

end Checked
