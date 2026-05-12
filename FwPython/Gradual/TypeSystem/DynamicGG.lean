import FwPython.Gradual.TypeSystem.RuntimePrecision
import FwPython.Gradual.TypeSystem.InitializationAlignment
import FwPython.Gradual.TypeSystem.BoundaryCast
import FwPython.Gradual.TypeSystem.Blame.Correctness
import FwPython.Gradual.Checked.Determinism

/-! ## Dynamic gradual guarantee scaffolding -/

namespace Checked

private theorem enforce_exists_under_precision
    (hct : ClassTableAnnotationPrecision gct₁ gct₂)
    (hheapwf₂ : CheckedHeapWellFormed gct₂ cct₂ heap₂)
    (hwfct₂ : WellFormedGClassTableCore gct₂)
    (halign₂ : AlignedCheckedClassTable gct₂ cct₂)
    (hval : CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ v₁ v₂)
    (w₁ : CheckedValueWitness gct₁ cct₁ heap₁ v₁ (interpTarget T₁))
    (htarget₂ : RuntimePublicCheckedTarget gct₂ T₂)
    (hwf₂ : WellFormedGTy gct₂ (interpTarget T₂))
    (hprec : CompileTargetPrecision T₁ T₂)
    (labels₂ : BoundaryLabels (compileBoundaryTarget T₂)) :
    EnforceValue gct₂ heap₂ v₂ (compileBoundaryTarget T₂) labels₂ (.ok v₂) := by
  have w₂ :=
    checkedValuePrecision_transport_compileTarget
      hct
      hheapwf₂
      hval
      w₁
      hprec
      hwf₂
  exact
    (checkedValueWitness_same_checkedTarget
      (labels := labels₂)
      w₂
      htarget₂
      hheapwf₂
      hwfct₂
      halign₂).1

inductive SimulationSegmentResult
    (gct₁ gct₂ : GClassTable)
    (cct₁ cct₂ : CheckedClassTable)
    (expectedType₁ expectedType₂ : GTy)
    (s₁ s₂ : State) : Prop where
  | continue :
      (hstep₁ : Step gct₁ cct₁ s₁ s₁') →
      (hpref₂ : Steps gct₂ cct₂ s₂ s₂') →
      (hsafe₁' : CheckedStateSafe gct₁ cct₁
        s₁'.heap s₁'.env s₁'.control s₁'.continuation expectedType₁) →
      (hsafe₂' : CheckedStateSafe gct₂ cct₂
        s₂'.heap s₂'.env s₂'.control s₂'.continuation expectedType₂) →
      (hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂') →
      (hleftProgress : s₁' ≠ s₁) →
      SimulationSegmentResult gct₁ gct₂ cct₁ cct₂ expectedType₁ expectedType₂ s₁ s₂
  | leftBlame :
      (hstep₁ : Step gct₁ cct₁ s₁ s₁') →
      (hctrl₁' : s₁'.control = .blame ℓ) →
      (hpref₂ : Steps gct₂ cct₂ s₂ s₂) →
      (hsafe₂ : CheckedStateSafe gct₂ cct₂
        s₂.heap s₂.env s₂.control s₂.continuation expectedType₂) →
      (hleftProgress : s₁' ≠ s₁) →
      SimulationSegmentResult gct₁ gct₂ cct₁ cct₂ expectedType₁ expectedType₂ s₁ s₂

inductive ElaboratedSimulationSegmentResult
    {gp₁ gp₂ : GProgram}
    {P₁ P₂ : GTy}
    {cp₁ cp₂ : CheckedProgram}
    (helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁)
    (helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂)
    (expectedType₁ expectedType₂ : GTy)
    (s₁ s₂ : State) : Prop where
  | continue :
      (hstep₁ : Step gp₁.classes cp₁.classes s₁ s₁') →
      (hpref₂ : Steps gp₂.classes cp₂.classes s₂ s₂') →
      (hsafe₁' : CheckedStateSafe gp₁.classes cp₁.classes
        s₁'.heap s₁'.env s₁'.control s₁'.continuation expectedType₁) →
      (hsafe₂' : CheckedStateSafe gp₂.classes cp₂.classes
        s₂'.heap s₂'.env s₂'.control s₂'.continuation expectedType₂) →
      (hprec' : ElaboratedStatePrecision helab₁ helab₂ s₁' s₂') →
      (hleftProgress : s₁' ≠ s₁) →
      ElaboratedSimulationSegmentResult helab₁ helab₂ expectedType₁ expectedType₂ s₁ s₂
  | leftBlame :
      (hstep₁ : Step gp₁.classes cp₁.classes s₁ s₁') →
      (hctrl₁' : s₁'.control = .blame ℓ) →
      (hpref₂ : Steps gp₂.classes cp₂.classes s₂ s₂) →
      (hsafe₂ : CheckedStateSafe gp₂.classes cp₂.classes
        s₂.heap s₂.env s₂.control s₂.continuation expectedType₂) →
      (hleftProgress : s₁' ≠ s₁) →
      ElaboratedSimulationSegmentResult helab₁ helab₂ expectedType₁ expectedType₂ s₁ s₂

theorem blame_unwind_safe_step
    (_hct : ClassTableAnnotationPrecision gct₁ gct₂)
    (_hccShape : Forall₂ (ShapeClassPrecision gct₁)
      (cct₁.map eraseLabelsClass)
      (cct₂.map eraseLabelsClass))
    (hsafe₁ : CheckedStateSafe gct₁ cct₁ s₁.heap s₁.env s₁.control s₁.continuation expectedType₁)
    (hsafe₂ : CheckedStateSafe gct₂ cct₂ s₂.heap s₂.env s₂.control s₂.continuation expectedType₂)
    (hprec : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁ s₂)
    (hctrl₁ : s₁.control = .blame ℓ)
    (hnotFinal₁ : finalResult? s₁ = none) :
    SimulationSegmentResult gct₁ gct₂ cct₁ cct₂ expectedType₁ expectedType₂ s₁ s₂ := by
  cases s₁ with
  | mk heap₁ env₁ ctrl₁ cont₁ =>
      simp at hctrl₁
      subst ctrl₁
      cases cont₁ with
      | nil => simp [finalResult?] at hnotFinal₁
      | cons frame k =>
          cases frame with
          | attrAccess _ =>
              exact .leftBlame .blameUnwindAttrAccess rfl .refl hsafe₂ nofun
          | callCallee _ _ _ _ =>
              exact .leftBlame .blameUnwindCallCallee rfl .refl hsafe₂ nofun
          | awaitArgument _ _ _ _ =>
              exact .leftBlame .blameUnwindAwaitArgument rfl .refl hsafe₂ nofun
          | callValue _ _ _ _ =>
              exact .leftBlame .blameUnwindCallValue rfl .refl hsafe₂ nofun
          | cond _ _ =>
              exact .leftBlame .blameUnwindCond rfl .refl hsafe₂ nofun
          | returnTo _ =>
              exact .leftBlame .blameUnwindReturnTo rfl .refl hsafe₂ nofun
          | enforce _ _ =>
              exact .leftBlame .blameUnwindEnforce rfl .refl hsafe₂ nofun
          | dynAttrAccess _ _ =>
              exact .leftBlame .blameUnwindDynAttrAccess rfl .refl hsafe₂ nofun

/-- Factor a deterministic execution through a prefix that starts at the same
    state and whose endpoint is on the unique path to a final state. -/
def steps_factor_prefix
    (hpref : Steps ct cct s₁ s₂)
    (hsteps : Steps ct cct s₁ s₃)
    (hfinal : finalResult? s₃ = some out) :
    Steps ct cct s₂ s₃ := by
  induction hpref generalizing s₃ out with
  | refl =>
      exact hsteps
  | step hs hpref ih =>
      cases hsteps with
      | refl =>
          exact (final_states_do_not_step hfinal hs).elim
      | step hs' hrest =>
          cases step_deterministic hs hs'
          exact ih hrest hfinal

theorem steps_split_via_determinism
    (hpref : Steps ct cct s₁ s₂)
    (hsteps : Steps ct cct s₁ s₃)
    (hfinal : finalResult? s₃ = some out) :
    Steps ct cct s₂ s₃ :=
  steps_factor_prefix hpref hsteps hfinal

private theorem checkedEnvPrecision_lookup_left
    (henv : CheckedEnvPrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ env₁ env₂) :
    ∀ {x v₁},
      env₁.lookup x = some v₁ →
      ∃ v₂,
        env₂.lookup x = some v₂ ∧
        CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ v₁ v₂ := by
  induction henv with
  | nil =>
      intro x v₁ hlook
      simp [NamedEnv.lookup] at hlook
  | cons hval hrest ih =>
      rename_i vHead₁ vHead₂ envTail₁ envTail₂ nameHead
      intro x v₁ hlook
      by_cases hname : nameHead = x
      · have hv : vHead₁ = v₁ := by
          exact Option.some.inj (by simpa [NamedEnv.lookup, hname] using hlook)
        refine ⟨vHead₂, ?_, hv ▸ hval⟩
        simp [NamedEnv.lookup, hname]
      · have hlookTail : envTail₁.lookup x = some v₁ := by
          simpa [NamedEnv.lookup, hname] using hlook
        obtain ⟨v₂, hlook₂, hprec⟩ := ih hlookTail
        refine ⟨v₂, ?_, hprec⟩
        simpa [NamedEnv.lookup, hname] using hlook₂

private theorem findCheckedClass_none_of_shapePrecision_local
    (hccShape : Forall₂ (ShapeClassPrecision gct₁)
      (cct₁.map eraseLabelsClass)
      (cct₂.map eraseLabelsClass))
    (hfind : findCheckedClass cct₁ cname = none) :
    findCheckedClass cct₂ cname = none := by
  induction cct₁ generalizing cct₂ with
  | nil =>
      cases cct₂ <;> cases hccShape <;> simp [findCheckedClass, findByName] at hfind ⊢
  | cons ccHead rest ih =>
      cases cct₂ with
      | nil =>
          cases hccShape
      | cons cc₂ rest₂ =>
          cases hccShape with
          | cons hhead htail =>
              by_cases hname : ccHead.name = cname
              · have hheadFind : findCheckedClass (ccHead :: rest) cname = some ccHead := by
                  simp [findCheckedClass, findByName, hname]
                rw [hheadFind] at hfind
                cases hfind
              · have hnameEq : ccHead.name = cc₂.name := by
                  simpa [eraseLabelsClass] using hhead.name_eq
                have hname₂ : cc₂.name ≠ cname := by
                  intro hEq
                  exact hname (hnameEq.trans hEq)
                have htailFind : findCheckedClass rest cname = none := by
                  simpa [findCheckedClass, findByName, hname] using hfind
                simpa [findCheckedClass, findByName, hname₂] using ih htail htailFind

private theorem findCheckedClass_shapePrecision_local
    (hccShape : Forall₂ (ShapeClassPrecision gct₁)
      (cct₁.map eraseLabelsClass)
      (cct₂.map eraseLabelsClass))
    (hfind : findCheckedClass cct₁ cname = some cc₁) :
    ∃ cc₂,
      findCheckedClass cct₂ cname = some cc₂ ∧
      ShapeClassPrecision gct₁ (eraseLabelsClass cc₁) (eraseLabelsClass cc₂) := by
  induction cct₁ generalizing cct₂ with
  | nil =>
      simp [findCheckedClass, findByName] at hfind
  | cons ccHead rest ih =>
      cases cct₂ with
      | nil =>
          cases hccShape
      | cons cc₂ rest₂ =>
          cases hccShape with
          | cons hhead htail =>
              by_cases hname : ccHead.name = cname
              · have hheadFind : findCheckedClass (ccHead :: rest) cname = some ccHead := by
                  simp [findCheckedClass, findByName, hname]
                rw [hheadFind] at hfind
                cases hfind
                have hnameEq : cc₁.name = cc₂.name := by
                  simpa [eraseLabelsClass] using hhead.name_eq
                have hname₂ : cc₂.name = cname := hnameEq.symm.trans hname
                exact ⟨cc₂, by simp [findCheckedClass, findByName, hname₂], hhead⟩
              · have hnameEq : ccHead.name = cc₂.name := by
                  simpa [eraseLabelsClass] using hhead.name_eq
                have hname₂ : cc₂.name ≠ cname := by
                  intro hEq
                  exact hname (hnameEq.trans hEq)
                have htailFind : findCheckedClass rest cname = some cc₁ := by
                  simpa [findCheckedClass, findByName, hname] using hfind
                obtain ⟨cc₂', hfind₂, hprec⟩ := ih htail htailFind
                exact ⟨cc₂', by simpa [findCheckedClass, findByName, hname₂] using hfind₂, hprec⟩

private theorem findCheckedMethodInList_none_of_shapePrecision_local
    (hms : Forall₂ (ShapeMethodPrecision gct₁)
      (ms₁.map eraseLabelsMethod)
      (ms₂.map eraseLabelsMethod))
    (hfind : findCheckedMethodInList ms₁ mname = none) :
    findCheckedMethodInList ms₂ mname = none := by
  induction ms₁ generalizing ms₂ with
  | nil =>
      cases ms₂ <;> cases hms <;> simp [findCheckedMethodInList, findByName] at hfind ⊢
  | cons mHead rest ih =>
      cases ms₂ with
      | nil =>
          cases hms
      | cons m₂ rest₂ =>
          cases hms with
          | cons hhead htail =>
              by_cases hname : mHead.name = mname
              · have hheadFind : findCheckedMethodInList (mHead :: rest) mname = some mHead := by
                  simp [findCheckedMethodInList, findByName, hname]
                rw [hheadFind] at hfind
                cases hfind
              · have hnameEq : mHead.name = m₂.name := by
                  simpa [eraseLabelsMethod] using hhead.name_eq
                have hname₂ : m₂.name ≠ mname := by
                  intro hEq
                  exact hname (hnameEq.trans hEq)
                have htailFind : findCheckedMethodInList rest mname = none := by
                  simpa [findCheckedMethodInList, findByName, hname] using hfind
                simpa [findCheckedMethodInList, findByName, hname₂] using ih htail htailFind

private theorem findCheckedMethodInList_shapePrecision_local
    (hms : Forall₂ (ShapeMethodPrecision gct₁)
      (ms₁.map eraseLabelsMethod)
      (ms₂.map eraseLabelsMethod))
    (hfind : findCheckedMethodInList ms₁ mname = some m₁) :
    ∃ m₂,
      findCheckedMethodInList ms₂ mname = some m₂ ∧
      ShapeMethodPrecision gct₁ (eraseLabelsMethod m₁) (eraseLabelsMethod m₂) := by
  induction ms₁ generalizing ms₂ with
  | nil =>
      simp [findCheckedMethodInList, findByName] at hfind
  | cons mHead rest ih =>
      cases ms₂ with
      | nil =>
          cases hms
      | cons m₂ rest₂ =>
          cases hms with
          | cons hhead htail =>
              by_cases hname : mHead.name = mname
              · have hheadFind : findCheckedMethodInList (mHead :: rest) mname = some mHead := by
                  simp [findCheckedMethodInList, findByName, hname]
                rw [hheadFind] at hfind
                cases hfind
                have hnameEq : m₁.name = m₂.name := by
                  simpa [eraseLabelsMethod] using hhead.name_eq
                have hname₂ : m₂.name = mname := hnameEq.symm.trans hname
                exact ⟨m₂, by simp [findCheckedMethodInList, findByName, hname₂], hhead⟩
              · have hnameEq : mHead.name = m₂.name := by
                  simpa [eraseLabelsMethod] using hhead.name_eq
                have hname₂ : m₂.name ≠ mname := by
                  intro hEq
                  exact hname (hnameEq.trans hEq)
                have htailFind : findCheckedMethodInList rest mname = some m₁ := by
                  simpa [findCheckedMethodInList, findByName, hname] using hfind
                obtain ⟨m₂', hfind₂, hprec⟩ := ih htail htailFind
                exact ⟨m₂', by simpa [findCheckedMethodInList, findByName, hname₂] using hfind₂, hprec⟩

private theorem findCheckedMethodInMro_shapePrecision_local
    (hccShape : Forall₂ (ShapeClassPrecision gct₁)
      (cct₁.map eraseLabelsClass)
      (cct₂.map eraseLabelsClass))
    (hfind : findCheckedMethodInMro cct₁ mro methodName = some m₁) :
    ∃ m₂,
      findCheckedMethodInMro cct₂ mro methodName = some m₂ ∧
      ShapeMethodPrecision gct₁ (eraseLabelsMethod m₁) (eraseLabelsMethod m₂) :=
  findMemberInHierarchy_transport
    (RClass := fun cc₁ cc₂ =>
      ShapeClassPrecision gct₁ (eraseLabelsClass cc₁) (eraseLabelsClass cc₂))
    (RMember := fun m₁ m₂ =>
      ShapeMethodPrecision gct₁ (eraseLabelsMethod m₁) (eraseLabelsMethod m₂))
    (findCheckedClass_none_of_shapePrecision_local hccShape)
    (findCheckedClass_shapePrecision_local hccShape)
    (fun hcc hnone => by
      simpa [eraseLabelsClass] using
        findCheckedMethodInList_none_of_shapePrecision_local hcc.methods_prec hnone)
    (fun hcc hsome => by
      simpa [eraseLabelsClass] using
        findCheckedMethodInList_shapePrecision_local hcc.methods_prec hsome)
    hfind

private theorem checkedExprPrecision_isInstance_right
    (hexpr : CheckedExprPrecision gct e₁ (.isInstance x C)) :
    e₁ = .isInstance x C := by
  cases e₁ <;> cases hexpr <;> rfl

private theorem checkedExprPrecision_not_isInstance_right
    (hexpr : CheckedExprPrecision gct e₁ e₂)
    (hnot : ∀ x C, e₁ ≠ .isInstance x C) :
    ∀ x C, e₂ ≠ .isInstance x C := by
  intro x C he₂
  subst he₂
  exact hnot x C (checkedExprPrecision_isInstance_right hexpr)

private theorem checkedExprPrecision_var
    (hexpr : CheckedExprPrecision gct (.var x) e₂) :
    e₂ = .var x := by
  cases e₂ <;> cases hexpr <;> rfl

private theorem checkedExprPrecision_new
    (hexpr : CheckedExprPrecision gct (.new cname) e₂) :
    e₂ = .new cname := by
  cases e₂ <;> cases hexpr <;> rfl

private theorem checkedExprPrecision_attrAccess
    (hexpr : CheckedExprPrecision gct (.attrAccess base₁ attrName) e₂) :
    ∃ base₂,
      e₂ = .attrAccess base₂ attrName ∧
      CheckedExprPrecision gct base₁ base₂ := by
  cases e₂ with
  | attrAccess base₂ attrName₂ =>
      cases hexpr with
      | attrAccess hbase =>
          exact ⟨base₂, rfl, hbase⟩
  | _ =>
      cases hexpr

private theorem checkedExprPrecision_call
    (hexpr : CheckedExprPrecision gct
      (.call callee₁ arg₁ paramTy₁ returnTy₁ returnLabels₁) e₂) :
    ∃ callee₂, ∃ arg₂, ∃ paramTy₂, ∃ returnTy₂,
      ∃ returnLabels₂ : BoundaryLabels (compileBoundaryTarget returnTy₂),
      e₂ = .call callee₂ arg₂ paramTy₂ returnTy₂ returnLabels₂ ∧
      CheckedExprPrecision gct callee₁ callee₂ ∧
      CheckedExprPrecision gct arg₁ arg₂ ∧
      CompileTargetPrecision paramTy₁ paramTy₂ ∧
      CompileTargetPrecision returnTy₁ returnTy₂ := by
  cases e₂ with
  | call callee₂ arg₂ paramTy₂ returnTy₂ returnLabels₂ =>
      cases hexpr with
      | call hcallee harg hparam hret =>
          exact ⟨callee₂, arg₂, paramTy₂, returnTy₂, returnLabels₂,
            rfl, hcallee, harg, hparam, hret⟩
  | _ =>
      cases hexpr

private theorem checkedExprPrecision_constNone
    (hexpr : CheckedExprPrecision gct .constNone e₂) :
    e₂ = .constNone := by
  cases e₂ <;> cases hexpr <;> rfl

private theorem checkedExprPrecision_constTrue
    (hexpr : CheckedExprPrecision gct .constTrue e₂) :
    e₂ = .constTrue := by
  cases e₂ <;> cases hexpr <;> rfl

private theorem checkedExprPrecision_constFalse
    (hexpr : CheckedExprPrecision gct .constFalse e₂) :
    e₂ = .constFalse := by
  cases e₂ <;> cases hexpr <;> rfl

private theorem checkedExprPrecision_cond
    (hexpr : CheckedExprPrecision gct (.cond test₁ then₁ else₁) e₂) :
    ∃ test₂, ∃ then₂, ∃ else₂,
      e₂ = .cond test₂ then₂ else₂ ∧
      CheckedExprPrecision gct test₁ test₂ ∧
      CheckedExprPrecision gct then₁ then₂ ∧
      CheckedExprPrecision gct else₁ else₂ := by
  cases e₂ with
  | cond test₂ then₂ else₂ =>
      cases hexpr with
      | cond htest hthen helse =>
          exact ⟨test₂, then₂, else₂, rfl, htest, hthen, helse⟩
  | _ =>
      cases hexpr

private theorem checkedExprPrecision_isInstance
    (hexpr : CheckedExprPrecision gct (.isInstance x C) e₂) :
    e₂ = .isInstance x C := by
  cases e₂ <;> cases hexpr <;> rfl

private theorem checkedExprPrecision_enforce
    (hexpr : CheckedExprPrecision gct (.enforce e₁ c₁ labels₁) e₂) :
    ∃ e₂', ∃ c₂, ∃ labels₂ : BoundaryLabels (compileBoundaryTarget c₂),
      e₂ = .enforce e₂' c₂ labels₂ ∧
      CheckedExprPrecision gct e₁ e₂' ∧
      CompileTargetPrecision c₁ c₂ := by
  cases e₂ with
  | enforce e₂' c₂ labels₂ =>
      cases hexpr with
      | enforce he hc =>
          exact ⟨e₂', c₂, labels₂, rfl, he, hc⟩
  | _ =>
      cases hexpr

private theorem checkedExprPrecision_dynAttrAccess
    (hexpr : CheckedExprPrecision gct (.dynAttrAccess base₁ attrName ℓ₁) e₂) :
    ∃ base₂, ∃ ℓ₂,
      e₂ = .dynAttrAccess base₂ attrName ℓ₂ ∧
      CheckedExprPrecision gct base₁ base₂ := by
  cases e₂ with
  | dynAttrAccess base₂ attrName₂ ℓ₂ =>
      cases hexpr with
      | dynAttrAccess hbase =>
          exact ⟨base₂, ℓ₂, rfl, hbase⟩
  | _ =>
      cases hexpr

private theorem boolClass_objRef_is_true_or_false
    (w : CheckedValueWitness gct cct heap (.objRef oid) (.class_ boolClass))
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct) :
    oid = trueOid ∨ oid = falseOid := by
  have hview := checkedValueWitness_class_view w
  cases hview with
  | objRef hlook hfind hmro hmem =>
      have hcn := hwfct.raw.boolLeaf _ _ _ hfind hmro hmem
      exact hheap.boolExhaustive oid _ hlook hcn

private theorem blame_steps_final_aux
    {heap : CheckedHeap} {env : CheckedEnv} {cont : Continuation}
    {s_final : State} {r : CheckedHeap × CheckedResult} {ℓ : Label}
    (hsteps : Steps ct cct { heap, env, control := .blame ℓ, continuation := cont } s_final)
    (hfinal : finalResult? s_final = some r) :
    ∃ ℓ', r = (heap, .blame ℓ') := by
  induction cont generalizing env s_final r with
  | nil =>
      have hs_eq :
          s_final =
            { heap, env, control := .blame ℓ, continuation := ([] : Continuation) } :=
        steps_final_eq hsteps ⟨_, hfinal⟩ .refl
          ⟨(heap, .blame ℓ), by simp [finalResult?]⟩
      subst s_final
      simp [finalResult?] at hfinal
      cases hfinal
      exact ⟨_, rfl⟩
  | cons frame k ih =>
      cases frame with
      | attrAccess _ =>
          exact ih (steps_split_via_determinism
            (RuntimeSteps.single (.blameUnwindAttrAccess (ct := ct) (cct := cct))) hsteps hfinal) hfinal
      | callCallee _ _ _ _ =>
          exact ih (steps_split_via_determinism
            (RuntimeSteps.single (.blameUnwindCallCallee (ct := ct) (cct := cct))) hsteps hfinal) hfinal
      | awaitArgument _ _ _ _ =>
          exact ih (steps_split_via_determinism
            (RuntimeSteps.single (.blameUnwindAwaitArgument (ct := ct) (cct := cct))) hsteps hfinal) hfinal
      | callValue _ _ _ _ =>
          exact ih (steps_split_via_determinism
            (RuntimeSteps.single (.blameUnwindCallValue (ct := ct) (cct := cct))) hsteps hfinal) hfinal
      | cond _ _ =>
          exact ih (steps_split_via_determinism
            (RuntimeSteps.single (.blameUnwindCond (ct := ct) (cct := cct))) hsteps hfinal) hfinal
      | returnTo _ =>
          exact ih (steps_split_via_determinism
            (RuntimeSteps.single (.blameUnwindReturnTo (ct := ct) (cct := cct))) hsteps hfinal) hfinal
      | enforce _ _ =>
          exact ih (steps_split_via_determinism
            (RuntimeSteps.single (.blameUnwindEnforce (ct := ct) (cct := cct))) hsteps hfinal) hfinal
      | dynAttrAccess _ _ =>
          exact ih (steps_split_via_determinism
            (RuntimeSteps.single (.blameUnwindDynAttrAccess (ct := ct) (cct := cct))) hsteps hfinal) hfinal

theorem blame_steps_final
    (_hsafe : CheckedStateSafe ct cct
      s.heap s.env s.control s.continuation expectedType)
    (hctrl : s.control = .blame ℓ)
    (hsteps : Steps ct cct s s_final)
    (hfinal : finalResult? s_final = some r) :
    ∃ ℓ', r = (s.heap, .blame ℓ') := by
  cases s with
  | mk heap env ctrl cont =>
      simp at hctrl
      subst ctrl
      simpa using (blame_steps_final_aux
        (ct := ct) (cct := cct) (heap := heap) (env := env)
        (cont := cont) (s_final := s_final) (r := r) (ℓ := ℓ) hsteps hfinal)

theorem simulate_safe_steps
    (hct : ClassTableAnnotationPrecision gct₁ gct₂)
    (hccShape : Forall₂ (ShapeClassPrecision gct₁)
      (cct₁.map eraseLabelsClass)
      (cct₂.map eraseLabelsClass))
    (hsafe₁ : CheckedStateSafe gct₁ cct₁ s₁.heap s₁.env s₁.control s₁.continuation expectedType₁)
    (hsafe₂ : CheckedStateSafe gct₂ cct₂ s₂.heap s₂.env s₂.control s₂.continuation expectedType₂)
    (hprec : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁ s₂)
    (hnotFinal₁ : finalResult? s₁ = none) :
    SimulationSegmentResult gct₁ gct₂ cct₁ cct₂ expectedType₁ expectedType₂ s₁ s₂ := by
  cases s₁ with
  | mk heap₁ env₁ ctrl₁ cont₁ =>
      cases s₂ with
      | mk heap₂ env₂ ctrl₂ cont₂ =>
          obtain ⟨Γ₁, outΓ₁, G₁, hwfct₁, hheapwf₁, halign₁, henv₁, hctrl₁, hcont₁⟩ := hsafe₁
          obtain ⟨Γ₂, outΓ₂, G₂, hwfct₂, hheapwf₂, halign₂, henv₂, hctrl₂, hcont₂⟩ := hsafe₂
          have hsafe₁' :
              CheckedStateSafe gct₁ cct₁ heap₁ env₁ ctrl₁ cont₁ expectedType₁ :=
            ⟨Γ₁, outΓ₁, G₁, hwfct₁, hheapwf₁, halign₁, henv₁, hctrl₁, hcont₁⟩
          have hsafe₂' :
              CheckedStateSafe gct₂ cct₂ heap₂ env₂ ctrl₂ cont₂ expectedType₂ :=
            ⟨Γ₂, outΓ₂, G₂, hwfct₂, hheapwf₂, halign₂, henv₂, hctrl₂, hcont₂⟩
          rcases hprec with ⟨hheap, henv, hctrl_prec, hcont_prec⟩
          cases hctrl_prec with
          | blame =>
              exact blame_unwind_safe_step hct hccShape hsafe₁' hsafe₂'
                ⟨hheap, henv, .blame, hcont_prec⟩ rfl hnotFinal₁
          | runtimeError =>
              cases hctrl₁
          | expr hexpr =>
              cases hctrl₁ with
              | expr hty₁ =>
                  cases hctrl₂ with
                  | expr hty₂ =>
                      cases hty₁ with
                      | var hlookΓ₁ =>
                          rename_i x
                          obtain rfl := checkedExprPrecision_var hexpr
                          obtain ⟨v₁, hlookup₁, _⟩ := henv₁ _ _ hlookΓ₁
                          obtain ⟨v₂, hlookup₂, hval⟩ :=
                            checkedEnvPrecision_lookup_left henv hlookup₁
                          let s₁' : State :=
                            { heap := heap₁, env := env₁, control := .val v₁, continuation := cont₁ }
                          let s₂' : State :=
                            { heap := heap₂, env := env₂, control := .val v₂, continuation := cont₂ }
                          have hstep₁ : Step gct₁ cct₁
                              { heap := heap₁, env := env₁, control := .expr (.var x), continuation := cont₁ } s₁' :=
                            Step.varSuccess hlookup₁
                          have hstep₂ : Step gct₂ cct₂
                              { heap := heap₂, env := env₂, control := .expr (.var x), continuation := cont₂ } s₂' :=
                            Step.varSuccess hlookup₂
                          have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                            ⟨hheap, henv, .val hval, hcont_prec⟩
                          exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                            (checked_preservation hsafe₁' hstep₁)
                            (checked_preservation hsafe₂' hstep₂) hprec'
                            (fun h => by cases congrArg State.control h)
                      | new hfind₁ hne_bool₁ hne_none₁ hne_bm₁ =>
                          rename_i cname c₁
                          obtain rfl := checkedExprPrecision_new hexpr
                          obtain ⟨c₂, hfind₂, _⟩ :=
                            findGClass_precision hct hfind₁
                          let obj : CheckedHeapObject := ⟨cname, .ordinary⟩
                          let oid : Nat := heap₁.heapCounter
                          let s₁' : State :=
                            { heap := (heap₁.alloc obj).2, env := env₁,
                              control := .val (.objRef oid), continuation := cont₁ }
                          let s₂' : State :=
                            { heap := (heap₂.alloc obj).2, env := env₂,
                              control := .val (.objRef oid), continuation := cont₂ }
                          have halloc₁ : heap₁.alloc obj = (oid, s₁'.heap) := by
                            dsimp [s₁', oid, obj]
                            rw [CheckedHeap.alloc, RuntimeHeap.alloc]
                          have halloc₂ : heap₂.alloc obj = (oid, s₂'.heap) := by
                            dsimp [s₂', oid, obj]
                            rw [CheckedHeap.alloc, RuntimeHeap.alloc]
                            apply Prod.ext
                            · exact hheap.counter_eq.symm
                            · rfl
                          have hheap' :
                              CheckedHeapPrecision gct₁ cct₁ cct₂ s₁'.heap s₂'.heap :=
                            new_alloc_heap_precision hheap rfl halloc₁ halloc₂
                          have hleft :
                              ∀ oid' obj', heap₁.lookup oid' = some obj' → s₁'.heap.lookup oid' = some obj' := by
                            intro oid' obj' hlook
                            simpa [s₁', obj] using
                              lookup_checkedAlloc_of_lookup hheapwf₁.idsBounded hlook
                          have hstep₁ : Step gct₁ cct₁
                              { heap := heap₁, env := env₁, control := .expr (.new cname), continuation := cont₁ } s₁' :=
                            Step.newSuccess hfind₁ hne_bool₁ hne_none₁ hne_bm₁ halloc₁
                          have hstep₂ : Step gct₂ cct₂
                              { heap := heap₂, env := env₂, control := .expr (.new cname), continuation := cont₂ } s₂' :=
                            Step.newSuccess hfind₂ hne_bool₁ hne_none₁ hne_bm₁ halloc₂
                          have hlookupNew : s₁'.heap.lookup oid = some obj := by
                            simpa [s₁', obj, oid] using checkedHeap_alloc_lookup_new halloc₁
                          have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                            ⟨hheap',
                              checkedEnvPrecision_transport_heap hheap' hleft henv,
                              .val (.objRef hheap' hlookupNew),
                              checkedContinuationPrecision_transport_heap hheap' hleft hcont_prec⟩
                          exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                            (checked_preservation hsafe₁' hstep₁)
                            (checked_preservation hsafe₂' hstep₂) hprec'
                            (fun h => by cases congrArg State.control h)
                      | constNone =>
                          obtain rfl := checkedExprPrecision_constNone hexpr
                          let s₁' : State :=
                            { heap := heap₁, env := env₁, control := .val (.objRef noneOid), continuation := cont₁ }
                          let s₂' : State :=
                            { heap := heap₂, env := env₂, control := .val (.objRef noneOid), continuation := cont₂ }
                          have hstep₁ : Step gct₁ cct₁
                              { heap := heap₁, env := env₁, control := .expr .constNone, continuation := cont₁ } s₁' :=
                            Step.constNone
                          have hstep₂ : Step gct₂ cct₂
                              { heap := heap₂, env := env₂, control := .expr .constNone, continuation := cont₂ } s₂' :=
                            Step.constNone
                          have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                            ⟨hheap, henv, .val (.objRef hheap hheapwf₁.initialNone), hcont_prec⟩
                          exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                            (checked_preservation hsafe₁' hstep₁)
                            (checked_preservation hsafe₂' hstep₂) hprec'
                            (fun h => by cases congrArg State.control h)
                      | constTrue =>
                          obtain rfl := checkedExprPrecision_constTrue hexpr
                          let s₁' : State :=
                            { heap := heap₁, env := env₁, control := .val (.objRef trueOid), continuation := cont₁ }
                          let s₂' : State :=
                            { heap := heap₂, env := env₂, control := .val (.objRef trueOid), continuation := cont₂ }
                          have hstep₁ : Step gct₁ cct₁
                              { heap := heap₁, env := env₁, control := .expr .constTrue, continuation := cont₁ } s₁' :=
                            Step.constTrue
                          have hstep₂ : Step gct₂ cct₂
                              { heap := heap₂, env := env₂, control := .expr .constTrue, continuation := cont₂ } s₂' :=
                            Step.constTrue
                          have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                            ⟨hheap, henv, .val (.objRef hheap hheapwf₁.initialTrue), hcont_prec⟩
                          exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                            (checked_preservation hsafe₁' hstep₁)
                            (checked_preservation hsafe₂' hstep₂) hprec'
                            (fun h => by cases congrArg State.control h)
                      | constFalse =>
                          obtain rfl := checkedExprPrecision_constFalse hexpr
                          let s₁' : State :=
                            { heap := heap₁, env := env₁, control := .val (.objRef falseOid), continuation := cont₁ }
                          let s₂' : State :=
                            { heap := heap₂, env := env₂, control := .val (.objRef falseOid), continuation := cont₂ }
                          have hstep₁ : Step gct₁ cct₁
                              { heap := heap₁, env := env₁, control := .expr .constFalse, continuation := cont₁ } s₁' :=
                            Step.constFalse
                          have hstep₂ : Step gct₂ cct₂
                              { heap := heap₂, env := env₂, control := .expr .constFalse, continuation := cont₂ } s₂' :=
                            Step.constFalse
                          have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                            ⟨hheap, henv, .val (.objRef hheap hheapwf₁.initialFalse), hcont_prec⟩
                          exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                            (checked_preservation hsafe₁' hstep₁)
                            (checked_preservation hsafe₂' hstep₂) hprec'
                            (fun h => by cases congrArg State.control h)
                      | @attrAccess _ _ base₁ cname₁ attrName paramTy₁ returnTy₁
                          hbase₁ hfind₁ =>
                          obtain ⟨base₂, rfl, hbase⟩ := checkedExprPrecision_attrAccess hexpr
                          let s₁' : State :=
                            { heap := heap₁, env := env₁, control := .expr base₁,
                              continuation := .attrAccess attrName :: cont₁ }
                          let s₂' : State :=
                            { heap := heap₂, env := env₂, control := .expr base₂,
                              continuation := .attrAccess attrName :: cont₂ }
                          have hstep₁ : Step gct₁ cct₁
                              { heap := heap₁, env := env₁,
                                control := .expr (.attrAccess base₁ attrName), continuation := cont₁ } s₁' :=
                            Step.focusAttrAccess
                          have hstep₂ : Step gct₂ cct₂
                              { heap := heap₂, env := env₂,
                                control := .expr (.attrAccess base₂ attrName), continuation := cont₂ } s₂' :=
                            Step.focusAttrAccess
                          have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                            ⟨hheap, henv, .expr hbase,
                              .cons .attrAccess hcont_prec⟩
                          exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                            (checked_preservation hsafe₁' hstep₁)
                            (checked_preservation hsafe₂' hstep₂) hprec'
                            (fun h => by cases congrArg State.control h)
                      | @attrAccessUnion _ _ base₁ c1 c2 attrName p1 r1 p2 r2
                          hbase₁ hfind₁ hfind₂ =>
                          obtain ⟨base₂, rfl, hbase⟩ := checkedExprPrecision_attrAccess hexpr
                          let s₁' : State :=
                            { heap := heap₁, env := env₁, control := .expr base₁,
                              continuation := .attrAccess attrName :: cont₁ }
                          let s₂' : State :=
                            { heap := heap₂, env := env₂, control := .expr base₂,
                              continuation := .attrAccess attrName :: cont₂ }
                          have hstep₁ : Step gct₁ cct₁
                              { heap := heap₁, env := env₁,
                                control := .expr (.attrAccess base₁ attrName), continuation := cont₁ } s₁' :=
                            Step.focusAttrAccess
                          have hstep₂ : Step gct₂ cct₂
                              { heap := heap₂, env := env₂,
                                control := .expr (.attrAccess base₂ attrName), continuation := cont₂ } s₂' :=
                            Step.focusAttrAccess
                          have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                            ⟨hheap, henv, .expr hbase,
                              .cons .attrAccess hcont_prec⟩
                          exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                            (checked_preservation hsafe₁' hstep₁)
                            (checked_preservation hsafe₂' hstep₂) hprec'
                            (fun h => by cases congrArg State.control h)
                      | @call _ _ callee₁ paramTy₁ returnTy₁ arg₁ argTy₁ returnLabels₁
                          hcallee₁ harg₁ hassign₁ hparam₁ hret₁ hwfParam₁ hwfRet₁ =>
                          obtain ⟨callee₂, arg₂, paramTy₂, returnTy₂, returnLabels₂, rfl,
                              hcallee, harg, hparamTarget, hretTarget⟩ :=
                            checkedExprPrecision_call hexpr
                          let s₁' : State :=
                            { heap := heap₁, env := env₁, control := .expr callee₁,
                              continuation := .callCallee arg₁ paramTy₁ returnTy₁ returnLabels₁ :: cont₁ }
                          let s₂' : State :=
                            { heap := heap₂, env := env₂, control := .expr callee₂,
                              continuation := .callCallee arg₂ paramTy₂ returnTy₂ returnLabels₂ :: cont₂ }
                          have hstep₁ : Step gct₁ cct₁
                              { heap := heap₁, env := env₁,
                                control := .expr (.call callee₁ arg₁ paramTy₁ returnTy₁ returnLabels₁),
                                continuation := cont₁ } s₁' :=
                            Step.focusCall
                          have hstep₂ : Step gct₂ cct₂
                              { heap := heap₂, env := env₂,
                                control := .expr (.call callee₂ arg₂ paramTy₂ returnTy₂ returnLabels₂),
                                continuation := cont₂ } s₂' :=
                            Step.focusCall
                          have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                            ⟨hheap, henv, .expr hcallee,
                              .cons (.callCallee harg hparamTarget hretTarget) hcont_prec⟩
                          exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                            (checked_preservation hsafe₁' hstep₁)
                            (checked_preservation hsafe₂' hstep₂) hprec'
                            (fun h => by cases congrArg State.control h)
                      | @cond _ _ condExpr₁ thenBr₁ R₁ elseBr₁
                          htest₁ hthen₁ helse₁ htarget₁ =>
                          obtain ⟨test₂, thenBr₂, elseBr₂, rfl, htest, hthen, helse⟩ :=
                            checkedExprPrecision_cond hexpr
                          have hfocus :
                              (∀ x C, condExpr₁ ≠ .isInstance x C) →
                              SimulationSegmentResult
                                gct₁ gct₂ cct₁ cct₂ expectedType₁ expectedType₂
                                { heap := heap₁, env := env₁,
                                  control := .expr (.cond condExpr₁ thenBr₁ elseBr₁), continuation := cont₁ }
                                { heap := heap₂, env := env₂,
                                  control := .expr (.cond test₂ thenBr₂ elseBr₂), continuation := cont₂ } := by
                            intro hnot₁
                            have hnot₂ := checkedExprPrecision_not_isInstance_right htest hnot₁
                            let s₁' : State :=
                              { heap := heap₁, env := env₁, control := .expr condExpr₁,
                                continuation := .cond thenBr₁ elseBr₁ :: cont₁ }
                            let s₂' : State :=
                              { heap := heap₂, env := env₂, control := .expr test₂,
                                continuation := .cond thenBr₂ elseBr₂ :: cont₂ }
                            have hstep₁ : Step gct₁ cct₁
                                { heap := heap₁, env := env₁,
                                  control := .expr (.cond condExpr₁ thenBr₁ elseBr₁), continuation := cont₁ } s₁' :=
                              Step.focusCond hnot₁
                            have hstep₂ : Step gct₂ cct₂
                                { heap := heap₂, env := env₂,
                                  control := .expr (.cond test₂ thenBr₂ elseBr₂), continuation := cont₂ } s₂' :=
                              Step.focusCond hnot₂
                            have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                              ⟨hheap, henv, .expr htest,
                                .cons (.cond hthen helse) hcont_prec⟩
                            exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                              (checked_preservation hsafe₁' hstep₁)
                              (checked_preservation hsafe₂' hstep₂) hprec'
                              (fun h => by cases congrArg State.control h)
                          cases condExpr₁ with
                          | var x => exact hfocus nofun
                          | new cname => exact hfocus nofun
                          | attrAccess base attrName => exact hfocus nofun
                          | call callee arg paramTy returnTy returnLabels => exact hfocus nofun
                          | constNone => exact hfocus nofun
                          | constTrue => exact hfocus nofun
                          | constFalse => exact hfocus nofun
                          | cond test thenBr elseBr => exact hfocus nofun
                          | isInstance x C =>
                              obtain rfl := checkedExprPrecision_isInstance htest
                              cases htest₁ with
                              | @isInstance _ _ _ _ _ _ hlookΓ₁ hfindCls₁ =>
                                  obtain ⟨v₁, hlookup₁, _⟩ := henv₁ _ _ hlookΓ₁
                                  cases v₁ with
                                  | objRef oid =>
                                      obtain ⟨v₂, hlookup₂, hval⟩ :=
                                        checkedEnvPrecision_lookup_left henv hlookup₁
                                      cases hval with
                                      | objRef _ hlookObj₁ =>
                                          rcases hheap.lookup_prec_left _ _ hlookObj₁ with
                                            ⟨obj₂, hlookObj₂, hobjprec⟩
                                          obtain ⟨cls₁, mro₁, hfindObj₁, hmro₁⟩ :=
                                            hheapwf₁.classesExist _ _ hlookObj₁
                                          have htransport :
                                              ∃ cls₂,
                                                findGClass gct₂ obj₂.className = some cls₂ ∧
                                                GComputeMro gct₂ cls₂ mro₁ := by
                                            cases hobjprec <;>
                                              · obtain ⟨cls₂, hfindObj₂, hclsPrec⟩ :=
                                                  findGClass_precision
                                                    hct hfindObj₁
                                                exact ⟨cls₂, hfindObj₂,
                                                  gComputeMro_transport
                                                    hct hclsPrec hmro₁⟩
                                          obtain ⟨cls₂, hfindObj₂, hmro₂⟩ := htransport
                                          by_cases hmem : C ∈ mro₁
                                          · let s₁' : State :=
                                              { heap := heap₁, env := env₁, control := .expr thenBr₁,
                                                continuation := .returnTo env₁ :: cont₁ }
                                            let s₂' : State :=
                                              { heap := heap₂, env := env₂, control := .expr thenBr₂,
                                                continuation := .returnTo env₂ :: cont₂ }
                                            have hstep₁ : Step gct₁ cct₁
                                                { heap := heap₁, env := env₁,
                                                  control := .expr (.cond (.isInstance x C) thenBr₁ elseBr₁),
                                                  continuation := cont₁ } s₁' :=
                                              Step.condIsInstanceTrue hlookup₁ hlookObj₁ hfindObj₁ hmro₁ hmem
                                            have hstep₂ : Step gct₂ cct₂
                                                { heap := heap₂, env := env₂,
                                                  control := .expr (.cond (.isInstance x C) thenBr₂ elseBr₂),
                                                  continuation := cont₂ } s₂' :=
                                              Step.condIsInstanceTrue hlookup₂ hlookObj₂ hfindObj₂ hmro₂ hmem
                                            have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                                              ⟨hheap, henv, .expr hthen,
                                                .cons (.returnTo henv) hcont_prec⟩
                                            exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                                              (checked_preservation hsafe₁' hstep₁)
                                              (checked_preservation hsafe₂' hstep₂) hprec'
                                              (fun h => by cases congrArg State.control h)
                                          · let s₁' : State :=
                                              { heap := heap₁, env := env₁, control := .expr elseBr₁,
                                                continuation := .returnTo env₁ :: cont₁ }
                                            let s₂' : State :=
                                              { heap := heap₂, env := env₂, control := .expr elseBr₂,
                                                continuation := .returnTo env₂ :: cont₂ }
                                            have hstep₁ : Step gct₁ cct₁
                                                { heap := heap₁, env := env₁,
                                                  control := .expr (.cond (.isInstance x C) thenBr₁ elseBr₁),
                                                  continuation := cont₁ } s₁' :=
                                              Step.condIsInstanceFalse hlookup₁ hlookObj₁ hfindObj₁ hmro₁ hmem
                                            have hstep₂ : Step gct₂ cct₂
                                                { heap := heap₂, env := env₂,
                                                  control := .expr (.cond (.isInstance x C) thenBr₂ elseBr₂),
                                                  continuation := cont₂ } s₂' :=
                                              Step.condIsInstanceFalse hlookup₂ hlookObj₂ hfindObj₂ hmro₂ hmem
                                            have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                                              ⟨hheap, henv, .expr helse,
                                                .cons (.returnTo henv) hcont_prec⟩
                                            exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                                              (checked_preservation hsafe₁' hstep₁)
                                              (checked_preservation hsafe₂' hstep₂) hprec'
                                              (fun h => by cases congrArg State.control h)
                          | enforce e c labels => exact hfocus nofun
                          | dynAttrAccess base attrName ℓ => exact hfocus nofun
                      | @isInstance _ _ C _ _ x hlookΓ₁ hfindCls₁ =>
                          obtain rfl := checkedExprPrecision_isInstance hexpr
                          obtain ⟨v₁, hlookup₁, _⟩ := henv₁ _ _ hlookΓ₁
                          cases v₁ with
                          | objRef oid =>
                              obtain ⟨v₂, hlookup₂, hval⟩ :=
                                checkedEnvPrecision_lookup_left henv hlookup₁
                              cases hval with
                              | objRef _ hlookObj₁ =>
                                  rcases hheap.lookup_prec_left _ _ hlookObj₁ with
                                    ⟨obj₂, hlookObj₂, hobjprec⟩
                                  obtain ⟨cls₁, mro₁, hfindObj₁, hmro₁⟩ :=
                                    hheapwf₁.classesExist _ _ hlookObj₁
                                  have htransport :
                                      ∃ cls₂,
                                        findGClass gct₂ obj₂.className = some cls₂ ∧
                                        GComputeMro gct₂ cls₂ mro₁ := by
                                    cases hobjprec with
                                    | ordinary =>
                                        obtain ⟨cls₂, hfindObj₂, hclsPrec⟩ :=
                                          findGClass_precision
                                            hct hfindObj₁
                                        exact ⟨cls₂, hfindObj₂,
                                          gComputeMro_transport
                                            hct hclsPrec hmro₁⟩
                                    | boundMethod _ =>
                                        obtain ⟨cls₂, hfindObj₂, hclsPrec⟩ :=
                                          findGClass_precision
                                            hct hfindObj₁
                                        exact ⟨cls₂, hfindObj₂,
                                          gComputeMro_transport
                                            hct hclsPrec hmro₁⟩
                                  obtain ⟨cls₂, hfindObj₂, hmro₂⟩ := htransport
                                  by_cases hmem : C ∈ mro₁
                                  · let s₁' : State :=
                                      { heap := heap₁, env := env₁,
                                        control := .val (.objRef trueOid), continuation := cont₁ }
                                    let s₂' : State :=
                                      { heap := heap₂, env := env₂,
                                        control := .val (.objRef trueOid), continuation := cont₂ }
                                    have hstep₁ : Step gct₁ cct₁
                                        { heap := heap₁, env := env₁,
                                          control := .expr (.isInstance x C), continuation := cont₁ } s₁' :=
                                      Step.isInstanceTrue hlookup₁ hlookObj₁ hfindObj₁ hmro₁ hmem
                                    have hstep₂ : Step gct₂ cct₂
                                        { heap := heap₂, env := env₂,
                                          control := .expr (.isInstance x C), continuation := cont₂ } s₂' :=
                                      Step.isInstanceTrue hlookup₂ hlookObj₂ hfindObj₂ hmro₂ hmem
                                    have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                                      ⟨hheap, henv,
                                        .val (.objRef hheap hheapwf₁.initialTrue), hcont_prec⟩
                                    exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                                      (checked_preservation hsafe₁' hstep₁)
                                      (checked_preservation hsafe₂' hstep₂) hprec'
                                      (fun h => by cases congrArg State.control h)
                                  · let s₁' : State :=
                                      { heap := heap₁, env := env₁,
                                        control := .val (.objRef falseOid), continuation := cont₁ }
                                    let s₂' : State :=
                                      { heap := heap₂, env := env₂,
                                        control := .val (.objRef falseOid), continuation := cont₂ }
                                    have hstep₁ : Step gct₁ cct₁
                                        { heap := heap₁, env := env₁,
                                          control := .expr (.isInstance x C), continuation := cont₁ } s₁' :=
                                      Step.isInstanceFalse hlookup₁ hlookObj₁ hfindObj₁ hmro₁ hmem
                                    have hstep₂ : Step gct₂ cct₂
                                        { heap := heap₂, env := env₂,
                                          control := .expr (.isInstance x C), continuation := cont₂ } s₂' :=
                                      Step.isInstanceFalse hlookup₂ hlookObj₂ hfindObj₂ hmro₂ hmem
                                    have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                                      ⟨hheap, henv,
                                        .val (.objRef hheap hheapwf₁.initialFalse), hcont_prec⟩
                                    exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                                      (checked_preservation hsafe₁' hstep₁)
                                      (checked_preservation hsafe₂' hstep₂) hprec'
                                      (fun h => by cases congrArg State.control h)
                      | @condIsInstance T₁ _ C cls₁ R₁ thenBr₁ elseBr₁ _ x
                          hlookΓ₁ hfindCls₁ htarget₁ hthenTarget₁ helseTarget₁ hthen₁ helse₁ =>
                          obtain ⟨test₂, thenBr₂, elseBr₂, rfl, htest, hthen, helse⟩ :=
                            checkedExprPrecision_cond hexpr
                          obtain rfl := checkedExprPrecision_isInstance htest
                          obtain ⟨v₁, hlookup₁, _⟩ := henv₁ _ _ hlookΓ₁
                          cases v₁ with
                          | objRef oid =>
                              obtain ⟨v₂, hlookup₂, hval⟩ :=
                                checkedEnvPrecision_lookup_left henv hlookup₁
                              cases hval with
                              | objRef _ hlookObj₁ =>
                                  rcases hheap.lookup_prec_left _ _ hlookObj₁ with
                                    ⟨obj₂, hlookObj₂, hobjprec⟩
                                  obtain ⟨cls₁', mro₁, hfindObj₁, hmro₁⟩ :=
                                    hheapwf₁.classesExist _ _ hlookObj₁
                                  have htransport :
                                      ∃ cls₂,
                                        findGClass gct₂ obj₂.className = some cls₂ ∧
                                        GComputeMro gct₂ cls₂ mro₁ := by
                                    cases hobjprec with
                                    | ordinary =>
                                        obtain ⟨cls₂, hfindObj₂, hclsPrec⟩ :=
                                          findGClass_precision
                                            hct hfindObj₁
                                        exact ⟨cls₂, hfindObj₂,
                                          gComputeMro_transport
                                            hct hclsPrec hmro₁⟩
                                    | boundMethod _ =>
                                        obtain ⟨cls₂, hfindObj₂, hclsPrec⟩ :=
                                          findGClass_precision
                                            hct hfindObj₁
                                        exact ⟨cls₂, hfindObj₂,
                                          gComputeMro_transport
                                            hct hclsPrec hmro₁⟩
                                  obtain ⟨cls₂, hfindObj₂, hmro₂⟩ := htransport
                                  by_cases hmem : C ∈ mro₁
                                  · let s₁' : State :=
                                      { heap := heap₁, env := env₁, control := .expr thenBr₁,
                                        continuation := .returnTo env₁ :: cont₁ }
                                    let s₂' : State :=
                                      { heap := heap₂, env := env₂, control := .expr thenBr₂,
                                        continuation := .returnTo env₂ :: cont₂ }
                                    have hstep₁ : Step gct₁ cct₁
                                        { heap := heap₁, env := env₁,
                                          control := .expr (.cond (.isInstance x C) thenBr₁ elseBr₁),
                                          continuation := cont₁ } s₁' :=
                                      Step.condIsInstanceTrue hlookup₁ hlookObj₁ hfindObj₁ hmro₁ hmem
                                    have hstep₂ : Step gct₂ cct₂
                                        { heap := heap₂, env := env₂,
                                          control := .expr (.cond (.isInstance x C) thenBr₂ elseBr₂),
                                          continuation := cont₂ } s₂' :=
                                      Step.condIsInstanceTrue hlookup₂ hlookObj₂ hfindObj₂ hmro₂ hmem
                                    have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                                      ⟨hheap, henv, .expr hthen,
                                        .cons (.returnTo henv) hcont_prec⟩
                                    exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                                      (checked_preservation hsafe₁' hstep₁)
                                      (checked_preservation hsafe₂' hstep₂) hprec'
                                      (fun h => by cases congrArg State.control h)
                                  · let s₁' : State :=
                                      { heap := heap₁, env := env₁, control := .expr elseBr₁,
                                        continuation := .returnTo env₁ :: cont₁ }
                                    let s₂' : State :=
                                      { heap := heap₂, env := env₂, control := .expr elseBr₂,
                                        continuation := .returnTo env₂ :: cont₂ }
                                    have hstep₁ : Step gct₁ cct₁
                                        { heap := heap₁, env := env₁,
                                          control := .expr (.cond (.isInstance x C) thenBr₁ elseBr₁),
                                          continuation := cont₁ } s₁' :=
                                      Step.condIsInstanceFalse hlookup₁ hlookObj₁ hfindObj₁ hmro₁ hmem
                                    have hstep₂ : Step gct₂ cct₂
                                        { heap := heap₂, env := env₂,
                                          control := .expr (.cond (.isInstance x C) thenBr₂ elseBr₂),
                                          continuation := cont₂ } s₂' :=
                                      Step.condIsInstanceFalse hlookup₂ hlookObj₂ hfindObj₂ hmro₂ hmem
                                    have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                                      ⟨hheap, henv, .expr helse,
                                        .cons (.returnTo henv) hcont_prec⟩
                                    exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                                      (checked_preservation hsafe₁' hstep₁)
                                      (checked_preservation hsafe₂' hstep₂) hprec'
                                      (fun h => by cases congrArg State.control h)
                      | @enforce _ _ e₁ Gin₁ c₁ labels₁
                          he₁ hwf₁ htarget₁ =>
                          obtain ⟨e₂, c₂, labels₂, rfl, he, hc⟩ :=
                            checkedExprPrecision_enforce hexpr
                          let s₁' : State :=
                            { heap := heap₁, env := env₁, control := .expr e₁,
                              continuation := .enforce c₁ labels₁ :: cont₁ }
                          let s₂' : State :=
                            { heap := heap₂, env := env₂, control := .expr e₂,
                              continuation := .enforce c₂ labels₂ :: cont₂ }
                          have hstep₁ : Step gct₁ cct₁
                              { heap := heap₁, env := env₁,
                                control := .expr (.enforce e₁ c₁ labels₁), continuation := cont₁ } s₁' :=
                            Step.focusEnforce
                          have hstep₂ : Step gct₂ cct₂
                              { heap := heap₂, env := env₂,
                                control := .expr (.enforce e₂ c₂ labels₂), continuation := cont₂ } s₂' :=
                            Step.focusEnforce
                          have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                            ⟨hheap, henv, .expr he,
                              .cons (.enforce hc) hcont_prec⟩
                          exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                            (checked_preservation hsafe₁' hstep₁)
                            (checked_preservation hsafe₂' hstep₂) hprec'
                            (fun h => by cases congrArg State.control h)
                      | @dynAttrAccess _ _ base₁ Gbase₁ attrName ℓ₁ hbase₁ =>
                          obtain ⟨base₂, ℓ₂, rfl, hbase⟩ := checkedExprPrecision_dynAttrAccess hexpr
                          let s₁' : State :=
                            { heap := heap₁, env := env₁, control := .expr base₁,
                              continuation := .dynAttrAccess attrName ℓ₁ :: cont₁ }
                          let s₂' : State :=
                            { heap := heap₂, env := env₂, control := .expr base₂,
                              continuation := .dynAttrAccess attrName ℓ₂ :: cont₂ }
                          have hstep₁ : Step gct₁ cct₁
                              { heap := heap₁, env := env₁,
                                control := .expr (.dynAttrAccess base₁ attrName ℓ₁), continuation := cont₁ } s₁' :=
                            Step.focusDynAttrAccess
                          have hstep₂ : Step gct₂ cct₂
                              { heap := heap₂, env := env₂,
                                control := .expr (.dynAttrAccess base₂ attrName ℓ₂), continuation := cont₂ } s₂' :=
                            Step.focusDynAttrAccess
                          have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                            ⟨hheap, henv, .expr hbase,
                              .cons .dynAttrAccess hcont_prec⟩
                          exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                            (checked_preservation hsafe₁' hstep₁)
                            (checked_preservation hsafe₂' hstep₂) hprec'
                            (fun h => by cases congrArg State.control h)
          | val hval =>
              rename_i v₁ v₂
              cases hctrl₁ with
              | val w₁ =>
                  cases hctrl₂ with
                  | val w₂ =>
                      cases cont₁ with
                      | nil =>
                          simp [finalResult?] at hnotFinal₁
                      | cons frame₁ k₁ =>
                          cases hcont₁ with
                          | cons hframe₁ hcont₁_tail =>
                              cases frame₁ with
                              | attrAccess attrName =>
                                  cases v₁ with
                                  | objRef oid =>
                                      obtain ⟨obj₁, hlookObj₁⟩ := checkedValueWitness_objRef_lookup w₁ rfl
                                      cases hval with
                                      | objRef hheapv hlookObj₁' =>
                                          rcases hheap.lookup_prec_left _ _ hlookObj₁ with
                                            ⟨obj₂, hlookObj₂, hobjprec⟩
                                          obtain ⟨cls₁, mro₁, hfindCls₁, hmro₁⟩ :=
                                            hheapwf₁.classesExist _ _ hlookObj₁
                                          have htransport :
                                              ∃ cls₂,
                                                findGClass gct₂ obj₂.className = some cls₂ ∧
                                                GComputeMro gct₂ cls₂ mro₁ := by
                                            cases hobjprec <;>
                                              · obtain ⟨cls₂, hfindCls₂, hclsPrec⟩ :=
                                                  findGClass_precision
                                                    hct hfindCls₁
                                                exact ⟨cls₂, hfindCls₂,
                                                  gComputeMro_transport
                                                    hct hclsPrec hmro₁⟩
                                          obtain ⟨cls₂, hfindCls₂, hmro₂⟩ := htransport
                                          cases cont₂ with
                                          | nil =>
                                              cases hcont_prec
                                          | cons frame₂ k₂ =>
                                              cases hcont₂ with
                                              | cons hframe₂ hcont₂_tail =>
                                                  cases hcont_prec with
                                                  | cons hframe_prec hcont_prec_tail =>
                                                      cases hframe_prec with
                                                      | attrAccess =>
                                                          have attrSuccess :
                                                              ∀ {m₁},
                                                                findCheckedMethodInMro cct₁ mro₁ attrName = some m₁ →
                                                                SimulationSegmentResult
                                                                  gct₁ gct₂ cct₁ cct₂
                                                                  expectedType₁ expectedType₂
                                                                  { heap := heap₁, env := env₁,
                                                                    control := .val (.objRef oid),
                                                                    continuation := .attrAccess attrName :: k₁ }
                                                                  { heap := heap₂, env := env₂,
                                                                    control := .val (.objRef oid),
                                                                    continuation := .attrAccess attrName :: k₂ } := by
                                                            intro m₁ hmeth₁
                                                            obtain ⟨m₂, hmeth₂, hmethPrec⟩ :=
                                                              findCheckedMethodInMro_shapePrecision_local hccShape hmeth₁
                                                            let bmObj₁ : CheckedHeapObject :=
                                                              ⟨boundMethodClass, .boundMethod oid m₁⟩
                                                            let bmObj₂ : CheckedHeapObject :=
                                                              ⟨boundMethodClass, .boundMethod oid m₂⟩
                                                            let bmOid : Nat := heap₁.heapCounter
                                                            let s₁' : State :=
                                                              { heap := (heap₁.alloc bmObj₁).2, env := env₁,
                                                                control := .val (.objRef bmOid), continuation := k₁ }
                                                            let s₂' : State :=
                                                              { heap := (heap₂.alloc bmObj₂).2, env := env₂,
                                                                control := .val (.objRef bmOid), continuation := k₂ }
                                                            have halloc₁ : heap₁.alloc bmObj₁ = (bmOid, s₁'.heap) := by
                                                              dsimp [s₁', bmOid, bmObj₁]
                                                              rw [CheckedHeap.alloc, RuntimeHeap.alloc]
                                                            have halloc₂ : heap₂.alloc bmObj₂ = (bmOid, s₂'.heap) := by
                                                              dsimp [s₂', bmOid, bmObj₂]
                                                              rw [CheckedHeap.alloc, RuntimeHeap.alloc]
                                                              apply Prod.ext
                                                              · exact hheap.counter_eq.symm
                                                              · rfl
                                                            have hheap' :
                                                                CheckedHeapPrecision gct₁ cct₁ cct₂ s₁'.heap s₂'.heap :=
                                                              boundMethod_alloc_heap_precision hheap hmethPrec halloc₁ halloc₂
                                                            have hleft :
                                                                ∀ oid' obj', heap₁.lookup oid' = some obj' →
                                                                  s₁'.heap.lookup oid' = some obj' := by
                                                              intro oid' obj' hlook
                                                              simpa [s₁', bmObj₁] using
                                                                lookup_checkedAlloc_of_lookup hheapwf₁.idsBounded hlook
                                                            have hstep₁ : Step gct₁ cct₁
                                                                { heap := heap₁, env := env₁,
                                                                  control := .val (.objRef oid),
                                                                  continuation := .attrAccess attrName :: k₁ } s₁' :=
                                                              Step.returnAttrAccess hlookObj₁ hfindCls₁ hmro₁ hmeth₁ halloc₁
                                                            have hstep₂ : Step gct₂ cct₂
                                                                { heap := heap₂, env := env₂,
                                                                  control := .val (.objRef oid),
                                                                  continuation := .attrAccess attrName :: k₂ } s₂' :=
                                                              Step.returnAttrAccess hlookObj₂ hfindCls₂ hmro₂ hmeth₂ halloc₂
                                                            have hlookupNew : s₁'.heap.lookup bmOid = some bmObj₁ := by
                                                              simpa [s₁', bmObj₁, bmOid] using
                                                                checkedHeap_alloc_lookup_new halloc₁
                                                            have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                                                              ⟨hheap',
                                                                checkedEnvPrecision_transport_heap hheap' hleft henv,
                                                                .val (.objRef hheap' hlookupNew),
                                                                checkedContinuationPrecision_transport_heap hheap' hleft hcont_prec_tail⟩
                                                            exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                                                              (checked_preservation hsafe₁' hstep₁)
                                                              (checked_preservation hsafe₂' hstep₂) hprec'
                                                              (fun h => by cases congrArg State.continuation h)
                                                          cases hframe₁ with
                                                          | attrAccess hfind =>
                                                              cases hmeth₁ : findCheckedMethodInMro cct₁ mro₁ attrName with
                                                              | none =>
                                                                  exact (attrAccess_method_exists_contradiction
                                                                    hfind w₁ hlookObj₁ hfindCls₁ hmro₁ hmeth₁ halign₁).elim
                                                              | some m₁ =>
                                                                  exact attrSuccess hmeth₁
                                                          | attrAccessUnion hfind₁ hfind₂ =>
                                                              cases w₁.data with
                                                              | unionLeft wL =>
                                                                  cases hmeth₁ : findCheckedMethodInMro cct₁ mro₁ attrName with
                                                                  | none =>
                                                                      exact (attrAccess_method_exists_contradiction
                                                                        hfind₁ wL hlookObj₁ hfindCls₁ hmro₁ hmeth₁ halign₁).elim
                                                                  | some m₁ =>
                                                                      exact attrSuccess hmeth₁
                                                              | unionRight wR =>
                                                                  cases hmeth₁ : findCheckedMethodInMro cct₁ mro₁ attrName with
                                                                  | none =>
                                                                      exact (attrAccess_method_exists_contradiction
                                                                        hfind₂ wR hlookObj₁ hfindCls₁ hmro₁ hmeth₁ halign₁).elim
                                                                  | some m₁ =>
                                                                      exact attrSuccess hmeth₁
                              | dynAttrAccess attrName ℓ₁ =>
                                  cases v₁ with
                                  | objRef oid =>
                                      obtain ⟨obj₁, hlookObj₁⟩ := checkedValueWitness_objRef_lookup w₁ rfl
                                      cases hval with
                                      | objRef hheapv hlookObj₁' =>
                                          rcases hheap.lookup_prec_left _ _ hlookObj₁ with
                                            ⟨obj₂, hlookObj₂, hobjprec⟩
                                          obtain ⟨cls₁, mro₁, hfindCls₁, hmro₁⟩ :=
                                            hheapwf₁.classesExist _ _ hlookObj₁
                                          have htransport :
                                              ∃ cls₂,
                                                findGClass gct₂ obj₂.className = some cls₂ ∧
                                                GComputeMro gct₂ cls₂ mro₁ := by
                                            cases hobjprec <;>
                                              · obtain ⟨cls₂, hfindCls₂, hclsPrec⟩ :=
                                                  findGClass_precision
                                                    hct hfindCls₁
                                                exact ⟨cls₂, hfindCls₂,
                                                  gComputeMro_transport
                                                    hct hclsPrec hmro₁⟩
                                          obtain ⟨cls₂, hfindCls₂, hmro₂⟩ := htransport
                                          cases cont₂ with
                                          | nil =>
                                              cases hcont_prec
                                          | cons frame₂ k₂ =>
                                              cases hcont₂ with
                                              | cons hframe₂ hcont₂_tail =>
                                                  cases hcont_prec with
                                                  | cons hframe_prec hcont_prec_tail =>
                                                      cases hframe_prec with
                                                      | dynAttrAccess =>
                                                          rename_i ℓ₂
                                                          cases hmeth₁ : findCheckedMethodInMro cct₁ mro₁ attrName with
                                                          | none =>
                                                              let s₁' : State :=
                                                                { heap := heap₁, env := env₁,
                                                                  control := .blame ℓ₁, continuation := k₁ }
                                                              have hstep₁ : Step gct₁ cct₁
                                                                  { heap := heap₁, env := env₁,
                                                                    control := .val (.objRef oid),
                                                                    continuation := .dynAttrAccess attrName ℓ₁ :: k₁ } s₁' :=
                                                                Step.returnDynAttrAccessNotFound hlookObj₁ hfindCls₁ hmro₁ hmeth₁
                                                              exact .leftBlame hstep₁ rfl .refl hsafe₂'
                                                                (fun h => by cases congrArg State.continuation h)
                                                          | some m₁ =>
                                                              obtain ⟨m₂, hmeth₂, hmethPrec⟩ :=
                                                                findCheckedMethodInMro_shapePrecision_local hccShape hmeth₁
                                                              let bmObj₁ : CheckedHeapObject :=
                                                                ⟨boundMethodClass, .boundMethod oid m₁⟩
                                                              let bmObj₂ : CheckedHeapObject :=
                                                                ⟨boundMethodClass, .boundMethod oid m₂⟩
                                                              let bmOid : Nat := heap₁.heapCounter
                                                              let s₁' : State :=
                                                                { heap := (heap₁.alloc bmObj₁).2, env := env₁,
                                                                  control := .val (.objRef bmOid), continuation := k₁ }
                                                              let s₂' : State :=
                                                                { heap := (heap₂.alloc bmObj₂).2, env := env₂,
                                                                  control := .val (.objRef bmOid), continuation := k₂ }
                                                              have halloc₁ : heap₁.alloc bmObj₁ = (bmOid, s₁'.heap) := by
                                                                dsimp [s₁', bmOid, bmObj₁]
                                                                rw [CheckedHeap.alloc, RuntimeHeap.alloc]
                                                              have halloc₂ : heap₂.alloc bmObj₂ = (bmOid, s₂'.heap) := by
                                                                dsimp [s₂', bmOid, bmObj₂]
                                                                rw [CheckedHeap.alloc, RuntimeHeap.alloc]
                                                                apply Prod.ext
                                                                · exact hheap.counter_eq.symm
                                                                · rfl
                                                              have hheap' :
                                                                  CheckedHeapPrecision gct₁ cct₁ cct₂ s₁'.heap s₂'.heap :=
                                                                boundMethod_alloc_heap_precision hheap hmethPrec halloc₁ halloc₂
                                                              have hleft :
                                                                  ∀ oid' obj', heap₁.lookup oid' = some obj' →
                                                                    s₁'.heap.lookup oid' = some obj' := by
                                                                intro oid' obj' hlook
                                                                simpa [s₁', bmObj₁] using
                                                                  lookup_checkedAlloc_of_lookup hheapwf₁.idsBounded hlook
                                                              have hstep₁ : Step gct₁ cct₁
                                                                  { heap := heap₁, env := env₁,
                                                                    control := .val (.objRef oid),
                                                                    continuation := .dynAttrAccess attrName ℓ₁ :: k₁ } s₁' :=
                                                                Step.returnDynAttrAccess hlookObj₁ hfindCls₁ hmro₁ hmeth₁ halloc₁
                                                              have hstep₂ : Step gct₂ cct₂
                                                                  { heap := heap₂, env := env₂,
                                                                    control := .val (.objRef oid),
                                                                    continuation := .dynAttrAccess attrName ℓ₂ :: k₂ } s₂' :=
                                                                Step.returnDynAttrAccess hlookObj₂ hfindCls₂ hmro₂ hmeth₂ halloc₂
                                                              have hlookupNew : s₁'.heap.lookup bmOid = some bmObj₁ := by
                                                                simpa [s₁', bmObj₁, bmOid] using
                                                                  checkedHeap_alloc_lookup_new halloc₁
                                                              have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                                                                ⟨hheap',
                                                                  checkedEnvPrecision_transport_heap hheap' hleft henv,
                                                                  .val (.objRef hheap' hlookupNew),
                                                                  checkedContinuationPrecision_transport_heap hheap' hleft hcont_prec_tail⟩
                                                              exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                                                                (checked_preservation hsafe₁' hstep₁)
                                                                (checked_preservation hsafe₂' hstep₂) hprec'
                                                                (fun h => by cases congrArg State.continuation h)
                              | callCallee arg₁ paramTy₁ returnTy₁ returnLabels₁ =>
                                  cases v₁ with
                                  | objRef calleeOid =>
                                      cases hval with
                                      | objRef hheapv hlookCallee₁ =>
                                          have hview₁ : CheckedCallableView gct₁ cct₁ heap₁ (.objRef calleeOid) := by
                                            cases hframe₁ with
                                            | callCallee _ _ _ _ _ _ =>
                                                exact checkedValueWitness_callable_view w₁
                                          cases hview₁ with
                                          | objRefBoundMethod hlookBound₁ hrecv₁ hmroMethod₁ =>
                                              rename_i m₁ recvOid
                                              rcases hheap.lookup_prec_left _ _ hlookBound₁ with
                                                ⟨obj₂, hlookBound₂, hobjprec⟩
                                              cases cont₂ with
                                              | nil =>
                                                  cases hcont_prec
                                              | cons frame₂ k₂ =>
                                                  cases hcont₂ with
                                                  | cons hframe₂ hcont₂_tail =>
                                                      cases hcont_prec with
                                                      | cons hframe_prec hcont_prec_tail =>
                                                          cases hframe_prec with
                                                          | callCallee harg hparam hret =>
                                                              rename_i arg₂ paramTy₂ returnTy₂ returnLabels₂
                                                              cases hobjprec with
                                                              | boundMethod hmethPrec =>
                                                                  rename_i m₂
                                                                  let s₁' : State :=
                                                                    { heap := heap₁, env := env₁,
                                                                      control := .expr arg₁,
                                                                      continuation := .awaitArgument recvOid m₁ returnTy₁ returnLabels₁ :: k₁ }
                                                                  let s₂' : State :=
                                                                    { heap := heap₂, env := env₂,
                                                                      control := .expr arg₂,
                                                                      continuation := .awaitArgument recvOid m₂ returnTy₂ returnLabels₂ :: k₂ }
                                                                  have hstep₁ : Step gct₁ cct₁
                                                                      { heap := heap₁, env := env₁,
                                                                        control := .val (.objRef calleeOid),
                                                                        continuation := .callCallee arg₁ paramTy₁ returnTy₁ returnLabels₁ :: k₁ } s₁' :=
                                                                    Step.returnCallCalleeBound hlookBound₁
                                                                  have hstep₂ : Step gct₂ cct₂
                                                                      { heap := heap₂, env := env₂,
                                                                        control := .val (.objRef calleeOid),
                                                                        continuation := .callCallee arg₂ paramTy₂ returnTy₂ returnLabels₂ :: k₂ } s₂' :=
                                                                    Step.returnCallCalleeBound hlookBound₂
                                                                  have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                                                                    ⟨hheap, henv, .expr harg,
                                                                      .cons (.awaitArgument hmethPrec hret) hcont_prec_tail⟩
                                                                  exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                                                                    (checked_preservation hsafe₁' hstep₁)
                                                                    (checked_preservation hsafe₂' hstep₂) hprec'
                                                                    (fun h => by cases congrArg State.continuation h)
                              | callValue argVal₁ paramTy₁ returnTy₁ returnLabels₁ =>
                                  cases v₁ with
                                  | objRef calleeOid =>
                                      cases hval with
                                      | objRef hheapv hlookCallee₁ =>
                                          have hview₁ : CheckedCallableView gct₁ cct₁ heap₁ (.objRef calleeOid) := by
                                            cases hframe₁ with
                                            | callValue _ _ _ _ _ =>
                                                exact checkedValueWitness_callable_view w₁
                                          cases hview₁ with
                                          | objRefBoundMethod hlookBound₁ hrecv₁ hmroMethod₁ =>
                                              rename_i m₁ recvOid
                                              rcases hheap.lookup_prec_left _ _ hlookBound₁ with
                                                ⟨obj₂, hlookBound₂, hobjprec⟩
                                              cases cont₂ with
                                              | nil =>
                                                  cases hcont_prec
                                              | cons frame₂ k₂ =>
                                                  cases hcont₂ with
                                                  | cons hframe₂ hcont₂_tail =>
                                                      cases hcont_prec with
                                                      | cons hframe_prec hcont_prec_tail =>
                                                          cases hframe_prec with
                                                          | callValue harg hparam hret =>
                                                              rename_i argVal₂ paramTy₂ returnTy₂ returnLabels₂
                                                              cases hobjprec with
                                                              | boundMethod hmethPrec =>
                                                                  rename_i m₂
                                                                  let s₁' : State :=
                                                                    { heap := heap₁, env := env₁,
                                                                      control := .val argVal₁,
                                                                      continuation := .awaitArgument recvOid m₁ returnTy₁ returnLabels₁ :: k₁ }
                                                                  let s₂' : State :=
                                                                    { heap := heap₂, env := env₂,
                                                                      control := .val argVal₂,
                                                                      continuation := .awaitArgument recvOid m₂ returnTy₂ returnLabels₂ :: k₂ }
                                                                  have hstep₁ : Step gct₁ cct₁
                                                                      { heap := heap₁, env := env₁,
                                                                        control := .val (.objRef calleeOid),
                                                                        continuation := .callValue argVal₁ paramTy₁ returnTy₁ returnLabels₁ :: k₁ } s₁' :=
                                                                    Step.returnCallValueBound hlookBound₁
                                                                  have hstep₂ : Step gct₂ cct₂
                                                                      { heap := heap₂, env := env₂,
                                                                        control := .val (.objRef calleeOid),
                                                                        continuation := .callValue argVal₂ paramTy₂ returnTy₂ returnLabels₂ :: k₂ } s₂' :=
                                                                    Step.returnCallValueBound hlookBound₂
                                                                  have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                                                                    ⟨hheap, henv, .val harg,
                                                                      .cons (.awaitArgument hmethPrec hret) hcont_prec_tail⟩
                                                                  exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                                                                    (checked_preservation hsafe₁' hstep₁)
                                                                    (checked_preservation hsafe₂' hstep₂) hprec'
                                                                    (fun h => by cases congrArg State.continuation h)
                              | awaitArgument recvOid m₁ returnTy₁ returnLabels₁ =>
                                  have hshape₁ := checkedValueWitness_toShape w₁
                                  have hlookup₁ :
                                      ∀ oid, v₁ = .objRef oid → ∃ obj, heap₁.lookup oid = some obj := by
                                    intro oid hv
                                    exact checkedAnyShape_objRef_lookup hshape₁ hv
                                  let callReturnTy₁ := returnTy₁
                                  let callReturnLabels₁ := returnLabels₁
                                  cases cont₂ with
                                  | nil =>
                                      cases hcont_prec
                                  | cons frame₂ k₂ =>
                                      cases frame₂ with
                                      | awaitArgument recvOid m₂ returnTy₂ returnLabels₂ =>
                                          cases hcont₂ with
                                          | cons hframe₂ hcont₂_tail =>
                                              cases hcont_prec with
                                              | cons hframe_prec hcont_prec_tail =>
                                                  cases hframe_prec with
                                                  | awaitArgument hmethPrec hret =>
                                                      cases hframe₁ with
                                                      | awaitArgument hrecv₁ hmroMethod₁ hparamTarget₁ hmethodReturnTarget₁
                                                          hcallReturnTarget₁ hparamWf₁ hmethodReturnWf₁ hcallReturnWf₁ =>
                                                              cases hframe₂ with
                                                          | awaitArgument hrecv₂ hmroMethod₂ hparamTarget₂ hmethodReturnTarget₂
                                                              hcallReturnTarget₂ hparamWf₂ hmethodReturnWf₂ hcallReturnWf₂ =>
                                                              have hparamTargetPrec :
                                                                  CompileTargetPrecision
                                                                    m₁.paramTy
                                                                    m₂.paramTy :=
                                                                compileTargetPrecision_of_checkedTargetPrecision
                                                                  (checkedMethodPrecision_paramTarget_precision hmethPrec)
                                                              have hmethodReturnPrec :
                                                                  CompileTargetPrecision
                                                                    m₁.returnTy
                                                                    m₂.returnTy :=
                                                                compileTargetPrecision_of_checkedTargetPrecision
                                                                  (checkedMethodPrecision_returnTarget_precision hmethPrec)
                                                              have hbodyPrec : CheckedExprPrecision gct₁ m₁.body m₂.body := by
                                                                simpa [CheckedMethodPrecision, eraseLabelsMethod] using hmethPrec.body_prec
                                                              have hparamName : m₁.param = m₂.param := by
                                                                simpa [CheckedMethodPrecision, eraseLabelsMethod] using hmethPrec.param_eq
                                                              have hrecvName : m₁.receiverParam = m₂.receiverParam := by
                                                                simpa [CheckedMethodPrecision, eraseLabelsMethod] using hmethPrec.receiver_eq
                                                              rcases enforceValue_total
                                                                  hheapwf₁ hwfct₁ m₁.parameterContract m₁.parameterLabels v₁ hlookup₁ with
                                                                ⟨v₁', henf₁⟩ | henf₁
                                                              · have w₁' : CheckedValueWitness gct₁ cct₁ heap₁ v₁' m₁.paramTy :=
                                                                  enforce_ok_has_checkedTargetWitness
                                                                    henf₁
                                                                    hshape₁
                                                                    hheapwf₁
                                                                    hwfct₁
                                                                    halign₁
                                                                    hparamTarget₁
                                                                    hparamWf₁
                                                                have hsame : v₁' = v₁ := enforce_ok_same_value henf₁
                                                                subst v₁'
                                                                have henf₂ :
                                                                    EnforceValue gct₂ heap₂ v₂
                                                                      m₂.parameterContract m₂.parameterLabels (.ok v₂) :=
                                                                  enforce_exists_under_precision
                                                                    hct
                                                                    hheapwf₂
                                                                    hwfct₂
                                                                    halign₂
                                                                    hval
                                                                    w₁'
                                                                    hparamTarget₂
                                                                    hparamWf₂
                                                                    hparamTargetPrec
                                                                    m₂.parameterLabels
                                                                have hrecvPrec :
                                                                    CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
                                                                      (.objRef recvOid) (.objRef recvOid) :=
                                                                  .objRef hheap hrecv₁
                                                                let s₁' : State :=
                                                                  { heap := heap₁,
                                                                    env := [(m₁.param, v₁), (m₁.receiverParam, .objRef recvOid)],
                                                                    control := .expr m₁.body,
                                                                    continuation :=
                                                                      .enforce m₁.returnTy m₁.returnLabels ::
                                                                        .enforce callReturnTy₁ callReturnLabels₁ ::
                                                                        .returnTo env₁ :: k₁ }
                                                                let s₂' : State :=
                                                                  { heap := heap₂,
                                                                    env := [(m₂.param, v₂), (m₂.receiverParam, .objRef recvOid)],
                                                                    control := .expr m₂.body,
                                                                    continuation :=
                                                                      .enforce m₂.returnTy m₂.returnLabels ::
                                                                        .enforce returnTy₂ returnLabels₂ ::
                                                                        .returnTo env₂ :: k₂ }
                                                                have hstep₁ : Step gct₁ cct₁
                                                                    { heap := heap₁, env := env₁,
                                                                      control := .val v₁,
                                                                      continuation := .awaitArgument recvOid m₁ callReturnTy₁ callReturnLabels₁ :: k₁ } s₁' :=
                                                                  Step.returnAwaitArgumentOk henf₁
                                                                have hstep₂ : Step gct₂ cct₂
                                                                    { heap := heap₂, env := env₂,
                                                                      control := .val v₂,
                                                                      continuation := .awaitArgument recvOid m₂ returnTy₂ returnLabels₂ :: k₂ } s₂' :=
                                                                  Step.returnAwaitArgumentOk henf₂
                                                                have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' := by
                                                                  refine ⟨hheap, ?_, .expr hbodyPrec, ?_⟩
                                                                  · simpa [s₁', s₂', hparamName, hrecvName] using
                                                                      (CheckedEnvPrecision.cons hval
                                                                        (CheckedEnvPrecision.cons hrecvPrec CheckedEnvPrecision.nil))
                                                                  · exact .cons (.enforce hmethodReturnPrec)
                                                                      (.cons (.enforce hret)
                                                                        (.cons (.returnTo henv) hcont_prec_tail))
                                                                exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                                                                  (checked_preservation hsafe₁' hstep₁)
                                                                  (checked_preservation hsafe₂' hstep₂) hprec'
                                                                  (fun h => by cases congrArg State.continuation h)
                                                              · let s₁' : State :=
                                                                  { heap := heap₁, env := env₁,
                                                                    control := .blame m₁.parameterLabels.direct, continuation := k₁ }
                                                                have hstep₁ : Step gct₁ cct₁
                                                                    { heap := heap₁, env := env₁,
                                                                      control := .val v₁,
                                                                      continuation := .awaitArgument recvOid m₁ callReturnTy₁ callReturnLabels₁ :: k₁ } s₁' :=
                                                                  Step.returnAwaitArgumentBlame henf₁
                                                                exact .leftBlame hstep₁ rfl .refl hsafe₂'
                                                                  (fun h => by cases congrArg State.continuation h)
                                      | _ =>
                                          cases hcont₂ with
                                          | cons hframe₂ _ =>
                                              cases hcont_prec with
                                              | cons hframe_prec _ =>
                                                  cases hframe_prec
                              | cond thenBr₁ elseBr₁ =>
                                  have w₁bool :
                                      CheckedValueWitness gct₁ cct₁ heap₁ v₁ (.class_ boolClass) := by
                                    cases hframe₁ with
                                    | cond _ _ =>
                                        simpa using w₁
                                  cases cont₂ with
                                  | nil =>
                                      cases hcont_prec
                                  | cons frame₂ k₂ =>
                                      cases hcont₂ with
                                      | cons hframe₂ hcont₂_tail =>
                                          cases hcont_prec with
                                          | cons hframe_prec hcont_prec_tail =>
                                              cases hframe_prec with
                                              | cond hthen helse =>
                                                  rename_i thenBr₂ elseBr₂
                                                  cases hval with
                                                  | objRef hheap' hlookVal₁ =>
                                                      rename_i oid obj₁
                                                      have w₁bool' :
                                                          CheckedValueWitness gct₁ cct₁ heap₁ (.objRef oid) (.class_ boolClass) := by
                                                        simpa using w₁bool
                                                      rcases boolClass_objRef_is_true_or_false w₁bool' hheapwf₁ hwfct₁ with htrue | hfalse
                                                      · subst htrue
                                                        let s₁' : State :=
                                                          { heap := heap₁, env := env₁,
                                                            control := .expr thenBr₁, continuation := k₁ }
                                                        let s₂' : State :=
                                                          { heap := heap₂, env := env₂,
                                                            control := .expr thenBr₂, continuation := k₂ }
                                                        have hstep₁ : Step gct₁ cct₁
                                                            { heap := heap₁, env := env₁,
                                                              control := .val (.objRef trueOid),
                                                              continuation := .cond thenBr₁ elseBr₁ :: k₁ } s₁' :=
                                                          Step.returnCondTrue
                                                        have hstep₂ : Step gct₂ cct₂
                                                            { heap := heap₂, env := env₂,
                                                              control := .val (.objRef trueOid),
                                                              continuation := .cond thenBr₂ elseBr₂ :: k₂ } s₂' :=
                                                          Step.returnCondTrue
                                                        have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                                                          ⟨hheap, henv, .expr hthen, hcont_prec_tail⟩
                                                        exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                                                          (checked_preservation hsafe₁' hstep₁)
                                                          (checked_preservation hsafe₂' hstep₂) hprec'
                                                          (fun h => by cases congrArg State.control h)
                                                      · subst hfalse
                                                        let s₁' : State :=
                                                          { heap := heap₁, env := env₁,
                                                            control := .expr elseBr₁, continuation := k₁ }
                                                        let s₂' : State :=
                                                          { heap := heap₂, env := env₂,
                                                            control := .expr elseBr₂, continuation := k₂ }
                                                        have hstep₁ : Step gct₁ cct₁
                                                            { heap := heap₁, env := env₁,
                                                              control := .val (.objRef falseOid),
                                                              continuation := .cond thenBr₁ elseBr₁ :: k₁ } s₁' :=
                                                          Step.returnCondFalse
                                                        have hstep₂ : Step gct₂ cct₂
                                                            { heap := heap₂, env := env₂,
                                                              control := .val (.objRef falseOid),
                                                              continuation := .cond thenBr₂ elseBr₂ :: k₂ } s₂' :=
                                                          Step.returnCondFalse
                                                        have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                                                          ⟨hheap, henv, .expr helse, hcont_prec_tail⟩
                                                        exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                                                          (checked_preservation hsafe₁' hstep₁)
                                                          (checked_preservation hsafe₂' hstep₂) hprec'
                                                          (fun h => by cases congrArg State.control h)
                              | returnTo callerEnv₁ =>
                                  cases cont₂ with
                                  | nil =>
                                      cases hcont_prec
                                  | cons frame₂ k₂ =>
                                      cases hcont₂ with
                                      | cons hframe₂ hcont₂_tail =>
                                          cases hcont_prec with
                                          | cons hframe_prec hcont_prec_tail =>
                                              cases hframe_prec with
                                              | returnTo hcallerEnv =>
                                                  rename_i callerEnv₂
                                                  let s₁' : State :=
                                                    { heap := heap₁, env := callerEnv₁,
                                                      control := .val v₁, continuation := k₁ }
                                                  let s₂' : State :=
                                                    { heap := heap₂, env := callerEnv₂,
                                                      control := .val v₂, continuation := k₂ }
                                                  have hstep₁ : Step gct₁ cct₁
                                                      { heap := heap₁, env := env₁,
                                                        control := .val v₁, continuation := .returnTo callerEnv₁ :: k₁ } s₁' :=
                                                    Step.returnFromBody
                                                  have hstep₂ : Step gct₂ cct₂
                                                      { heap := heap₂, env := env₂,
                                                        control := .val v₂, continuation := .returnTo callerEnv₂ :: k₂ } s₂' :=
                                                    Step.returnFromBody
                                                  have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                                                    ⟨hheap, hcallerEnv, .val hval, hcont_prec_tail⟩
                                                  exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                                                    (checked_preservation hsafe₁' hstep₁)
                                                    (checked_preservation hsafe₂' hstep₂) hprec'
                                                    (fun h => by cases congrArg State.continuation h)
                              | enforce c₁ labels₁ =>
                                  have hshape₁ := checkedValueWitness_toShape w₁
                                  have hlookup₁ :
                                      ∀ oid, v₁ = .objRef oid → ∃ obj, heap₁.lookup oid = some obj := by
                                    intro oid hv
                                    exact checkedAnyShape_objRef_lookup hshape₁ hv
                                  cases cont₂ with
                                  | nil =>
                                      cases hcont_prec
                                  | cons frame₂ k₂ =>
                                      cases hcont₂ with
                                      | cons hframe₂ hcont₂_tail =>
                                              cases hcont_prec with
                                                  | cons hframe_prec hcont_prec_tail =>
                                              cases hframe_prec with
                                                  | enforce hboundary =>
                                                  rename_i c₂ labels₂
                                                  have hframe₁Info :
                                                      WellFormedGTy gct₁ (interpTarget c₁) ∧
                                                      RuntimePublicCheckedTarget gct₁ c₁ := by
                                                    cases hframe₁ with
                                                    | enforce hwf hchecked =>
                                                        exact ⟨hwf, hchecked⟩
                                                  rcases hframe₁Info with
                                                    ⟨hwfOut₁, hcheckedOut₁⟩
                                                  have hframe₂Info :
                                                      WellFormedGTy gct₂ (interpTarget c₂) ∧
                                                      RuntimePublicCheckedTarget gct₂ c₂ := by
                                                    cases hframe₂ with
                                                    | enforce hwf hchecked =>
                                                        exact ⟨hwf, hchecked⟩
                                                  rcases hframe₂Info with
                                                    ⟨hwfOut₂, hcheckedOut₂⟩
                                                  rcases enforceValue_total
                                                      hheapwf₁ hwfct₁ (compileBoundaryTarget c₁) labels₁ v₁ hlookup₁ with
                                                    ⟨v₁', henf₁⟩ | henf₁
                                                  · have w₁' : CheckedValueWitness gct₁ cct₁ heap₁ v₁' c₁ :=
                                                      enforce_ok_has_checkedTargetWitness
                                                        henf₁
                                                        hshape₁
                                                        hheapwf₁
                                                        hwfct₁
                                                        halign₁
                                                        hcheckedOut₁
                                                        hwfOut₁
                                                    have hsame : v₁' = v₁ := enforce_ok_same_value henf₁
                                                    subst v₁'
                                                    have henf₂ :
                                                        EnforceValue gct₂ heap₂ v₂
                                                          (compileBoundaryTarget c₂) labels₂ (.ok v₂) :=
                                                      enforce_exists_under_precision
                                                        hct
                                                        hheapwf₂
                                                        hwfct₂
                                                        halign₂
                                                        hval
                                                        w₁'
                                                        hcheckedOut₂
                                                        hwfOut₂
                                                        hboundary
                                                        labels₂
                                                    let s₁' : State :=
                                                      { heap := heap₁, env := env₁, control := .val v₁, continuation := k₁ }
                                                    let s₂' : State :=
                                                      { heap := heap₂, env := env₂, control := .val v₂, continuation := k₂ }
                                                    have hstep₁ : Step gct₁ cct₁
                                                        { heap := heap₁, env := env₁,
                                                          control := .val v₁, continuation := .enforce c₁ labels₁ :: k₁ } s₁' :=
                                                      Step.returnEnforceOk henf₁
                                                    have hstep₂ : Step gct₂ cct₂
                                                        { heap := heap₂, env := env₂,
                                                          control := .val v₂, continuation := .enforce c₂ labels₂ :: k₂ } s₂' :=
                                                      Step.returnEnforceOk henf₂
                                                    have hprec' : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁' s₂' :=
                                                      ⟨hheap, henv, .val hval, hcont_prec_tail⟩
                                                    exact .continue hstep₁ (RuntimeSteps.single hstep₂)
                                                      (checked_preservation hsafe₁' hstep₁)
                                                      (checked_preservation hsafe₂' hstep₂) hprec'
                                                      (fun h => by cases congrArg State.continuation h)
                                                  · let s₁' : State :=
                                                      { heap := heap₁, env := env₁,
                                                        control := .blame labels₁.direct, continuation := k₁ }
                                                    have hstep₁ : Step gct₁ cct₁
                                                        { heap := heap₁, env := env₁,
                                                          control := .val v₁, continuation := .enforce c₁ labels₁ :: k₁ } s₁' :=
                                                      Step.returnEnforceBlame henf₁
                                                    exact .leftBlame hstep₁ rfl .refl hsafe₂'
                                                      (fun h => by cases congrArg State.continuation h)
theorem simulate_safe_steps_elaborated
    {gp₁ gp₂ : GProgram}
    {P₁ P₂ : GTy}
    {cp₁ cp₂ : CheckedProgram}
    {helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁}
    {helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂}
    (hct : ClassTableAnnotationPrecision gp₁.classes gp₂.classes)
    (hccShape : Forall₂ (ShapeClassPrecision gp₁.classes)
      (cp₁.classes.map eraseLabelsClass)
      (cp₂.classes.map eraseLabelsClass))
    (hsafe₁ : CheckedStateSafe gp₁.classes cp₁.classes
      s₁.heap s₁.env s₁.control s₁.continuation expectedType₁)
    (hsafe₂ : CheckedStateSafe gp₂.classes cp₂.classes
      s₂.heap s₂.env s₂.control s₂.continuation expectedType₂)
    (hprec : ElaboratedStatePrecision helab₁ helab₂ s₁ s₂)
    (hnotFinal₁ : finalResult? s₁ = none) :
    ElaboratedSimulationSegmentResult
      helab₁ helab₂ expectedType₁ expectedType₂ s₁ s₂ := by
  have hseg :=
    simulate_safe_steps hct hccShape hsafe₁ hsafe₂ hprec.state_prec hnotFinal₁
  cases hseg with
  | «continue» hstep₁ hpref₂ hsafe₁' hsafe₂' hstate hleftProgress =>
      exact .continue hstep₁ hpref₂ hsafe₁' hsafe₂'
        (hprec.of_step_steps hstep₁ hpref₂ hstate) hleftProgress
  | leftBlame hstep₁ hctrl₁' hpref₂ hsafe₂' hleftProgress =>
      exact .leftBlame hstep₁ hctrl₁' hpref₂ hsafe₂' hleftProgress

theorem dynamic_gradual_guarantee_at
    (hgp : ProgramTargetPrecision gp₁ gp₂)
    (helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁)
    (helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂)
    (hRoot : ProgramRootTargetInputPrecision P₁ P₂)
    (hwfct₁ : WellFormedGClassTableCore gp₁.classes)
    (hwfct₂ : WellFormedGClassTableCore gp₂.classes)
    (hsteps₁ : Steps gp₁.classes cp₁.classes (initialState cp₁) finalState₁)
    (hsteps₂ : Steps gp₂.classes cp₂.classes (initialState cp₂) finalState₂)
    (hfinal₁ : finalResult? finalState₁ = some (heap₁, result₁))
    (hfinal₂ : finalResult? finalState₂ = some (heap₂, result₂)) :
      CheckedOutcomePrecision gp₁.classes gp₂.classes cp₁.classes cp₂.classes
      (heap₁, result₁)
      (heap₂, result₂) := by
  let hct : ClassTableAnnotationPrecision gp₁.classes gp₂.classes :=
    classTableTargetPrecision_to_classTableAnnotationPrecision hgp.classes_prec
  have halign₁ : AlignedCheckedClassTable gp₁.classes cp₁.classes :=
    alignedCheckedClassTable_of_compiled hwfct₁ helab₁.classes_elab
  have halign₂ : AlignedCheckedClassTable gp₂.classes cp₂.classes :=
    alignedCheckedClassTable_of_compiled hwfct₂ helab₂.classes_elab
  have hinit :=
    initial_elaborated_state_precision hgp helab₁ helab₂ hRoot
  have hccShape :
      Forall₂ (ShapeClassPrecision gp₁.classes)
        (cp₁.classes.map eraseLabelsClass)
        (cp₂.classes.map eraseLabelsClass) := by
    simpa [CheckedProgramPrecision, eraseLabelsProgram] using hinit.program_prec.classes_prec
  have hsafe_init₁ :
      CheckedStateSafe gp₁.classes cp₁.classes
        (initialState cp₁).heap
        (initialState cp₁).env
        (initialState cp₁).control
        (initialState cp₁).continuation
        (runtimePublicTy P₁) :=
    compiled_initial_safe_from_elaboration_at helab₁
  have hsafe_init₂ :
      CheckedStateSafe gp₂.classes cp₂.classes
        (initialState cp₂).heap
        (initialState cp₂).env
        (initialState cp₂).control
        (initialState cp₂).continuation
        (runtimePublicTy P₂) :=
    compiled_initial_safe_from_elaboration_at helab₂
  have hprec_init :
      ElaboratedStatePrecision helab₁ helab₂
        (initialState cp₁)
        (initialState cp₂) :=
    hinit.elaborated_prec
  have hsim :
      ∀ {s₁ s₂},
        CheckedStateSafe gp₁.classes cp₁.classes
          s₁.heap s₁.env s₁.control s₁.continuation
          (runtimePublicTy P₁) →
        CheckedStateSafe gp₂.classes cp₂.classes
          s₂.heap s₂.env s₂.control s₂.continuation
          (runtimePublicTy P₂) →
        ElaboratedStatePrecision helab₁ helab₂ s₁ s₂ →
        Steps gp₂.classes cp₂.classes s₂ finalState₂ →
        (hsteps₁ : Steps gp₁.classes cp₁.classes s₁ finalState₁) →
        CheckedOutcomePrecision gp₁.classes gp₂.classes cp₁.classes cp₂.classes
          (heap₁, result₁)
          (heap₂, result₂) := by
    intro s₁ s₂ hsafe₁ hsafe₂ hprec hsteps₂ hsteps₁
    induction hsteps₁ generalizing s₂ with
    | refl =>
        obtain ⟨out₂, hfinal₂_cur, hprec_out⟩ :=
          hprec.final_right hfinal₁
        have hs₂eq : finalState₂ = s₂ := by
          exact steps_final_eq hsteps₂ ⟨_, hfinal₂⟩ .refl ⟨_, hfinal₂_cur⟩
        subst hs₂eq
        have hout₂ : out₂ = (heap₂, result₂) := by
          rw [hfinal₂_cur] at hfinal₂
          exact Option.some.inj hfinal₂
        subst hout₂
        simpa using hprec_out
    | @step s₁ s₁' sfinal hs₁ hrest ih =>
        have hnotFinal₁ : finalResult? s₁ = none := by
          cases hfinal₁_cur : finalResult? s₁ with
          | none =>
              rfl
          | some out =>
              exact (final_states_do_not_step hfinal₁_cur hs₁).elim
        have hseg :=
          simulate_safe_steps_elaborated hct hccShape hsafe₁ hsafe₂
            hprec hnotFinal₁
        cases hseg with
        | «continue» hstep₁ hpref₂ hsafe₁' hsafe₂' hprec' hleftProgress =>
            rename_i s₁' s₂'
            cases step_deterministic hs₁ hstep₁
            have hsteps₂' := steps_split_via_determinism hpref₂ hsteps₂ hfinal₂
            exact ih hsteps₁ hfinal₁ hsafe₁' hsafe₂' hprec' hsteps₂'
        | leftBlame hstep₁ hctrl₁' hpref₂ hsafe₂_cur hleftProgress =>
            cases step_deterministic hs₁ hstep₁
            have hsafe₁' :
                CheckedStateSafe gp₁.classes cp₁.classes
                  _ _ _ _
                  (runtimePublicTy P₁) :=
              checked_preservation hsafe₁ hs₁
            obtain ⟨ℓ, hblame_final⟩ :=
              blame_steps_final hsafe₁' hctrl₁' hrest hfinal₁
            have hright :=
              checked_safe_execution_result hsafe₂_cur hsteps₂ hfinal₂
            cases hright with
            | inl hsucc =>
                rcases hsucc with ⟨v₂, hv₂, hw₂⟩
                rw [hblame_final, hv₂]
                exact .blame_success
            | inr hblame =>
                rcases hblame with ⟨ℓ₂, hℓ₂⟩
                rw [hblame_final, hℓ₂]
                exact .blame_blame
  exact hsim hsafe_init₁ hsafe_init₂ hprec_init hsteps₂ hsteps₁

theorem dynamic_gradual_guarantee
    (hgp : ProgramTargetPrecision gp₁ gp₂)
    (helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁)
    (helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂)
    (hRoot : ProgramRootTargetInputPrecision P₁ P₂)
    (hwfct₁ : WellFormedGClassTableCore gp₁.classes)
    (hwfct₂ : WellFormedGClassTableCore gp₂.classes)
    (hsteps₁ : Steps gp₁.classes cp₁.classes (initialState cp₁) finalState₁)
    (hsteps₂ : Steps gp₂.classes cp₂.classes (initialState cp₂) finalState₂)
    (hfinal₁ : finalResult? finalState₁ = some (heap₁, result₁))
    (hfinal₂ : finalResult? finalState₂ = some (heap₂, result₂)) :
    CheckedOutcomePrecision gp₁.classes gp₂.classes cp₁.classes cp₂.classes
      (heap₁, result₁)
      (heap₂, result₂) :=
  dynamic_gradual_guarantee_at
    hgp helab₁ helab₂ hRoot hwfct₁ hwfct₂ hsteps₁ hsteps₂ hfinal₁ hfinal₂

end Checked
