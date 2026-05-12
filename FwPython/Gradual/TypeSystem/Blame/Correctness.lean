import FwPython.Gradual.TypeSystem.Blame.Provenance

/-! # Blame correctness

This file refines blame provenance with the Castagna-style owner
computation for each compiled boundary origin. -/

namespace Checked

theorem compiled_boundary_origin_expectedOwner
    (hcompiled : ElaboratesProgramAt gp P cp)
    (horig : CompiledBoundaryOrigin hcompiled origin ℓ) :
    BoundaryOrigin.expectedOwner origin = ℓ.owner := by
  cases origin with
  | mainEnforce exprPath c p =>
      rcases horig with ⟨e, labels, hnode, hlabel⟩
      have hnode' :
          (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPath =
            some (.enforce e c labels) := by
        simpa [hcompiled.main_eq] using hnode
      obtain ⟨k, hk⟩ := compileCheck_enforce_labels_form .main hcompiled.main_hsrc hnode'
      simp [BoundaryOrigin.expectedOwner]
      rw [hlabel, hk, mkBoundaryLabels_at_owner (compileBoundaryTarget c) p .main .positive k]
  | mainDynAttr exprPath =>
      rcases horig with ⟨e, attr, hnode⟩
      have hnode' :
          (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPath =
            some (.dynAttrAccess e attr ℓ) := by
        simpa [hcompiled.main_eq] using hnode
      obtain ⟨k, hk⟩ := compileCheck_dynAttr_label_form .main hcompiled.main_hsrc hnode'
      simp [BoundaryOrigin.expectedOwner]
      rw [hk, freshLabel_owner (scope := .main) (owner := .context) (n := k)]
  | mainCallReturn exprPath c p =>
      rcases horig with ⟨callee, arg, paramTy, labels, hnode, hlabel⟩
      have hnode' :
          (compileCheck .main hcompiled.main_hsrc [] P 0).1.nodeAt exprPath =
            some (.call callee arg paramTy c labels) := by
        simpa [hcompiled.main_eq] using hnode
      obtain ⟨k, hlabels⟩ :=
        compileCheck_call_return_labels_form .main hcompiled.main_hsrc hnode'
      have hlabel' : ℓ = labels.at p := by
        simpa using hlabel
      simp [BoundaryOrigin.expectedOwner]
      rw [hlabel', hlabels,
        mkBoundaryLabels_at_owner (compileBoundaryTarget c) p .main .positive k]
  | methodParameter definerName methodName c p =>
      rcases horig with ⟨cc, gm, cm, hfc, hmem, hcm, hc, hname, hlabel⟩
      cases hc
      have hcontract : cm.parameterContract = compileBoundaryRaw gm.paramTy := by
        simpa [hcm.paramTy_eq] using hcm.paramContract_eq
      simp [BoundaryOrigin.expectedOwner]
      rw [hlabel]
      symm
      calc
        (cm.parameterLabels.at p).owner
            = ((cast (congrArg BoundaryLabels hcontract) cm.parameterLabels).at
                (cast (congrArg BoundaryPath hcontract) p)).owner := by
                  simpa using congrArg Label.owner
                    (BoundaryLabels.at_cast hcontract cm.parameterLabels p).symm
        _ = (((mkBoundaryLabels (.methodParameter definerName gm.name) .negative
                (compileBoundaryRaw gm.paramTy) 0).1).at
              (cast (congrArg BoundaryPath hcontract) p)).owner := by
                rw [show cast (congrArg BoundaryLabels hcontract) cm.parameterLabels =
                    (mkBoundaryLabels (.methodParameter definerName gm.name) .negative
                      (compileBoundaryRaw gm.paramTy) 0).1 by
                    simpa using hcm.parameterLabels_eq]
        _ = (cast (congrArg BoundaryPath hcontract) p).ownerFrom .negative := by
              simpa using
                mkBoundaryLabels_at_owner (compileBoundaryRaw gm.paramTy)
                  (cast (congrArg BoundaryPath hcontract) p)
                  (.methodParameter definerName gm.name) .negative 0
        _ = p.ownerFrom .negative := by
              simpa using (BoundaryPath.ownerFrom_cast hcontract .negative p)
  | methodReturn definerName methodName c p =>
      rcases horig with ⟨cc, gm, cm, hfc, hmem, hcm, hc, hname, hlabel⟩
      cases hc
      have hcontract : cm.returnContract = compileBoundaryRaw gm.returnTy := by
        simpa [hcm.returnTy_eq] using hcm.returnContract_eq
      simp [BoundaryOrigin.expectedOwner]
      rw [hlabel]
      symm
      calc
        (cm.returnLabels.at p).owner
            = ((cast (congrArg BoundaryLabels hcontract) cm.returnLabels).at
                (cast (congrArg BoundaryPath hcontract) p)).owner := by
                  simpa using congrArg Label.owner
                    (BoundaryLabels.at_cast hcontract cm.returnLabels p).symm
        _ = (((mkBoundaryLabels (.methodReturn definerName gm.name) .positive
                (compileBoundaryRaw gm.returnTy) 0).1).at
              (cast (congrArg BoundaryPath hcontract) p)).owner := by
                rw [show cast (congrArg BoundaryLabels hcontract) cm.returnLabels =
                    (mkBoundaryLabels (.methodReturn definerName gm.name) .positive
                      (compileBoundaryRaw gm.returnTy) 0).1 by
                    simpa using hcm.returnLabels_eq]
        _ = (cast (congrArg BoundaryPath hcontract) p).ownerFrom .positive := by
              simpa using
                mkBoundaryLabels_at_owner (compileBoundaryRaw gm.returnTy)
                  (cast (congrArg BoundaryPath hcontract) p)
                  (.methodReturn definerName gm.name) .positive 0
        _ = p.ownerFrom .positive := by
              simpa using (BoundaryPath.ownerFrom_cast hcontract .positive p)
  | methodBodyEnforce definerName methodName exprPath c p =>
      rcases horig with ⟨cc, gm, cm, e, labels, hfc, hmem, hcm, hname, hnode, hlabel⟩
      obtain ⟨_, _, hsrc, hbody⟩ := hcm.body_compiled
      have hnode' :
          (compileCheck (.methodBody definerName methodName) hsrc
            [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
            gm.returnTy 0).1.nodeAt exprPath =
            some (.enforce e c labels) := by
        simpa [hbody, hname] using hnode
      obtain ⟨k, hk⟩ :=
        compileCheck_enforce_labels_form (.methodBody definerName methodName) hsrc hnode'
      simp [BoundaryOrigin.expectedOwner]
      rw [hlabel, hk,
        mkBoundaryLabels_at_owner (compileBoundaryTarget c) p
          (.methodBody definerName methodName) .positive k]
  | methodBodyDynAttr definerName methodName exprPath =>
      rcases horig with ⟨cc, gm, cm, e, attr, hfc, hmem, hcm, hname, hnode⟩
      obtain ⟨_, _, hsrc, hbody⟩ := hcm.body_compiled
      have hnode' :
          (compileCheck (.methodBody definerName methodName) hsrc
            [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
            gm.returnTy 0).1.nodeAt exprPath =
            some (.dynAttrAccess e attr ℓ) := by
        simpa [hbody, hname] using hnode
      obtain ⟨k, hk⟩ :=
        compileCheck_dynAttr_label_form (.methodBody definerName methodName) hsrc hnode'
      simp [BoundaryOrigin.expectedOwner]
      rw [hk, freshLabel_owner (scope := .methodBody definerName methodName)
        (owner := .context) (n := k)]
  | methodBodyCallReturn definerName methodName exprPath c p =>
      rcases horig with ⟨cc, gm, cm, callee, arg, paramTy, labels,
        hfc, hmem, hcm, hname, hnode, hlabel⟩
      obtain ⟨_, _, hsrc, hbody⟩ := hcm.body_compiled
      have hnode' :
          (compileCheck (.methodBody definerName methodName) hsrc
            [(gm.param, gm.paramTy), (gm.receiverParam, .class_ definerName)]
            gm.returnTy 0).1.nodeAt exprPath =
            some (.call callee arg paramTy c labels) := by
        simpa [hbody, hname] using hnode
      obtain ⟨k, hlabels⟩ := compileCheck_call_return_labels_form
        (.methodBody definerName methodName) hsrc hnode'
      have hlabel' : ℓ = labels.at p := by
        simpa using hlabel
      simp [BoundaryOrigin.expectedOwner]
      rw [hlabel', hlabels,
        mkBoundaryLabels_at_owner (compileBoundaryTarget c) p
          (.methodBody definerName methodName) .positive k]

theorem gradual_blame_correctness_at
    (hcompiled : ElaboratesProgramAt gp P cp)
    (hsteps : Checked.Steps gp.classes cp.classes (initialState cp) finalState)
    (hfinal : finalResult? finalState = some (heap', .blame ℓ)) :
    ∃ origin, CompiledBoundaryOrigin hcompiled origin ℓ ∧
      BoundaryOrigin.expectedOwner origin = ℓ.owner := by
  obtain ⟨origin, horig⟩ := gradual_blame_provenance_at hcompiled hsteps hfinal
  exact ⟨origin, horig, compiled_boundary_origin_expectedOwner hcompiled horig⟩

end Checked
