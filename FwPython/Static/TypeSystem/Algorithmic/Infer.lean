import FwPython.Static.TypeSystem.Algorithmic.Attr
import FwPython.Static.TypeSystem.Algorithmic.Call
import FwPython.Static.TypeSystem.Algorithmic.Basis

/-! ## Expression type inference

Inference computes a finite set of candidates that is sufficient for every
declarative result type. It constructs valid packages and closes them under
nonempty intersection to cover combined typings. The checker accepts a
requested type when one candidate is below it, using the validity proofs
carried by both packages for the comparison.
-/

open FwPython.Static.Subtyping

variable {ct : ClassTable} {structural : WellFormedClassHierarchy ct}

/-! ### Searching for a `Bool` witness in a basis

The cond cases require that the condition's basis contain at least one type
subtype of `Bool`. `findBoolWitness` decides this and produces a witness. -/

/-- Find a valid candidate that is a subtype of Bool. -/
def findBoolWitness (structural : WellFormedClassHierarchy ct)
    (basis : List (WellFormedType (ct.map ClassDecl.name))) :
    Option { S // S ∈ basis ∧ IsSubtype structural S.raw (.class_ boolClass) } :=
  match basis with
  | [] => none
  | S :: rest =>
      letI : Decidable (IsSubtype structural S.raw (.class_ boolClass)) :=
        WellFormedType.subtypeDecidable structural S (WellFormedTy.bool structural).toType
      if accepted : IsSubtype structural S.raw (.class_ boolClass) then
        some ⟨S, List.mem_cons_self .., accepted⟩
      else
        match findBoolWitness structural rest with
        | none => none
        | some ⟨T, member, included⟩ => some ⟨T, .tail _ member, included⟩

/-- A Bool-compatible candidate makes the witness search succeed. -/
theorem findBoolWitness_some_of_match (structural : WellFormedClassHierarchy ct)
    (hcond : S ∈ basis) (hbool : IsSubtype structural S.raw (.class_ boolClass)) :
    ∃ witness, findBoolWitness structural basis = some witness := by
  induction basis with
  | nil => cases hcond
  | cons T rest ih =>
      letI : Decidable (IsSubtype structural T.raw (.class_ boolClass)) :=
        WellFormedType.subtypeDecidable structural T (WellFormedTy.bool structural).toType
      by_cases included : IsSubtype structural T.raw (.class_ boolClass)
      · exact ⟨⟨T, .head _, included⟩, by simp [findBoolWitness, included]⟩
      · rcases List.mem_cons.mp hcond with rfl | member
        · exact (included hbool).elim
        · obtain ⟨⟨U, listed, compatible⟩, found⟩ := ih member
          exact ⟨⟨U, .tail _ listed, compatible⟩, by simp [findBoolWitness, included, found]⟩

/-! ### Per-construct candidate packages

Each expression constructor computes valid candidates.
Soundness is stated on these packages; their raw fields supply the annotations
used by declarative typing. -/

/-- A visible binding supplies its annotation and validity proof together. -/
private def varTypes (Γ : TyEnv) (valid : WellFormedTyEnv ct Γ) (x : Identifier) :
    List (WellFormedType (ct.map ClassDecl.name)) :=
  ((Γ.lookup x).attach.map fun entry => (valid x entry.1 entry.2).toType).toList

/-- A variable has the annotation of every candidate from its visible binding. -/
private theorem varTypes_sound (valid : WellFormedTyEnv ct Γ)
    (member : type ∈ varTypes Γ valid x) : HasType structural Γ (.var x) type.raw := by
  cases looked : Γ.lookup x with
  | none => simp [varTypes, looked] at member
  | some annotation =>
      simp [varTypes, Option.attach_eq_some _ ⟨annotation, looked⟩] at member
      cases member
      exact .var looked

/-- Return a declared class type unless it is one of the three non-instantiable builtins. -/
private def newTypes (ct : ClassTable) (cname : Identifier) :
    List (WellFormedType (ct.map ClassDecl.name)) :=
  match (findClass ct cname).attach with
  | none => []
  | some ⟨_, found⟩ =>
      if cname = boolClass ∨ cname = noneClass ∨ cname = boundMethodClass then []
      else [(WellFormedTy.class_of_lookup found).toType]

/-- Each constructor candidate names a declared, instantiable class. -/
private theorem newTypes_sound (member : type ∈ newTypes ct cname) :
    HasType structural Γ (.new cname) type.raw := by
  cases found : findClass ct cname with
  | none => simp [newTypes, Option.attach_eq_none_iff.mpr found] at member
  | some declaration =>
      by_cases excluded : cname = boolClass ∨ cname = noneClass ∨ cname = boundMethodClass
      · simp [newTypes, Option.attach_eq_some _ ⟨declaration, found⟩, excluded] at member
      · simp [newTypes, Option.attach_eq_some _ ⟨declaration, found⟩, excluded] at member
        cases member
        exact .new found (fun h => excluded (.inl h))
          (fun h => excluded (.inr (.inl h))) (fun h => excluded (.inr (.inr h)))

/-- The valid Bool result of a class test with an existing variable and class. -/
private def isInstanceTypes (structural : WellFormedClassHierarchy ct)
    (Γ : TyEnv) (x C : Identifier) : List (WellFormedType (ct.map ClassDecl.name)) :=
  match Γ.lookup x, findClass ct C with
  | some _, some _ => [(WellFormedTy.bool structural).toType]
  | _, _ => []

/-- Each class-test candidate has the Bool result required by the typing rule. -/
private theorem isInstanceTypes_sound
    (member : type ∈ isInstanceTypes structural Γ x C) :
    HasType structural Γ (.isInstance x C) type.raw := by
  cases looked : Γ.lookup x with
  | none => simp [isInstanceTypes, looked] at member
  | some _ =>
      cases found : findClass ct C with
      | none => simp [isInstanceTypes, looked, found] at member
      | some _ =>
          simp [isInstanceTypes, looked, found] at member
          cases member
          exact .isInstance looked found

/-- Valid attribute results from the inferred receiver types. -/
private def attrAccessTypes (hwfct : WellTypedClassHierarchy ct)
    (baseBasis : InferredBasis hwfct.toWellFormedClassHierarchy Γ base) (attr : Identifier) :
    List (WellFormedType (ct.map ClassDecl.name)) :=
  baseBasis.types.flatMap fun receiver => attrResultsFromTy hwfct receiver attr

/-- Every attribute candidate comes from a typed receiver and its selected method. -/
private theorem attrAccessTypes_sound (hwfct : WellTypedClassHierarchy ct)
    (baseBasis : InferredBasis hwfct.toWellFormedClassHierarchy Γ base)
    (member : type ∈ attrAccessTypes hwfct baseBasis attr) :
    HasType hwfct.toWellFormedClassHierarchy Γ (.attrAccess base attr) type.raw := by
  obtain ⟨receiver, listed, selected⟩ := List.mem_flatMap.mp member
  exact attrResultsFromTy_sound hwfct receiver selected (baseBasis.types_sound listed)

/-- Valid call results from the inferred callee and argument types. -/
private def callTypes (hwfct : WellTypedClassHierarchy ct)
    (calleeBasis : InferredBasis hwfct.toWellFormedClassHierarchy Γ callee)
    (argBasis : InferredBasis hwfct.toWellFormedClassHierarchy Γ arg) :
    List (WellFormedType (ct.map ClassDecl.name)) :=
  calleeBasis.types.flatMap fun callee =>
    callResultsFromTy hwfct.toWellFormedClassHierarchy callee argBasis.types

/-- Each call candidate has a typed function requirement and an accepted argument. -/
private theorem callTypes_sound (hwfct : WellTypedClassHierarchy ct)
    (calleeBasis : InferredBasis hwfct.toWellFormedClassHierarchy Γ callee)
    (argBasis : InferredBasis hwfct.toWellFormedClassHierarchy Γ arg)
    (member : type ∈ callTypes hwfct calleeBasis argBasis) :
    HasType hwfct.toWellFormedClassHierarchy Γ (.call callee arg) type.raw := by
  obtain ⟨callee, listed, selected⟩ := List.mem_flatMap.mp member
  exact callResultsFromTy_sound callee selected (calleeBasis.types_sound listed)
    (fun _ member => argBasis.types_sound member)

/-- Form the valid union for every pair of branch candidates. -/
private def pairwiseUnionTypes (left right : List (WellFormedType names)) : List (WellFormedType names) :=
  left.flatMap fun first => right.map (WellFormedType.union first)

/-- A union candidate pairs one type from each branch. -/
private theorem mem_pairwiseUnionTypes :
    type ∈ pairwiseUnionTypes left right ↔
      ∃ first ∈ left, ∃ second ∈ right, WellFormedType.union first second = type := by
  simp [pairwiseUnionTypes]

/-- Valid union candidates for a conditional whose condition has a Bool-compatible type. -/
private def ordinaryCondTypes (hwfct : WellTypedClassHierarchy ct)
    (condBasis : InferredBasis hwfct.toWellFormedClassHierarchy Γ condExpr)
    (thenBasis : InferredBasis hwfct.toWellFormedClassHierarchy Γ thenBr)
    (elseBasis : InferredBasis hwfct.toWellFormedClassHierarchy Γ elseBr) :
    List (WellFormedType (ct.map ClassDecl.name)) :=
  match findBoolWitness hwfct.toWellFormedClassHierarchy condBasis.types with
  | some _ => pairwiseUnionTypes thenBasis.types elseBasis.types
  | none => []

/-- The typing rule combines the condition witness and the two branch candidates. -/
private theorem ordinaryCondTypes_sound (hwfct : WellTypedClassHierarchy ct)
    (condBasis : InferredBasis hwfct.toWellFormedClassHierarchy Γ condExpr)
    (thenBasis : InferredBasis hwfct.toWellFormedClassHierarchy Γ thenBr)
    (elseBasis : InferredBasis hwfct.toWellFormedClassHierarchy Γ elseBr)
    (member : type ∈ ordinaryCondTypes hwfct condBasis thenBasis elseBasis) :
    HasType hwfct.toWellFormedClassHierarchy Γ (.cond condExpr thenBr elseBr) type.raw := by
  unfold ordinaryCondTypes at member
  cases found : findBoolWitness hwfct.toWellFormedClassHierarchy condBasis.types with
  | none => simp [found] at member
  | some witness =>
      rw [found] at member
      obtain ⟨first, firstMember, second, secondMember, rfl⟩ := mem_pairwiseUnionTypes.mp member
      exact .cond (condBasis.types_sound witness.2.1) witness.2.2
        (thenBasis.types_sound firstMember) (elseBasis.types_sound secondMember)

/-- A Bool-compatible condition and two branch candidates give a union candidate. -/
private theorem ordinaryCondTypes_mem_of_witness (hwfct : WellTypedClassHierarchy ct)
    (condBasis : InferredBasis hwfct.toWellFormedClassHierarchy Γ condExpr)
    (thenBasis : InferredBasis hwfct.toWellFormedClassHierarchy Γ thenBr)
    (elseBasis : InferredBasis hwfct.toWellFormedClassHierarchy Γ elseBr)
    (condition : conditionType ∈ condBasis.types)
    (accepted : IsSubtype hwfct.toWellFormedClassHierarchy conditionType.raw (.class_ boolClass))
    (first : firstType ∈ thenBasis.types) (second : secondType ∈ elseBasis.types) :
    WellFormedType.union firstType secondType ∈ ordinaryCondTypes hwfct condBasis thenBasis elseBasis := by
  obtain ⟨_, found⟩ := findBoolWitness_some_of_match hwfct.toWellFormedClassHierarchy condition accepted
  unfold ordinaryCondTypes
  rw [found]
  exact mem_pairwiseUnionTypes.mpr ⟨firstType, first, secondType, second, rfl⟩

/-! ### Class-test conditionals

A condition `isInstance x C` refines x's type in both branches.
The then-branch requires `T & class_ C`; the else-branch requires `T & negClass C`.
Inference computes valid candidates in these environments and pairs their results. -/

/-- Valid union candidates from the two class-test branch environments. -/
private def specializedCondTypes
    (Γ : TyEnv) (x C : Identifier) (thenBr elseBr : Expr)
    (mkThen : (T : Ty) → Γ.lookup x = some T →
              (cls : Class) → findClass ct C = some cls →
              InferredBasis structural (Γ.update x (.intersection T (.class_ C))) thenBr)
    (mkElse : (T : Ty) → Γ.lookup x = some T →
              (cls : Class) → findClass ct C = some cls →
              InferredBasis structural (Γ.update x (.intersection T (.negClass C))) elseBr) :
    List (WellFormedType (ct.map ClassDecl.name)) :=
  match (Γ.lookup x).attach with
  | none => []
  | some ⟨T, looked⟩ =>
      match (findClass ct C).attach with
      | none => []
      | some ⟨cls, found⟩ =>
          pairwiseUnionTypes (mkThen T looked cls found).types (mkElse T looked cls found).types

/-- Class-test candidates combine types proved in the two refined environments. -/
private theorem specializedCondTypes_sound
    {mkThen : (T : Ty) → Γ.lookup x = some T →
      (cls : Class) → findClass ct C = some cls →
      InferredBasis structural (Γ.update x (.intersection T (.class_ C))) thenBr}
    {mkElse : (T : Ty) → Γ.lookup x = some T →
      (cls : Class) → findClass ct C = some cls →
      InferredBasis structural (Γ.update x (.intersection T (.negClass C))) elseBr}
    (member : type ∈ specializedCondTypes Γ x C thenBr elseBr mkThen mkElse) :
    HasType structural Γ (.cond (.isInstance x C) thenBr elseBr) type.raw := by
  revert member
  unfold specializedCondTypes
  cases (Γ.lookup x).attach with
  | none => intro member; simp at member
  | some binding =>
      obtain ⟨annotation, looked⟩ := binding
      cases (findClass ct C).attach with
      | none => intro member; simp at member
      | some selected =>
          obtain ⟨declaration, found⟩ := selected
          intro member
          obtain ⟨first, firstMember, second, secondMember, rfl⟩ := mem_pairwiseUnionTypes.mp member
          exact .condIsInstance looked found
            ((mkThen annotation looked declaration found).types_sound firstMember)
            ((mkElse annotation looked declaration found).types_sound secondMember)

/-- Two candidates in the refined branches supply their union to the conditional. -/
private theorem specializedCondTypes_mem_of_witness
    {mkThen : (T : Ty) → Γ.lookup x = some T →
      (cls : Class) → findClass ct C = some cls →
      InferredBasis structural (Γ.update x (.intersection T (.class_ C))) thenBr}
    {mkElse : (T : Ty) → Γ.lookup x = some T →
      (cls : Class) → findClass ct C = some cls →
      InferredBasis structural (Γ.update x (.intersection T (.negClass C))) elseBr}
    (looked : Γ.lookup x = some annotation) (found : findClass ct C = some declaration)
    (first : firstType ∈ (mkThen annotation looked declaration found).types)
    (second : secondType ∈ (mkElse annotation looked declaration found).types) :
    WellFormedType.union firstType secondType ∈ specializedCondTypes Γ x C thenBr elseBr mkThen mkElse := by
  unfold specializedCondTypes
  rw [Option.attach_eq_some _ ⟨annotation, looked⟩, Option.attach_eq_some _ ⟨declaration, found⟩]
  exact mem_pairwiseUnionTypes.mpr ⟨firstType, first, secondType, second, rfl⟩

/-! ### Main inference dispatcher -/

/-- Compute valid candidates and prove their expression typing together. -/
def inferBasis (hwfct : WellTypedClassHierarchy ct)
    (Γ : TyEnv) (hΓwf : WellFormedTyEnv ct Γ) :
    (e : Expr) → InferredBasis hwfct.toWellFormedClassHierarchy Γ e
  | .var x => ⟨varTypes Γ hΓwf x, fun _ member => varTypes_sound hΓwf member⟩
  | .new name => ⟨newTypes ct name, fun _ member => newTypes_sound member⟩
  | .attrAccess base attr =>
      let baseBasis := inferBasis hwfct Γ hΓwf base
      ⟨attrAccessTypes hwfct baseBasis attr, fun _ member => attrAccessTypes_sound hwfct baseBasis member⟩
  | .call callee arg =>
      let calleeBasis := inferBasis hwfct Γ hΓwf callee
      let argBasis := inferBasis hwfct Γ hΓwf arg
      ⟨callTypes hwfct calleeBasis argBasis, fun _ member => callTypes_sound hwfct calleeBasis argBasis member⟩
  | .constNone =>
      ⟨[(WellFormedTy.none hwfct.toWellFormedClassHierarchy).toType], fun _ member => by
        cases List.mem_singleton.mp member
        exact .constNone⟩
  | .constTrue =>
      ⟨[(WellFormedTy.bool hwfct.toWellFormedClassHierarchy).toType], fun _ member => by
        cases List.mem_singleton.mp member
        exact .constTrue⟩
  | .constFalse =>
      ⟨[(WellFormedTy.bool hwfct.toWellFormedClassHierarchy).toType], fun _ member => by
        cases List.mem_singleton.mp member
        exact .constFalse⟩
  | .cond (.isInstance x C) thenBr elseBr =>
      let condBasis := inferBasis hwfct Γ hΓwf (.isInstance x C)
      let thenBasis := inferBasis hwfct Γ hΓwf thenBr
      let elseBasis := inferBasis hwfct Γ hΓwf elseBr
      let mkThen := fun (T : Ty) (looked : Γ.lookup x = some T)
          (cls : Class) (found : findClass ct C = some cls) =>
        inferBasis hwfct (Γ.update x (.intersection T (.class_ C)))
          (wellFormedTyEnv_update_class hΓwf looked found) thenBr
      let mkElse := fun (T : Ty) (looked : Γ.lookup x = some T)
          (cls : Class) (found : findClass ct C = some cls) =>
        inferBasis hwfct (Γ.update x (.intersection T (.negClass C)))
          (wellFormedTyEnv_update_negClass hΓwf looked found) elseBr
      ⟨ordinaryCondTypes hwfct condBasis thenBasis elseBasis ++
        specializedCondTypes Γ x C thenBr elseBr mkThen mkElse, fun _ member => by
          rcases List.mem_append.mp member with ordinary | specialized
          · exact ordinaryCondTypes_sound hwfct condBasis thenBasis elseBasis ordinary
          · exact specializedCondTypes_sound specialized⟩
  | .cond condition thenBr elseBr =>
      let condBasis := inferBasis hwfct Γ hΓwf condition
      let thenBasis := inferBasis hwfct Γ hΓwf thenBr
      let elseBasis := inferBasis hwfct Γ hΓwf elseBr
      ⟨ordinaryCondTypes hwfct condBasis thenBasis elseBasis,
        fun _ member => ordinaryCondTypes_sound hwfct condBasis thenBasis elseBasis member⟩
  | .isInstance x C =>
      ⟨isInstanceTypes hwfct.toWellFormedClassHierarchy Γ x C, fun _ member => isInstanceTypes_sound member⟩

/-- A visible variable supplies its validated annotation. -/
@[simp] theorem inferBasis_var_eq
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hlook : Γ.lookup x = some T) :
    (inferBasis hwfct Γ hΓwf (.var x)).types = [(hΓwf x T hlook).toType] := by
  simp [inferBasis, varTypes, Option.attach_eq_some _ ⟨_, hlook⟩, WellFormedTy.toType]

/-- The None constant supplies the validated NoneType annotation. -/
@[simp] theorem inferBasis_constNone_eq
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ) :
    (inferBasis hwfct Γ hΓwf .constNone).types =
      [(WellFormedTy.none hwfct.toWellFormedClassHierarchy).toType] := by
  simp [inferBasis, WellFormedTy.toType]

/-- The True constant supplies the validated Bool annotation. -/
@[simp] theorem inferBasis_constTrue_eq
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ) :
    (inferBasis hwfct Γ hΓwf .constTrue).types =
      [(WellFormedTy.bool hwfct.toWellFormedClassHierarchy).toType] := by
  simp [inferBasis, WellFormedTy.toType]

/-- The False constant supplies the validated Bool annotation. -/
@[simp] theorem inferBasis_constFalse_eq
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ) :
    (inferBasis hwfct Γ hΓwf .constFalse).types =
      [(WellFormedTy.bool hwfct.toWellFormedClassHierarchy).toType] := by
  simp [inferBasis, WellFormedTy.toType]

/-- An instantiable declaration supplies its validated class annotation. -/
@[simp] theorem inferBasis_new_eq
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hfind : findClass ct cname = some cls)
    (hbool : cname ≠ boolClass)
    (hnone : cname ≠ noneClass)
    (hbm : cname ≠ boundMethodClass) :
    (inferBasis hwfct Γ hΓwf (.new cname)).types =
      [(WellFormedTy.class_of_lookup hfind).toType] := by
  simp [inferBasis, newTypes, Option.attach_eq_some _ ⟨_, hfind⟩, hbool, hnone, hbm,
    WellFormedTy.toType]

/-- A class test supplies the validated Bool annotation. -/
@[simp] theorem inferBasis_isInstance_eq
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hlook : Γ.lookup x = some T)
    (hfind : findClass ct C = some cls) :
    (inferBasis hwfct Γ hΓwf (.isInstance x C)).types =
      [(WellFormedTy.bool hwfct.toWellFormedClassHierarchy).toType] := by
  simp [inferBasis, isInstanceTypes, hlook, hfind,
    WellFormedTy.toType]

/-! ### Completeness steps

Each step selects a valid package from the compound expression's candidates.
The package supplies validity directly to the next subtype check. -/

/-- A receiver case supplies a candidate with its declared attribute result. -/
private theorem inferBasis_attrAccess_step_general
    (hwfct : WellTypedClassHierarchy ct) (hΓwf : WellFormedTyEnv ct Γ)
    (hSb : Sb ∈ (inferBasis hwfct Γ hΓwf base).types)
    (hsub : IsSubtype hwfct.toWellFormedClassHierarchy Sb.raw view.receiver.raw)
    (member : view ∈ attrReceiverViews hwfct attrName) :
    view.result ∈ (inferBasis hwfct Γ hΓwf (.attrAccess base attrName)).types := by
  apply InferredBasis.candidate_member
  exact List.mem_flatMap.mpr ⟨Sb, hSb,
    attrResultsFromTy_complete_of_member hwfct Sb hsub member⟩

/-- A class method supplies a candidate with exactly its declared function type. -/
theorem inferBasis_attrAccess_step
    (hwfct : WellTypedClassHierarchy ct) (hΓwf : WellFormedTyEnv ct Γ)
    (hSb : Sb ∈ (inferBasis hwfct Γ hΓwf base).types)
    (hsub : IsSubtype hwfct.toWellFormedClassHierarchy Sb.raw (.class_ cname))
    (hfmt : FindMethodType ct cname attrName paramTy returnTy) :
    ∃ result ∈ (inferBasis hwfct Γ hΓwf (.attrAccess base attrName)).types,
      result.raw = .callable paramTy returnTy := by
  obtain ⟨view, member, inputEqual, resultEqual⟩ := attrReceiverView_class_member hwfct hfmt
  exact ⟨view.result, inferBasis_attrAccess_step_general hwfct hΓwf hSb
    (inputEqual.symm ▸ hsub) member, resultEqual⟩

/-- A union receiver supplies the union of its two declared method types. -/
theorem inferBasis_attrAccessUnion_step
    (hwfct : WellTypedClassHierarchy ct) (hΓwf : WellFormedTyEnv ct Γ)
    (hSb : Sb ∈ (inferBasis hwfct Γ hΓwf base).types)
    (hsub : IsSubtype hwfct.toWellFormedClassHierarchy Sb.raw (.union (.class_ c1) (.class_ c2)))
    (hfmt1 : FindMethodType ct c1 attrName p1 r1)
    (hfmt2 : FindMethodType ct c2 attrName p2 r2) :
    ∃ result ∈ (inferBasis hwfct Γ hΓwf (.attrAccess base attrName)).types,
      result.raw = .union (.callable p1 r1) (.callable p2 r2) := by
  obtain ⟨view, member, inputEqual, resultEqual⟩ := attrReceiverView_union_member hwfct hfmt1 hfmt2
  exact ⟨view.result, inferBasis_attrAccess_step_general hwfct hΓwf hSb
    (inputEqual.symm ▸ hsub) member, resultEqual⟩

/-- The call candidates contain a package refining the declarative result. -/
theorem inferBasis_call_step
    (hwfct : WellTypedClassHierarchy ct) (hΓwf : WellFormedTyEnv ct Γ)
    (hSc : Sc ∈ (inferBasis hwfct Γ hΓwf callee).types)
    (hSa : Sa ∈ (inferBasis hwfct Γ hΓwf arg).types)
    (hsubCallable : IsSubtype hwfct.toWellFormedClassHierarchy Sc.raw (.callable paramTy returnTy))
    (hsubArg : IsSubtype hwfct.toWellFormedClassHierarchy Sa.raw paramTy) :
    ∃ result ∈ (inferBasis hwfct Γ hΓwf (.call callee arg)).types,
      IsSubtype hwfct.toWellFormedClassHierarchy result.raw returnTy := by
  obtain ⟨result, selected, included⟩ := callResultsFromTy_complete Sc hsubCallable hSa hsubArg
  exact ⟨result, InferredBasis.candidate_member _
    (List.mem_flatMap.mpr ⟨Sc, hSc, selected⟩), included⟩

/-- An ordinary conditional contains the union of two selected branch packages. -/
theorem inferBasis_cond_ordinary_step
    (hwfct : WellTypedClassHierarchy ct) (hΓwf : WellFormedTyEnv ct Γ)
    (hSc : Sc ∈ (inferBasis hwfct Γ hΓwf condExpr).types)
    (hbool : IsSubtype hwfct.toWellFormedClassHierarchy Sc.raw (.class_ boolClass))
    (hSt : St ∈ (inferBasis hwfct Γ hΓwf thenBr).types)
    (hSe : Se ∈ (inferBasis hwfct Γ hΓwf elseBr).types) :
    WellFormedType.union St Se ∈
      (inferBasis hwfct Γ hΓwf (.cond condExpr thenBr elseBr)).types := by
  have member := ordinaryCondTypes_mem_of_witness hwfct
    (inferBasis hwfct Γ hΓwf condExpr)
    (inferBasis hwfct Γ hΓwf thenBr)
    (inferBasis hwfct Γ hΓwf elseBr) hSc hbool hSt hSe
  cases condExpr with
  | isInstance _ _ =>
      apply InferredBasis.candidate_member
      exact List.mem_append.mpr (Or.inl member)
  | _ => exact InferredBasis.candidate_member _ member

/-- A class-test conditional contains the union of its refined branch packages. -/
theorem inferBasis_cond_isInstance_specialized_step
    (hwfct : WellTypedClassHierarchy ct) (hΓwf : WellFormedTyEnv ct Γ)
    (hlook : Γ.lookup x = some T) (hfind : findClass ct C = some cls)
    (St Se : WellFormedType (ct.map ClassDecl.name))
    (hSt : St ∈ (inferBasis hwfct
      (Γ.update x (.intersection T (.class_ C)))
      (wellFormedTyEnv_update_class hΓwf hlook hfind) thenBr).types)
    (hSe : Se ∈ (inferBasis hwfct
      (Γ.update x (.intersection T (.negClass C)))
      (wellFormedTyEnv_update_negClass hΓwf hlook hfind) elseBr).types) :
    WellFormedType.union St Se ∈
      (inferBasis hwfct Γ hΓwf (.cond (.isInstance x C) thenBr elseBr)).types := by
  apply InferredBasis.candidate_member
  exact List.mem_append.mpr (Or.inr
    (specializedCondTypes_mem_of_witness hlook hfind hSt hSe))
