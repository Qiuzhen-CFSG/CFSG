module

public import Theory.AlgebraicGroup.Borel.RootStructure.ChevalleyPresentationEvaluation

/-!
This module supplies the arbitrary-version torus-relator interface for a
Chevalley presentation.  A family of torus weights on the chosen base records
the final general coroot-kernel condition in `IsChevalleySystem`; the resulting
torus words are adjoined to the common Chevalley relators.  The membership
characterizations and evaluation lemmas are intentionally small so that a
later normal-form theorem can use this API without depending on the numbered
presentation theorem, Frobenius data, or stored automorphisms.

The evaluation argument maps a formal base-torus word to the corresponding
product of `C.h` values and applies the weight-family kernel equivalence.  The
common-relator part is delegated to the existing
`ChevalleyPresentationEvaluation` package.
-/

universe u

set_option linter.unusedSectionVars false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public def generalTorusRelators
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (weights : base.support → TorusWeight T) :
    Set (FreeGroup (FormalChevalleyGenerator D.Root k)) :=
  { word | ∃ t : base.support → kˣ,
      (∀ j, (∏ i, t i ^ D.weightPairing (weights j) (e.symm i)) = 1) ∧
      word = formalRelation
        (base.support.attach.toList.map fun i : base.support =>
        formalChevalleyH (e.symm i) (t i)).prod 1 }

public theorem mem_generalTorusRelators
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (weights : base.support → TorusWeight T)
    (word : FreeGroup (FormalChevalleyGenerator D.Root k)) :
    word ∈ generalTorusRelators (e := e) (base := base) weights ↔
      ∃ t : base.support → kˣ,
        (∀ j, (∏ i, t i ^ D.weightPairing (weights j) (e.symm i)) = 1) ∧
        word = formalRelation
          (base.support.attach.toList.map fun i : base.support =>
            formalChevalleyH (e.symm i) (t i)).prod 1 := by
  rfl

public def generalChevalleyRelators
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T) :
    Set (FreeGroup (FormalChevalleyGenerator D.Root k)) :=
  universalChevalleyRelators data ∪
    generalTorusRelators (e := e) (base := base) weights

public theorem mem_generalChevalleyRelators
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T)
    (word : FreeGroup (FormalChevalleyGenerator D.Root k)) :
    word ∈ generalChevalleyRelators data weights ↔
      word ∈ universalChevalleyRelators data ∨
        word ∈ generalTorusRelators (e := e) (base := base) weights := by
  simp only [generalChevalleyRelators, Set.mem_union]

private theorem lift_formalH_list_prod
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (C : ChevalleyData K D)
    (xs : List base.support) (t : base.support → kˣ) :
    FreeGroup.lift (evaluateFormalChevalleyGenerator C)
        (xs.map (fun i : base.support =>
          formalChevalleyH (e.symm i) (t i))).prod =
      (xs.map (fun i : base.support => C.h (e.symm i) (t i))).prod := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
      simp only [List.map_cons, List.prod_cons, map_mul]
      rw [formalChevalleyH_eq, FreeGroup.lift_apply_of,
        evaluateFormalChevalleyGenerator_h, ih]

public theorem evaluation_kills_generalTorusRelators
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (C : ChevalleyData K D)
    (weights : base.support → TorusWeight T)
    (hGeneral : ∀ t : base.support → kˣ,
      (base.support.attach.toList.map fun i : base.support =>
      C.h (e.symm i) (t i)).prod = 1 ↔
        ∀ j, (∏ i, t i ^ D.weightPairing (weights j) (e.symm i)) = 1) :
    ∀ r ∈ generalTorusRelators (e := e) (base := base) weights,
      FreeGroup.lift (evaluateFormalChevalleyGenerator C) r = 1 := by
  intro r hr
  rw [mem_generalTorusRelators (e := e) (base := base)] at hr
  rcases hr with ⟨t, ht, hw⟩
  rw [hw]
  simp only [lift_evaluate_formalRelation, map_one, inv_one, mul_one]
  rw [show FreeGroup.lift (evaluateFormalChevalleyGenerator C)
      ((base.support.attach.toList.map fun i : base.support =>
        formalChevalleyH (e.symm i) (t i)).prod) =
      (base.support.attach.toList.map fun i : base.support =>
        C.h (e.symm i) (t i)).prod by
      exact lift_formalH_list_prod C base.support.attach.toList t]
  exact hGeneral t |>.mpr (fun j => ht j)

public theorem evaluation_kills_generalChevalleyRelators
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (C : ChevalleyData K D)
    (hC : IsChevalleySystem D C P e base)
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T)
    (hData : IsChevalleyRelationDataFor D C P e base data)
    (hGeneral : ∀ t : base.support → kˣ,
      (base.support.attach.toList.map fun i : base.support =>
      C.h (e.symm i) (t i)).prod = 1 ↔
        ∀ j, (∏ i, t i ^ D.weightPairing (weights j) (e.symm i)) = 1) :
    ∀ r ∈ generalChevalleyRelators data weights,
      FreeGroup.lift (evaluateFormalChevalleyGenerator C) r = 1 := by
  intro r hr
  rw [mem_generalChevalleyRelators (e := e) (base := base)] at hr
  rcases hr with hr | hr
  · exact evaluation_kills_universalChevalleyRelators D C P e base hC data hData r hr
  · exact evaluation_kills_generalTorusRelators P e base C weights hGeneral r hr

public theorem exists_generalChevalleyRelationData
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (C : ChevalleyData K D) (hC : IsChevalleySystem D C P e base) :
    ∃ data : ChevalleyRelationData D P e base,
      ∃ weights : base.support → TorusWeight T,
        Set.range D.rootWeight ⊆ Subgroup.closure (Set.range weights) ∧
        (∀ t : base.support → kˣ,
          (base.support.attach.toList.map fun i : base.support =>
            C.h (e.symm i) (t i)).prod = 1 ↔
            ∀ j, (∏ i, t i ^ D.weightPairing (weights j) (e.symm i)) = 1) ∧
        IsChevalleyRelationDataFor D C P e base data := by
  obtain ⟨data, hData⟩ := exists_chevalleyRelationData D C P e base hC
  rcases hC with
    ⟨_, _, _, _, _, _, _, _, _, _, hGeneral, _, _, _⟩
  exact ⟨data, hGeneral.choose, hGeneral.choose_spec.1,
    hGeneral.choose_spec.2, hData⟩

end Theory.AlgebraicGroup
