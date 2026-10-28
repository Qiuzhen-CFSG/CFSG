module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_12_1

/-!
This module packages the formal evaluation step in the universal Chevalley
presentation of GLS3, Theorem 1.12.4(a), following Steinberg's presentation.
An `IsChevalleySystem` supplies ordered commutator coefficients, coroot
coordinates, and reflection signs.  These choices form `ChevalleyRelationData`;
the corresponding formulas show that evaluation kills every displayed relator,
so it descends to the presented group.  The reverse kernel inclusion and root
generation needed to identify that group with the universal algebraic group are
deliberately left to the later normal-form argument.
-/

universe u

set_option linter.unusedSectionVars false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public structure IsChevalleyRelationDataFor
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (data : ChevalleyRelationData D P e base) : Prop where
  commutatorFormula : ∀ α β,
    AreLinearlyIndependentRoots D P e α β → ∀ t s,
      (C.x α t)⁻¹ * (C.x β s)⁻¹ * C.x α t * C.x β s =
        ((data.commutatorOrder α β).map fun q =>
          C.x q.root
            (data.commutatorCoefficient α β q * t ^ q.i * s ^ q.j)).prod
  corootFormula : ∀ α t, C.h α t =
    (base.support.attach.toList.map fun i : base.support =>
      C.h (e.symm i) (t ^ data.corootCoefficient α i)).prod
  reflectionConjugatesRoot : ∀ α β t,
    (C.n β 1)⁻¹ * C.x α t * C.n β 1 =
      C.x (D.reflect β α) ((data.reflectionSign α β : k) * t)
  reflectionConjugatesTorus : ∀ α β t,
    (C.n β 1)⁻¹ * C.h α t * C.n β 1 = C.h (D.reflect β α) t
  reflectionConjugatesReflection : ∀ α β t,
    (C.n β 1)⁻¹ * C.n α t * C.n β 1 =
      C.n (D.reflect β α) (data.reflectionSign α β * t)

public theorem exists_chevalleyRelationData
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hC : IsChevalleySystem D C P e base) :
    ∃ data : ChevalleyRelationData D P e base,
      IsChevalleyRelationDataFor D C P e base data := by
  classical
  have hcomm : ∀ α β : D.Root,
      ∃ order : List (ChevalleyCommutatorTerm D.Root),
      ∃ coefficient : ChevalleyCommutatorTerm D.Root → k,
        AreLinearlyIndependentRoots D P e α β →
          order.Nodup ∧
          order.Pairwise (fun q r => q.i + q.j ≤ r.i + r.j) ∧
          (∀ q, q ∈ order ↔ IsValidChevalleyCommutatorTerm D P e α β q) ∧
          (∀ q ∈ order,
            HasExpectedChevalleyCoefficient D P e α β q (coefficient q)) ∧
          ∀ t s,
            (C.x α t)⁻¹ * (C.x β s)⁻¹ * C.x α t * C.x β s =
              (order.map fun q =>
                C.x q.root (coefficient q * t ^ q.i * s ^ q.j)).prod := by
    intro α β
    by_cases hIndependent : AreLinearlyIndependentRoots D P e α β
    · obtain ⟨order, coefficient, horder⟩ := hC.2.2.2.2.1 α β hIndependent
      exact ⟨order, coefficient, fun _ => horder⟩
    · exact ⟨[], fun _ => 0, fun h => (hIndependent h).elim⟩
  choose order horder using hcomm
  choose coefficient hcoefficient using horder
  obtain ⟨corootCoefficient, hcorootExpansion, hcorootFormula⟩ :=
    hC.2.2.2.2.2.2.2.1
  obtain ⟨reflectionSign, hreflectionSign, hreflectionRoot,
      hreflectionTorus, hreflectionReflection⟩ :=
    hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  let data : ChevalleyRelationData D P e base :=
    { commutatorOrder := order
      commutatorCoefficient := coefficient
      commutatorOrderNodup := fun α β h => (hcoefficient α β h).1
      commutatorOrderSorted := fun α β h => (hcoefficient α β h).2.1
      commutatorOrderMem := fun α β h => (hcoefficient α β h).2.2.1
      commutatorCoefficientExpected := fun α β h =>
        (hcoefficient α β h).2.2.2.1
      corootCoefficient := corootCoefficient
      corootExpansion := hcorootExpansion
      reflectionSign := reflectionSign
      reflectionSignValue := hreflectionSign }
  exact ⟨data,
    { commutatorFormula := fun α β h => (hcoefficient α β h).2.2.2.2
      corootFormula := hcorootFormula
      reflectionConjugatesRoot := hreflectionRoot
      reflectionConjugatesTorus := hreflectionTorus
      reflectionConjugatesReflection := hreflectionReflection }⟩

public theorem evaluation_kills_universalChevalleyRelators
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hC : IsChevalleySystem D C P e base)
    (data : ChevalleyRelationData D P e base)
    (hData : IsChevalleyRelationDataFor D C P e base data) :
    ∀ r ∈ universalChevalleyRelators data,
      FreeGroup.lift (evaluateFormalChevalleyGenerator C) r = 1 := by
  intro r hr
  rw [mem_universalChevalleyRelators_iff] at hr
  cases hr with
  | nDefinition α t =>
      simp only [lift_evaluate_formalRelation, map_mul,
        lift_evaluate_formalChevalleyN, lift_evaluate_formalChevalleyX]
      rw [hC.2.1]
      group
  | hDefinition α t =>
      simp only [lift_evaluate_formalRelation, map_mul, map_inv,
        lift_evaluate_formalChevalleyH, lift_evaluate_formalChevalleyN]
      rw [hC.2.2.1]
      group
  | rootAddition α t s =>
      simp only [lift_evaluate_formalRelation, map_mul,
        lift_evaluate_formalChevalleyX]
      rw [hC.2.2.2.1]
      group
  | rootCommutator α β hIndependent t s =>
      simp only [lift_evaluate_formalRelation, map_mul, map_inv,
        lift_evaluate_formalChevalleyX, map_list_prod, List.map_map]
      have heval :
          (FreeGroup.lift (evaluateFormalChevalleyGenerator C) :
              FreeGroup (FormalChevalleyGenerator D.Root k) → Variety.Point K) ∘
              (fun q => formalChevalleyX q.root
                (data.commutatorCoefficient α β q * t ^ q.i * s ^ q.j)) =
            fun q => C.x q.root
              (data.commutatorCoefficient α β q * t ^ q.i * s ^ q.j) := by
        funext q
        simp only [Function.comp_apply, lift_evaluate_formalChevalleyX]
      rw [heval]
      rw [hData.commutatorFormula α β hIndependent]
      group
  | torusCommutes α β t s =>
      simp only [lift_evaluate_formalRelation, map_mul, map_inv, map_one,
        lift_evaluate_formalChevalleyH, inv_one]
      have hcomm : Commute (C.h α t) (C.h β s) := hC.2.2.2.2.2.1 α β t s
      rw [(hcomm.inv_right).inv_mul_cancel]
      simp
  | torusMultiplication α t s =>
      simp only [lift_evaluate_formalRelation, map_mul,
        lift_evaluate_formalChevalleyH]
      rw [hC.2.2.2.2.2.2.1 α t s]
      group
  | corootExpansion α t =>
      simp only [lift_evaluate_formalRelation, lift_evaluate_formalChevalleyH,
        map_list_prod, List.map_map]
      have heval :
          (FreeGroup.lift (evaluateFormalChevalleyGenerator C) :
              FreeGroup (FormalChevalleyGenerator D.Root k) → Variety.Point K) ∘
              (fun i : base.support =>
                formalChevalleyH (e.symm i)
                  (t ^ data.corootCoefficient α i)) =
            fun i : base.support =>
              C.h (e.symm i) (t ^ data.corootCoefficient α i) := by
        funext i
        simp only [Function.comp_apply, lift_evaluate_formalChevalleyH]
      rw [heval, hData.corootFormula α t]
      group
  | torusConjugatesRoot α β t s =>
      simp only [lift_evaluate_formalRelation, map_mul, map_inv,
        lift_evaluate_formalChevalleyH, lift_evaluate_formalChevalleyX]
      rw [hC.2.2.2.2.2.2.2.2.2.2.2.1 α β t s]
      group
  | reflectionConjugatesRoot α β t =>
      simp only [lift_evaluate_formalRelation, map_mul, map_inv,
        lift_evaluate_formalChevalleyN, lift_evaluate_formalChevalleyX]
      rw [hData.reflectionConjugatesRoot α β t]
      group
  | reflectionConjugatesTorus α β t =>
      simp only [lift_evaluate_formalRelation, map_mul, map_inv,
        lift_evaluate_formalChevalleyN, lift_evaluate_formalChevalleyH]
      rw [hData.reflectionConjugatesTorus α β t]
      group
  | reflectionConjugatesReflection α β t =>
      simp only [lift_evaluate_formalRelation, map_mul, map_inv,
        lift_evaluate_formalChevalleyN]
      rw [hData.reflectionConjugatesReflection α β t]
      group
  | reflectionSquare α =>
      simp only [lift_evaluate_formalRelation, map_mul,
        lift_evaluate_formalChevalleyN, lift_evaluate_formalChevalleyH]
      rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.2 α]
      group

public theorem exists_universalChevalleyEvaluation
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hC : IsChevalleySystem D C P e base) :
    ∃ data : ChevalleyRelationData D P e base,
    ∃ _hData : IsChevalleyRelationDataFor D C P e base data,
    ∃ evaluation : PresentedGroup (universalChevalleyRelators data) →*
        Variety.Point K,
      (∀ r ∈ universalChevalleyRelators data,
        FreeGroup.lift (evaluateFormalChevalleyGenerator C) r = 1) ∧
      ∀ generator, evaluation (PresentedGroup.of generator) =
        evaluateFormalChevalleyGenerator C generator := by
  obtain ⟨data, hData⟩ := exists_chevalleyRelationData D C P e base hC
  have hrels := evaluation_kills_universalChevalleyRelators
    D C P e base hC data hData
  let evaluation : PresentedGroup (universalChevalleyRelators data) →*
      Variety.Point K := PresentedGroup.toGroup hrels
  refine ⟨data, hData, evaluation, hrels, ?_⟩
  intro generator
  exact PresentedGroup.toGroup.of hrels

end Theory.AlgebraicGroup
