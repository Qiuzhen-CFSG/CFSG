module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_12_6
public import Theory.AlgebraicGroup.Borel.RootStructure.UnipotentProduct

/-!
GLS3 Theorem 1.12.7 packages the structure of a Borel subgroup through ordered
positive-root products, Chevalley commutators, closed root subsets and ideals,
fundamental-root generation, and simple-root torus factors.

The root-system realization now explicitly includes realization of partial
root addition. This is the source-faithful bridge from vector sums occurring
in the Chevalley formula to the `RootGroupData.add` operation used by positive
systems, closed subsets, and root ideals.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_12_7
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsSemisimpleAlgebraicGroup K)
    (T B U : ClosedSubgroup K) (D : RootGroupData K T)
    (C : ChevalleyData K D) (positiveRoots : Set D.Root)
    [Fintype D.Root]
    (hSetup : IsStandardBorelSetup T B D positiveRoots)
    (hU : IsUnipotentRadicalOf B U)
    (hGen : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hFactor : B.toSubgroup = T.toSubgroup ⊔ U.toSubgroup)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hActual : IsRootSystemRealization D P e base)
    (hAdd : IsRootAdditionRealization D P e)
    (hC : IsChevalleySystem D C P e base) :
    Nonempty (BorelRootStructure T D positiveRoots B U C P e base) := by sorry

end Theory.AlgebraicGroup
