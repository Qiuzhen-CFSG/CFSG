module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Overgroups
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.Reduction

/-!
# Assembly of arbitrary J₄ pair coverage from a fixed Sylow calculation

Odd index makes the certified order-2²¹ subgroup Sylow in the ambient
matrix group. Coverage for pairs with this subgroup then transports to
every Sylow pair by conjugacy, preserving the actual max4 isomorphism.

This assembly is conditional. The ambient odd-index proof belongs to
`Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex`; the remaining
fixed-subgroup incidence contract is `FixedTwoSubgroupPairCoverage`.
Until both are proved, `maximalFourPairCoverage` remains open. In particular
neither a specified max4 subgroup nor its quotient calculation supplies
the incidence assertion.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528 of
`refs/quasithin.pdf`), citing Aschbacher's *Overgroups of Sylow subgroups in
sporadic groups* (1986).
-/

public section

open Janko4.OuterReduction.OddIndex Janko4.Cardinality
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- Discharge the Sylow-coordinate reduction using the two independent
model inputs. This theorem does not assert either input. -/
theorem maximalFourPairCoverage_of_fixedTwoSubgroup
    (hindex : ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model]
      [Group.IsPerfect Janko4.Model],
      ¬ 2 ∣ (max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four).index)
    (hcover : FixedTwoSubgroupPairCoverage) : MaximalFourPairCoverage := by
  intro _ _ _ S R h
  let T : Sylow 2 Janko4.Model :=
    twoSubgroup_isPGroup.toSylow (twoSubgroup_odd_index_of_max1 hindex)
  exact pairCoverage_of_one_sylow T (fun R hR => hcover T rfl R hR) S R h

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
