module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu

/-!
# The intrinsic Sylow-core obligation for the literal J₄ max1 subgroup

The literal normal closure is already a nontrivial elementary abelian two-core
of order 2048. It lies in every Sylow two-subgroup of max1. The remaining
intrinsic obligation says that every automorphism of such a Sylow preserves
this particular subgroup. Normality in max1 alone does not establish this.

The embedding assembly uses characteristicity to compare two copies after
aligning their Sylow subgroups. This interface contains no ambient conjugacy,
normalizer equality, or maximal-overgroup classification assertion.

Source context: Kleidman–Wilson, *The maximal subgroups of J₄* (1988),
pp.484–510; GLS3 Table 5.3i, printed p.270. The actual ATLAS word subgroup,
its binary kernel and its M₂₄ quotient are certified in the imported
`LocalStructure.Mathieu` module. Characteristicity is a separate proof
obligation for that concrete group, not a claim supplied by the table.
-/

public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover

open Janko4 Janko4.Cardinality

/-- Every local Sylow automorphism preserves the restriction of the literal
max1 two-core. Its proof is required before the embedding theorem is complete. -/
@[expose] def Max1SylowCoreCharacteristic : Prop :=
  ∀ P : Sylow 2 (max1Subgroup matrixA_mul_self matrixB_pow_four),
    ((localKernel matrixA_mul_self matrixB_pow_four).subgroupOf P.toSubgroup).Characteristic

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
