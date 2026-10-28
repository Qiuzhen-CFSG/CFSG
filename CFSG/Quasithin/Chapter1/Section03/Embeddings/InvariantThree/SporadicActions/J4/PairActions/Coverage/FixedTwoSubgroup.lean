module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.LocalReduction

/-!
# Assembly of fixed J₄ pair coverage from elementary-normalizer placement

The proved local reduction puts every pair inside a full elementary
normalizer containing the fixed Sylow two-subgroup. Split the odd
complement into its elementary order-nine and extraspecial order-27 cases.
Placement for those two cases supplies an actual conjugate of max4; its
conjugation equivalence gives the required element of `PairOvergroups`.

This assembly remains conditional on the two model placement contracts.
Neither contract nor `fixedTwoSubgroupPairCoverage` is proved here yet.
The ambient Sylow witness is inherited from the caller throughout.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528 of
`refs/quasithin.pdf`), citing Aschbacher's *Overgroups of Sylow subgroups in
sporadic groups* (1986).
-/

public section

open Janko4.OuterReduction.OddIndex
open Janko4.LocalStructure.SymmetricLinear

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- Both normalizer-placement branches give fixed-subgroup coverage.
The two placement premises still require proofs on the actual matrix carrier. -/
theorem fixedTwoSubgroupPairCoverage_of_normalizer_placements
    (he : FixedTwoElementaryNormalizerPlacement)
    (hx : FixedTwoExtraspecialNormalizerPlacement) : FixedTwoSubgroupPairCoverage := by
  intro _ _ _ S hS R h
  obtain ⟨A, hA, hRA⟩ := fixedTwo_pair_elementary_normalizer hS h
  have hplace : ∃ g : Janko4.Model,
      twoSubgroup ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom ∧
      R ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom := by
    rcases h.oddComplement with ⟨hE, hc⟩ | ⟨hE, hc, hexp⟩
    · exact he S hS R h hE hc A hA hRA
    · exact hx S hS R h hE hc hexp A hA hRA
  obtain ⟨g, hT, hR⟩ := hplace
  exact pairOvergroups_nonempty_of_conjugate twoSubgroup R g hT hR

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
