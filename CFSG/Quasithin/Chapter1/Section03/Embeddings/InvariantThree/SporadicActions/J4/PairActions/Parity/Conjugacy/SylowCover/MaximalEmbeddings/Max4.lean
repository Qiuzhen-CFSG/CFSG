module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.Reduction

/-!
# Max4 maximal-embedding conjugacy from two intrinsic local facts

A normal elementary subgroup of order eight in the literal max4 carrier lies
in every local Sylow subgroup. If normal elementary subgroups of order eight
in these Sylows are characteristic, aligning the Sylows also aligns this
normal subgroup. The normalizer comparison in `Reduction` then identifies
an isomorphic maximal Sylow overgroup with a conjugate of literal max4.

Both local facts remain explicit proof obligations. In particular this
conditional theorem does not yet establish `max4MaximalEmbeddingConjugacy`.
No quotient identification, ambient order or maximal-subgroup cover is used.
The conjugation convention is g L g⁻¹.

Source context: Kleidman--Wilson, *The maximal subgroups of J₄*, Proc. London
Math. Soc. 56 (1988), 484--510; the application in Aschbacher--Smith,
`refs/quasithin.pdf`, printed p.511/PDF p.528, cites Aschbacher (1986).
-/

public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover

/-- Conditional final assembly for the two independent intrinsic max4 facts.
The unconditional embedding theorem requires proofs of both premises. -/
theorem max4MaximalEmbeddingConjugacy_of_normalElementaryEight
    (hA : Max4NormalElementaryEight)
    (hS : Max4SylowElementaryEightCharacteristic) :
    MaximalEmbeddingConjugacyAt Janko4.LocalStructure.SymmetricLinear.max4Subgroup :=
  max4MaximalEmbeddingConjugacy_of_sylowCharacteristicNormal
    (max4SylowCharacteristicNormal_of_normalElementaryEight hA hS)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
