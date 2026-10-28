module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.SylowEightRigidity.AmbientComparison
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowTwoPart

/-!
# From the literal max4 kernel count to the Sylow model comparison

The Theory producer combines an actual epimorphism onto S₅ × SL₃(2)
with the two-group property and cardinality lower bound of the literal
seed normal closure. The resulting divisibility is exactly the hypothesis
of the checked ambient Sylow comparison. The ambient embeddings and
Sylow conjugacy provide the multiplicative equivalence.

The unconditional `max4SylowEightModelComparison` applies the completed
two-part certificate to that ambient comparison, giving an actual
isomorphism from one intrinsic max4 Sylow to the reference matrix group.
The conditional API is retained for its separate inputs.

Source context: Kleidman--Wilson (1988), pp.484--510, and the literal
ATLAS max4 program cited in `SymmetricLinear.Model`.
-/

public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
open Janko4.LocalStructure.SymmetricLinear

/-- The actual consumer of the quotient and relative normal-closure certificates. -/
theorem max4SylowEightModelComparison_of_seed_card
    (f : max4Subgroup →* QuotientModel) (hf : Function.Surjective f)
    (hQ : IsPGroup 2 CharacteristicTwo.seedNormalClosure)
    (hc : 2 ^ 15 ≤ Nat.card CharacteristicTwo.seedNormalClosure) :
    Max4SylowEightModelComparison :=
  max4SylowEightModelComparison_of_twoPart
    (max4_twoPart_dvd_of_seed_card f hf hQ hc)

/-- An intrinsic Sylow of the literal max4 subgroup is genuinely isomorphic
to the reference matrix two-subgroup, by their ambient Sylow embeddings. -/
theorem max4SylowEightModelComparison : Max4SylowEightModelComparison :=
  max4SylowEightModelComparison_of_twoPart max4_twoPart_dvd

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
