module
public import Theory.SpecificGroups.Held.TwoRank.Normalizer
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer

/-!
# The intrinsic two-rank bound for Held

The original Held carrier embeds in its actual permutation normalizer.
The proved quotient bound and the checked Sylow coloring give rank at most
six for that normalizer, and hence for Held itself.

Source: Aschbacher--Smith G.7.3(2), printed p.348; the local application is
the ordinary Held row of C.3.5, printed p.150.
-/

public section
namespace Held

/-- The actual Held model has two-rank at most six. -/
theorem primeRank_two_le_six : primeRank 2 He ≤ 6 := by
  apply (Theory.GroupTheory.primeRank_le_of_injective 2
    LocalPairs.innerEmbedding (Subgroup.inclusion_injective _)).trans
  exact TwoRank.normalizer_twoRank_le_six permutationNormalizerQuotient_card_le_two

end Held
