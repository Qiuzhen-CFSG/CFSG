module
public import Theory.SpecificGroups.Held.ComponentFacts
public import Theory.SpecificGroups.Held.TwoRank.Normalizer

/-!
# Automorphism two-rank of the Held carrier

The proved full automorphism realization identifies Aut(He) with its
permutation normalizer. The completed normalizer-quotient bound applies
the checked rank-six calculation to this literal group, discharging both
outer-group premises. The point-component six-dimensional section is the
consumer. Source: GLS3 Table 5.3p and Aschbacher--Smith 10.2.9, pp.750--751.
-/

public section
open Subgroup Theory.GroupTheory
namespace Held
/-- The full automorphism group has two-rank at most six. -/
theorem automorphism_rank_le_six : primeRank 2 (MulAut He) ≤ 6 := by
  let e := MulEquiv.ofBijective permutationGroup.normalizerMonoidHom
    ⟨OuterInvolution.normalizer_action_injective,Realization.normalizer_surjective⟩
  rw [←primeRank_equiv 2 e]
  exact TwoRank.normalizer_twoRank_le_six permutationNormalizerQuotient_card_le_two
end Held
