module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers.NineDivisibility
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers.RowTwo

/-!
# Arithmetic of the three Held four-group normalizers

For the literal ambient catalogue rows 1 and 3, two commuting cubic words
embed C₃ × C₃ in the full normalizer. For row 2, its common fixed vertices
recover the certified Sylow coloring of the Held graph. The full normalizer
embeds in the even colored graph group of order 1024 and is a two-group.
Thus these are arithmetic statements about full normalizers in the original
degree-2058 Held carrier, independent of the exhaustive catalogue and coverage.

This is the exact arithmetic input to the Held branch of Aschbacher–Smith
15.3.43, printed p.1140, based on GLS3 Table 5.3p. See the descendant source
README for the ATLAS words, graph certificates and action conventions.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open Subgroup FourGroupNormalizers

/-- The three literal four-group rows satisfy the arithmetic required by the
rank-one Held exclusion, with every concrete calculation discharged. -/
public theorem four_group_normalizer_arithmetic (j : Fin 22)
    (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    IsPGroup 2 (normalizer (ambient j : Set He)) ∨
      9 ∣ Nat.card (normalizer (ambient j : Set He)) := by
  rcases hj with rfl | rfl | rfl
  · exact Or.inr nine_dvd_normalizer_one
  · exact Or.inl isPGroup_normalizer_two
  · exact Or.inr nine_dvd_normalizer_three

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue
