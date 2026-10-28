module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Row12.UpperBound
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Row12.LowerBound

/-!
# The exceptional Held row-12 normalizer containment

An invariant ten-point configuration embeds the actual normalizer in an even
pair-preserving graph group of order at most 9216. Five explicit Held words
generate a subgroup normalizing both rows 12 and 20 and containing nine
disjoint copies of the 1024-element representative. The matching bounds
identify this subgroup with the whole row-12 normalizer.

All finite premises are discharged in the two descendants. In particular the
argument applies to arbitrary normalizer elements and does not choose an E64
by the false assertion that the row-12 centralizer contains a unique normal E64.

Sources: the unchanged ATLAS subgroup words and degree-2058 action;
GLS3 Table 5.3p; Aschbacher–Smith condition E, printed pp.3–4 and 481–482.
This containment supplies the exceptional premise in the separate nine-row
assembly; it makes no maximal-subgroup classification assertion.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open Subgroup E64Containment

/-- The exceptional E64 containment, for the full actual ambient normalizer. -/
public theorem normalizer_row12_le_normalizer_row20 :
    normalizer (ambient 12 : Set He) ≤ normalizer (ambient 20 : Set He) := by
  have he : Row12.wordSubgroup = normalizer (ambient 12 : Set He) :=
    eq_of_le_of_card_ge Row12.wordSubgroup_le_normalizer12
      (Row12.normalizer_card_le.trans Row12.wordSubgroup_card_ge)
  rw [← he]
  exact Row12.wordSubgroup_le_normalizer20

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue
