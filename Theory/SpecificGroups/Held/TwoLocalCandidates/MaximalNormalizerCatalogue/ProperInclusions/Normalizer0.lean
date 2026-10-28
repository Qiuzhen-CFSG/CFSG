module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.WordTests

/-!
# A concrete element in the containing normalizer

Conjugating each literal generator gives a product of generators in the same
row. The equations are checked on Held's certified four-point base, and
finiteness upgrades the resulting inclusion to normalization.
Source: the unchanged ATLAS words; coordinates reproduced by `source/verify.py`.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions
open Subgroup

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem conjugate_0 :
    witness 0 * rowElement 0 0 * (witness 0)⁻¹ =
      rowProduct 0 [0] := by
  apply Held.eq_of_four_point_images
  decide +kernel

public theorem witness_mem_0 :
    witness 0 ∈ normalizer (ambient 0 : Set He) := by
  apply mem_normalizer_of_words
  intro w hw
  simp only [generatorWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl
  · change witness 0 * rowElement 0 0 * (witness 0)⁻¹ ∈ ambient 0
    rw [conjugate_0]
    exact rowProduct_mem _ _

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions
