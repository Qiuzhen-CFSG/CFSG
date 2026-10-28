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
    witness 2 * rowElement 20 0 * (witness 2)⁻¹ =
      rowProduct 20 [0, 1, 2, 5] := by
  apply Held.eq_of_four_point_images
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem conjugate_1 :
    witness 2 * rowElement 20 1 * (witness 2)⁻¹ =
      rowProduct 20 [0, 1, 2, 3, 5] := by
  apply Held.eq_of_four_point_images
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem conjugate_2 :
    witness 2 * rowElement 20 2 * (witness 2)⁻¹ =
      rowProduct 20 [4] := by
  apply Held.eq_of_four_point_images
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem conjugate_3 :
    witness 2 * rowElement 20 3 * (witness 2)⁻¹ =
      rowProduct 20 [0, 1, 2, 4] := by
  apply Held.eq_of_four_point_images
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem conjugate_4 :
    witness 2 * rowElement 20 4 * (witness 2)⁻¹ =
      rowProduct 20 [0, 4, 5] := by
  apply Held.eq_of_four_point_images
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem conjugate_5 :
    witness 2 * rowElement 20 5 * (witness 2)⁻¹ =
      rowProduct 20 [1, 3] := by
  apply Held.eq_of_four_point_images
  decide +kernel

public theorem witness_mem_2 :
    witness 2 ∈ normalizer (ambient 20 : Set He) := by
  apply mem_normalizer_of_words
  intro w hw
  simp only [generatorWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · change witness 2 * rowElement 20 0 * (witness 2)⁻¹ ∈ ambient 20
    rw [conjugate_0]
    exact rowProduct_mem _ _
  · change witness 2 * rowElement 20 1 * (witness 2)⁻¹ ∈ ambient 20
    rw [conjugate_1]
    exact rowProduct_mem _ _
  · change witness 2 * rowElement 20 2 * (witness 2)⁻¹ ∈ ambient 20
    rw [conjugate_2]
    exact rowProduct_mem _ _
  · change witness 2 * rowElement 20 3 * (witness 2)⁻¹ ∈ ambient 20
    rw [conjugate_3]
    exact rowProduct_mem _ _
  · change witness 2 * rowElement 20 4 * (witness 2)⁻¹ ∈ ambient 20
    rw [conjugate_4]
    exact rowProduct_mem _ _
  · change witness 2 * rowElement 20 5 * (witness 2)⁻¹ ∈ ambient 20
    rw [conjugate_5]
    exact rowProduct_mem _ _

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions
