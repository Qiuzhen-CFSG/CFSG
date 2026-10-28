module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.LowerData
public import Theory.SpecificGroups.Held.Model.FourPointBase
import Mathlib.Tactic.FinCases

/-!
# Checked conjugation for distinguished Held row 1

Each identity is verified in the original degree-2058 carrier on its certified
four-point base. The product witnesses are those in `LowerData`, derived from
the unchanged ATLAS words; no GAP result is used as a proof.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_0_0 : ∀ x : Fin 4,
    representation (mappedGenerator 1 0 * rowGenerator 1 0 * (mappedGenerator 1 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 1 (conjugateFactors 1 0 0)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_0_1 : ∀ x : Fin 4,
    representation (mappedGenerator 1 0 * rowGenerator 1 1 * (mappedGenerator 1 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 1 (conjugateFactors 1 0 1)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_0_2 : ∀ x : Fin 4,
    representation (mappedGenerator 1 0 * rowGenerator 1 2 * (mappedGenerator 1 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 1 (conjugateFactors 1 0 2)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_0_3 : ∀ x : Fin 4,
    representation (mappedGenerator 1 0 * rowGenerator 1 3 * (mappedGenerator 1 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 1 (conjugateFactors 1 0 3)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_1_0 : ∀ x : Fin 4,
    representation (mappedGenerator 1 1 * rowGenerator 1 0 * (mappedGenerator 1 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 1 (conjugateFactors 1 1 0)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_1_1 : ∀ x : Fin 4,
    representation (mappedGenerator 1 1 * rowGenerator 1 1 * (mappedGenerator 1 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 1 (conjugateFactors 1 1 1)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_1_2 : ∀ x : Fin 4,
    representation (mappedGenerator 1 1 * rowGenerator 1 2 * (mappedGenerator 1 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 1 (conjugateFactors 1 1 2)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_1_3 : ∀ x : Fin 4,
    representation (mappedGenerator 1 1 * rowGenerator 1 3 * (mappedGenerator 1 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 1 (conjugateFactors 1 1 3)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
public theorem conjugation_1 (t : Fin 2) (j : Fin 6) :
    mappedGenerator 1 t * rowGenerator 1 j * (mappedGenerator 1 t)⁻¹ =
      rowProduct 1 (conjugateFactors 1 t j) := by
  fin_cases t <;> fin_cases j
  · exact eq_of_four_point_images check_0_0
  · exact eq_of_four_point_images check_0_1
  · exact eq_of_four_point_images check_0_2
  · exact eq_of_four_point_images check_0_3
  · simp [rowGenerator, rowWord, distinguished, generatorWords, word,
      rowProduct, conjugateFactors]
  · simp [rowGenerator, rowWord, distinguished, generatorWords, word,
      rowProduct, conjugateFactors]
  · exact eq_of_four_point_images check_1_0
  · exact eq_of_four_point_images check_1_1
  · exact eq_of_four_point_images check_1_2
  · exact eq_of_four_point_images check_1_3
  · simp [rowGenerator, rowWord, distinguished, generatorWords, word,
      rowProduct, conjugateFactors]
  · simp [rowGenerator, rowWord, distinguished, generatorWords, word,
      rowProduct, conjugateFactors]

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities
