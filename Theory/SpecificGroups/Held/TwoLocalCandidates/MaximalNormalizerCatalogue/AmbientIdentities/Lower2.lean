module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.LowerData
public import Theory.SpecificGroups.Held.Model.FourPointBase
import Mathlib.Tactic.FinCases

/-!
# Checked conjugation for distinguished Held row 2

Each identity is verified in the original degree-2058 carrier on its certified
four-point base. The product witnesses are those in `LowerData`, derived from
the unchanged ATLAS words; no GAP result is used as a proof.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_0_0 : ∀ x : Fin 4,
    representation (mappedGenerator 2 0 * rowGenerator 2 0 * (mappedGenerator 2 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 2 (conjugateFactors 2 0 0)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_0_1 : ∀ x : Fin 4,
    representation (mappedGenerator 2 0 * rowGenerator 2 1 * (mappedGenerator 2 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 2 (conjugateFactors 2 0 1)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_0_2 : ∀ x : Fin 4,
    representation (mappedGenerator 2 0 * rowGenerator 2 2 * (mappedGenerator 2 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 2 (conjugateFactors 2 0 2)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_0_3 : ∀ x : Fin 4,
    representation (mappedGenerator 2 0 * rowGenerator 2 3 * (mappedGenerator 2 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 2 (conjugateFactors 2 0 3)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_1_0 : ∀ x : Fin 4,
    representation (mappedGenerator 2 1 * rowGenerator 2 0 * (mappedGenerator 2 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 2 (conjugateFactors 2 1 0)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_1_1 : ∀ x : Fin 4,
    representation (mappedGenerator 2 1 * rowGenerator 2 1 * (mappedGenerator 2 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 2 (conjugateFactors 2 1 1)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_1_2 : ∀ x : Fin 4,
    representation (mappedGenerator 2 1 * rowGenerator 2 2 * (mappedGenerator 2 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 2 (conjugateFactors 2 1 2)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_1_3 : ∀ x : Fin 4,
    representation (mappedGenerator 2 1 * rowGenerator 2 3 * (mappedGenerator 2 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 2 (conjugateFactors 2 1 3)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
public theorem conjugation_2 (t : Fin 2) (j : Fin 6) :
    mappedGenerator 2 t * rowGenerator 2 j * (mappedGenerator 2 t)⁻¹ =
      rowProduct 2 (conjugateFactors 2 t j) := by
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
