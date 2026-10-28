module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.LowerData
public import Theory.SpecificGroups.Held.Model.FourPointBase
import Mathlib.Tactic.FinCases

/-!
# Checked conjugation for distinguished Held row 4

Each identity is verified in the original degree-2058 carrier on its certified
four-point base. The product witnesses are those in `LowerData`, derived from
the unchanged ATLAS words; no GAP result is used as a proof.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_0_0 : ∀ x : Fin 4,
    representation (mappedGenerator 4 0 * rowGenerator 4 0 * (mappedGenerator 4 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 4 (conjugateFactors 4 0 0)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_0_1 : ∀ x : Fin 4,
    representation (mappedGenerator 4 0 * rowGenerator 4 1 * (mappedGenerator 4 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 4 (conjugateFactors 4 0 1)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_0_2 : ∀ x : Fin 4,
    representation (mappedGenerator 4 0 * rowGenerator 4 2 * (mappedGenerator 4 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 4 (conjugateFactors 4 0 2)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_0_3 : ∀ x : Fin 4,
    representation (mappedGenerator 4 0 * rowGenerator 4 3 * (mappedGenerator 4 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 4 (conjugateFactors 4 0 3)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_0_4 : ∀ x : Fin 4,
    representation (mappedGenerator 4 0 * rowGenerator 4 4 * (mappedGenerator 4 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 4 (conjugateFactors 4 0 4)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_0_5 : ∀ x : Fin 4,
    representation (mappedGenerator 4 0 * rowGenerator 4 5 * (mappedGenerator 4 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 4 (conjugateFactors 4 0 5)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_1_0 : ∀ x : Fin 4,
    representation (mappedGenerator 4 1 * rowGenerator 4 0 * (mappedGenerator 4 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 4 (conjugateFactors 4 1 0)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_1_1 : ∀ x : Fin 4,
    representation (mappedGenerator 4 1 * rowGenerator 4 1 * (mappedGenerator 4 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 4 (conjugateFactors 4 1 1)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_1_2 : ∀ x : Fin 4,
    representation (mappedGenerator 4 1 * rowGenerator 4 2 * (mappedGenerator 4 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 4 (conjugateFactors 4 1 2)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_1_3 : ∀ x : Fin 4,
    representation (mappedGenerator 4 1 * rowGenerator 4 3 * (mappedGenerator 4 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 4 (conjugateFactors 4 1 3)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_1_4 : ∀ x : Fin 4,
    representation (mappedGenerator 4 1 * rowGenerator 4 4 * (mappedGenerator 4 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 4 (conjugateFactors 4 1 4)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem check_1_5 : ∀ x : Fin 4,
    representation (mappedGenerator 4 1 * rowGenerator 4 5 * (mappedGenerator 4 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 4 (conjugateFactors 4 1 5)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
public theorem conjugation_4 (t : Fin 2) (j : Fin 6) :
    mappedGenerator 4 t * rowGenerator 4 j * (mappedGenerator 4 t)⁻¹ =
      rowProduct 4 (conjugateFactors 4 t j) := by
  fin_cases t <;> fin_cases j
  · exact eq_of_four_point_images check_0_0
  · exact eq_of_four_point_images check_0_1
  · exact eq_of_four_point_images check_0_2
  · exact eq_of_four_point_images check_0_3
  · exact eq_of_four_point_images check_0_4
  · exact eq_of_four_point_images check_0_5
  · exact eq_of_four_point_images check_1_0
  · exact eq_of_four_point_images check_1_1
  · exact eq_of_four_point_images check_1_2
  · exact eq_of_four_point_images check_1_3
  · exact eq_of_four_point_images check_1_4
  · exact eq_of_four_point_images check_1_5

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities
