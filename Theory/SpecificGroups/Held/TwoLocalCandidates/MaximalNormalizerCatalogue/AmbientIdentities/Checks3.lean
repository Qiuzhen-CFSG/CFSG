module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.LowerData
public import Theory.SpecificGroups.Held.Model.FourPointBase
import Mathlib.Tactic.FinCases

/-!
# Checked conjugation for distinguished Held row 3

Each identity is verified in the original degree-2058 carrier on its certified
four-point base. The product witnesses are those in `LowerData`, derived from
the unchanged ATLAS words; no GAP result is used as a proof.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.Checks3

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
public theorem check_0_0 : ∀ x : Fin 4,
    representation (mappedGenerator 3 0 * rowGenerator 3 0 * (mappedGenerator 3 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 3 (conjugateFactors 3 0 0)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
public theorem check_0_1 : ∀ x : Fin 4,
    representation (mappedGenerator 3 0 * rowGenerator 3 1 * (mappedGenerator 3 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 3 (conjugateFactors 3 0 1)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
public theorem check_0_2 : ∀ x : Fin 4,
    representation (mappedGenerator 3 0 * rowGenerator 3 2 * (mappedGenerator 3 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 3 (conjugateFactors 3 0 2)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
public theorem check_0_3 : ∀ x : Fin 4,
    representation (mappedGenerator 3 0 * rowGenerator 3 3 * (mappedGenerator 3 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 3 (conjugateFactors 3 0 3)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
public theorem check_0_4 : ∀ x : Fin 4,
    representation (mappedGenerator 3 0 * rowGenerator 3 4 * (mappedGenerator 3 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 3 (conjugateFactors 3 0 4)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
public theorem check_0_5 : ∀ x : Fin 4,
    representation (mappedGenerator 3 0 * rowGenerator 3 5 * (mappedGenerator 3 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 3 (conjugateFactors 3 0 5)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
public theorem check_1_0 : ∀ x : Fin 4,
    representation (mappedGenerator 3 1 * rowGenerator 3 0 * (mappedGenerator 3 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 3 (conjugateFactors 3 1 0)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
public theorem check_1_1 : ∀ x : Fin 4,
    representation (mappedGenerator 3 1 * rowGenerator 3 1 * (mappedGenerator 3 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 3 (conjugateFactors 3 1 1)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
public theorem check_1_2 : ∀ x : Fin 4,
    representation (mappedGenerator 3 1 * rowGenerator 3 2 * (mappedGenerator 3 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 3 (conjugateFactors 3 1 2)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
public theorem check_1_3 : ∀ x : Fin 4,
    representation (mappedGenerator 3 1 * rowGenerator 3 3 * (mappedGenerator 3 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 3 (conjugateFactors 3 1 3)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
public theorem check_1_4 : ∀ x : Fin 4,
    representation (mappedGenerator 3 1 * rowGenerator 3 4 * (mappedGenerator 3 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 3 (conjugateFactors 3 1 4)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
public theorem check_1_5 : ∀ x : Fin 4,
    representation (mappedGenerator 3 1 * rowGenerator 3 5 * (mappedGenerator 3 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (rowProduct 3 (conjugateFactors 3 1 5)) ⟨x.val, by omega⟩ := by
  decide +kernel

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.Checks3
