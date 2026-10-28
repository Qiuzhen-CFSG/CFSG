module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.CentralInvolutionBounds.Checks

/-!
# Orbit-cell sizes and the trivial terminal stabilizer

The seven cell sizes multiply to 43008; the terminal invariant is injective.
-/
namespace Held.TwoLocalCandidates.CentralInvolutionBounds

open Cores NormalizerGraph.CardBound

public theorem cell0_card : Nat.card {x : Fin 2058 // weight00 x.val = weight00 48} = 42 := by
  rw [cell_card weight00 ⟨48, by decide⟩]
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem cell1_card : Nat.card {x : Fin 2058 // weight11 x.val = weight11 191} = 8 := by
  rw [cell_card weight11 ⟨191, by decide⟩]
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem cell2_card : Nat.card {x : Fin 2058 // weight21 x.val = weight21 877} = 2 := by
  rw [cell_card weight21 ⟨877, by decide⟩]
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem cell3_card : Nat.card {x : Fin 2058 // weight31 x.val = weight31 65} = 4 := by
  rw [cell_card weight31 ⟨65, by decide⟩]
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem cell4_card : Nat.card {x : Fin 2058 // weight41 x.val = weight41 0} = 4 := by
  rw [cell_card weight41 ⟨0, by decide⟩]
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem cell5_card : Nat.card {x : Fin 2058 // weight51 x.val = weight51 1} = 2 := by
  rw [cell_card weight51 ⟨1, by decide⟩]
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem cell6_card : Nat.card {x : Fin 2058 // weight61 x.val = weight61 2} = 2 := by
  rw [cell_card weight61 ⟨2, by decide⟩]
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

private theorem decode_final : ∀ x : Fin 2058, decodeFinal (weight71 x.val) = x.val := by
  apply allLetters
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem seven_fixed_eq_one (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphCentralizer) (hf : ∀ b ∈ [48, 191, 877, 65, 0, 1, 2], σ b = b) : σ = 1 :=
  discrete_eq_one invariant71 decodeFinal decode_final σ hσ hf
end Held.TwoLocalCandidates.CentralInvolutionBounds
