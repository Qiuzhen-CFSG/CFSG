module

public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphCardBound.Checks

/-!
# Orbit cells and the terminal four-point certificate

The certified invariant cells of points 1, 2, 3 have sizes 425, 256, 36.
After fixing 0, 1, 2, 3, eight singleton cells give fixed vertices whose
adjacencies, together with the second refinement, separate all 2058 points.
No symmetry or regularity assumption about the relation is needed.

-/

namespace Held.NormalizerGraph.CardBound

public theorem cell1_card : Nat.card {x : Fin 2058 // weight11 x.val = weight11 1} = 425 := by
  rw [cell_card weight11 ⟨1, by decide⟩]
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem cell2_card : Nat.card {x : Fin 2058 // weight22 x.val = weight22 2} = 256 := by
  rw [cell_card weight22 ⟨2, by decide⟩]
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem cell3_card : Nat.card {x : Fin 2058 // weight33 x.val = weight33 3} = 36 := by
  rw [cell_card weight33 ⟨3, by decide⟩]
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem singleton_separators : ∀ b ∈ separators, ∀ x : Fin 2058,
    weight42 x.val = weight42 b.val → x = b := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem decode_final : ∀ x : Fin 2058,
    decodeFinal (weight42 x.val + 2^64 * baseSignature separators x) = x.val := by
  decide +kernel

public theorem four_fixed_eq_one (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ preservingGroup) (hf : Fixes 4 σ) : σ = 1 :=
  fixes_eq_one invariant42 separators singleton_separators decodeFinal decode_final σ hσ hf

end Held.NormalizerGraph.CardBound
