module
public import Theory.SpecificGroups.ReeTwo.SylowCollectedArithmetic
public import Mathlib.Data.Fintype.Card

/-!
# Involutions in the full binary Ree Sylow subgroup

The collected coordinate multiplication computes the square of all 4096
coordinate tuples without repeatedly expanding the semidirect action.
The kernel-checked finite count gives 143 elements of order two.
This separates the native Sylow group in the second-endpoint extension
analysis of Aschbacher–Smith F.1.12 as used in J.4.5.
-/

namespace ReeTwo.SylowModel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem involution_count_check :
    Fintype.card {x : SylowModel // Collected.collectedMul x x=1 ∧ x≠1}=143 := by
  decide +kernel

public theorem involution_card : Nat.card {x : SylowModel // orderOf x=2}=143 := by
  have hp (x:SylowModel) : (orderOf x=2) ↔ (x*x=1 ∧ x≠1) := by
    rw [orderOf_eq_prime_iff]
    simp only [pow_two]
  let e : {x:SylowModel //orderOf x=2}≃{x:SylowModel //x*x=1∧x≠1} :=
    Equiv.subtypeEquivRight hp
  rw [Nat.card_congr e,Nat.card_eq_fintype_card]
  simpa only [Collected.collectedMul_eq] using involution_count_check
end ReeTwo.SylowModel
