module

public import Theory.SpecificGroups.Lyons.GebhardtLocalTowerSetup

/-!
# Assembly of the Gebhardt local order bound

Multiply the order bound for `⟨a,b⟩` by the relative index bounds for
`⟨a,b⟩ ≤ ⟨a,b,c⟩ ≤ ⟨a,b,c,d⟩`. Positivity of both relative indices,
together with finiteness of the bottom subgroup, proves finiteness at each
stage. The three enumeration results remain explicit inputs to this assembly.

Source: Gebhardt, Experimental Mathematics 9 (2000), 333–338, Section 3B.
-/

namespace Lyons.Gebhardt
public section

private theorem finite_card_le_of_tower_step {G : Type*} [Group G]
    (H K : Subgroup G) (hHK : H ≤ K) {m n : ℕ}
    (hH : Finite H ∧ Nat.card H ≤ m)
    (hindex : 0 < H.relIndex K ∧ H.relIndex K ≤ n) :
    Finite K ∧ Nat.card K ≤ m * n := by
  have he : Nat.card H * H.relIndex K = Nat.card K := by
    simpa only [Subgroup.relIndex_bot_left] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) H K bot_le hHK
  have : Finite H := hH.1
  constructor
  · apply Nat.finite_of_card_ne_zero
    rw [← he]
    exact ne_of_gt (Nat.mul_pos Nat.card_pos hindex.1)
  · rw [← he]
    exact Nat.mul_le_mul hH.2 hindex.2

/-- The local tower's three certified bounds suffice for the desired finite
order bound. In particular, both index inputs include finite-index evidence. -/
theorem gebhardtLocalSubgroup_finite_card_le_of_tower_bounds
    (hbase : Finite LocalTower.base ∧ Nat.card LocalTower.base ≤ 480)
    (hparabolic : 0 < LocalTower.base.relIndex LocalTower.parabolic ∧
      LocalTower.base.relIndex LocalTower.parabolic ≤ 3125)
    (hlocal : 0 < LocalTower.parabolic.relIndex localSubgroup ∧
      LocalTower.parabolic.relIndex localSubgroup ≤ 3906) :
    Finite localSubgroup ∧ Nat.card localSubgroup ≤ 5859000000 := by
  have hp := finite_card_le_of_tower_step _ _ LocalTower.base_le_parabolic
    hbase hparabolic
  exact finite_card_le_of_tower_step _ _ LocalTower.parabolic_le_local hp hlocal

end
end Lyons.Gebhardt
