module

public import Theory.GroupAction.FiveActionMinimalOrder

/-!
# A nontrivial five-action with a nonidentity fixed point needs order 32

The minimum order is sixteen. At order sixteen the action has trivial
fixed subgroup. Since the group order is a power of two, a nonidentity
fixed point therefore raises the lower bound to thirty-two.
-/

public section
namespace Theory.GroupAction

theorem thirty_two_le_card_of_five_action_fixed
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hA : Nat.card A = 5) (hV : IsPGroup 2 V)
    (hmove : FixedPoints.subgroup A V ≠ ⊤)
    (hfixed : FixedPoints.subgroup A V ≠ ⊥) : 32 ≤ Nat.card V := by
  have hlo := sixteen_le_card_of_five_action_nontrivial hA hV hmove
  obtain ⟨n, hn⟩ := hV.exists_card_eq
  have hneq : Nat.card V ≠ 16 := fun h =>
    hfixed (fixed_eq_bot_of_five_action_card_sixteen hA h hmove)
  rw [hn] at hlo hneq ⊢
  have hn4 : 4 ≤ n := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hlo
  have hn5 : 5 ≤ n := by
    by_contra h
    have : n = 4 := by omega
    exact hneq (by rw [this]; decide)
  change 2 ^ 5 ≤ 2 ^ n
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr hn5

end Theory.GroupAction
