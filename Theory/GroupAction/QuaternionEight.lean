module

public import Theory.GroupTheory.SpecificGroups.QuaternionEightInvolution
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

/-!
# The minimum faithful permutation degree of the quaternion group

In an action of the quaternion group of order eight on fewer than eight
points, every stabilizer is nontrivial. Every nontrivial quaternion subgroup
contains the unique involution, so that involution acts trivially.

This is the permutation obstruction used in Wong (1964), Theorem 6(a),
p.108, DOI 10.1017/S1446788700022771.
-/

namespace QuaternionGroup

/-- Every nontrivial subgroup of the quaternion group contains its involution. -/
public theorem a_two_mem_of_ne_bot (H : Subgroup (QuaternionGroup 2)) (hH : H ≠ ⊥) :
    a 2 ∈ H := by
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
  have h : ∀ x : QuaternionGroup 2, x ≠ 1 → x = a 2 ∨ x ^ 2 = a 2 := by decide
  rcases h x (fun heq => hx1 (Subtype.ext heq)) with h | h
  · exact h ▸ x.property
  · exact h ▸ H.pow_mem x.property 2

/-- On fewer than eight points the quaternion involution fixes every point. -/
public theorem a_two_smul_eq_of_card_lt_eight {X : Type*} [Finite X]
    [MulAction (QuaternionGroup 2) X] (hX : Nat.card X < 8) (x : X) :
    (a 2 : QuaternionGroup 2) • x = x := by
  apply a_two_mem_of_ne_bot (MulAction.stabilizer (QuaternionGroup 2) x)
  intro hbot
  have hbound : Nat.card (MulAction.orbit (QuaternionGroup 2) x) ≤ Nat.card X :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hindex := MulAction.index_stabilizer (QuaternionGroup 2) x
  rw [hbot, Subgroup.index_bot, Nat.card_eq_fintype_card, card] at hindex
  change 4 * 2 = Nat.card (MulAction.orbit (QuaternionGroup 2) x) at hindex
  omega

/-- A faithful action of the quaternion group of order eight needs at least
eight points. -/
public theorem eight_le_card_of_faithfulSMul {X : Type*} [Finite X]
    [MulAction (QuaternionGroup 2) X] [FaithfulSMul (QuaternionGroup 2) X] :
    8 ≤ Nat.card X := by
  by_contra h
  have heq : (a 2 : QuaternionGroup 2) = 1 := eq_of_smul_eq_smul fun x : X => by
    simpa only [one_smul] using a_two_smul_eq_of_card_lt_eight (by omega) x
  exact (by decide : (a 2 : QuaternionGroup 2) ≠ 1) heq

/-- An embedding of the quaternion group into a permutation group requires
at least eight letters. -/
public theorem eight_le_card_of_injective_permHom {X : Type*} [Finite X]
    (f : QuaternionGroup 2 →* Equiv.Perm X) (hf : Function.Injective f) :
    8 ≤ Nat.card X := by
  let : MulAction (QuaternionGroup 2) X := MulAction.compHom X f
  let : FaithfulSMul (QuaternionGroup 2) X := ⟨fun h => hf (Equiv.ext h)⟩
  exact eight_le_card_of_faithfulSMul

end QuaternionGroup
