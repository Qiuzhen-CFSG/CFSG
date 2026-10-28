module

public import Theory.GroupTheory.CharacteristicIndexTwoAut
public import Theory.GroupTheory.CyclicTwoAut
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Automorphisms of generalized quaternion two-groups

A generalized quaternion two-group of order greater than eight has a two-group
of automorphisms. Its standard cyclic subgroup has index two and is
characteristic: its generator has order greater than four, whereas every
outside element has order four. Restriction to this cyclic subgroup, using
the characteristic-index-two automorphism lemma, proves the assertion.

This is the elementary automorphism step accompanying the cyclic/quaternion
alternative in Huppert III.8.2.
-/

namespace QuaternionGroup
open Subgroup

private theorem a_mem_zpowers_a_one {n : ℕ} [NeZero n] (i : ZMod (2 * n)) :
    a i ∈ zpowers (a 1 : QuaternionGroup n) := by
  have h := pow_mem (mem_zpowers (a 1 : QuaternionGroup n)) i.val
  simpa only [a_one_pow, ZMod.natCast_zmod_val] using h

private theorem zpowers_a_one_characteristic {n : ℕ} [NeZero n] (hn : 2 < n) :
    (zpowers (a 1 : QuaternionGroup n)).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro f
  apply zpowers_le.mpr
  change f (a 1) ∈ zpowers (a 1 : QuaternionGroup n)
  have hord := f.orderOf_eq (a 1)
  cases he : f (a 1) with
  | a i => exact a_mem_zpowers_a_one i
  | xa i =>
    rw [he, orderOf_xa, orderOf_a_one] at hord
    omega

/-- Apart from order eight, a generalized quaternion two-group has a two-group
of automorphisms. -/
public theorem isPGroup_mulAut_of_two_lt {n : ℕ} (hn : 2 < n)
    (hQ : IsPGroup 2 (QuaternionGroup n)) :
    IsPGroup 2 (MulAut (QuaternionGroup n)) := by
  let : NeZero n := ⟨by omega⟩
  let A := zpowers (a 1 : QuaternionGroup n)
  let : A.Characteristic := zpowers_a_one_characteristic hn
  have hcard : Nat.card A = 2 * n := by
    rw [Nat.card_zpowers, orderOf_a_one]
  have hindex : A.index = 2 := by
    have h := A.index_mul_card
    rw [hcard, Nat.card_eq_fintype_card, card] at h
    have heq : A.index * 2 = 4 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < n)
      (by simpa only [Nat.mul_assoc] using h)
    omega
  exact A.isPGroup_mulAut_of_characteristic_index_two hindex
    (hQ.to_subgroup A) (hQ.to_subgroup A).mulAut_of_isCyclic_two

end QuaternionGroup
