module

public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Basic
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# The two normal order-three directions in S₃ × S₃

A two-perfect subgroup lies in the product of the alternating subgroups,
because its quotient there is a two-group. If its three-part is three,
it has order three. Conjugating a generator by a transposition in the first
coordinate excludes the diagonal lines, leaving exactly the two axes.
The finite permutation calculations are checked by the kernel.

Source application: Aschbacher--Smith, 15.3.40, printed p.1138.
-/

@[expose] public section

open Subgroup
namespace SymmetricThreeProduct

/-- The alternating subgroup, described by the cube equation. -/
def threeCore : Subgroup S3 where
  carrier := {x | x ^ 3 = 1}
  one_mem' := by decide
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

instance : DecidablePred (· ∈ threeCore) := fun _ => inferInstanceAs (Decidable (_ = _))

instance : DecidablePred (· ∈ threeCore.prod threeCore) := fun g =>
  inferInstanceAs (Decidable (g.1 ^ 3 = 1 ∧ g.2 ^ 3 = 1))

instance : threeCore.Normal where
  conj_mem := by decide +kernel

/-- The first normal order-three direction. -/
def leftThree : Subgroup G := threeCore.prod ⊥
/-- The second normal order-three direction. -/
def rightThree : Subgroup G := (⊥ : Subgroup S3).prod threeCore

instance : DecidablePred (· ∈ leftThree) := fun g =>
  inferInstanceAs (Decidable (g.1 ^ 3 = 1 ∧ g.2 = 1))
instance : DecidablePred (· ∈ rightThree) := fun g =>
  inferInstanceAs (Decidable (g.1 = 1 ∧ g.2 ^ 3 = 1))

theorem card_leftThree : Nat.card leftThree = 3 := by rw [Nat.card_eq_fintype_card]; decide
theorem card_rightThree : Nat.card rightThree = 3 := by rw [Nat.card_eq_fintype_card]; decide

private theorem card_threeCore : Nat.card threeCore = 3 := by rw [Nat.card_eq_fintype_card]; decide

private theorem le_threeCore_square_of_twoPerfect (N : Subgroup G)
    (hp : IsPPerfect 2 N) : N ≤ threeCore.prod threeCore := by
  have hc : Nat.card (threeCore.prod threeCore) = 9 := by
    rw [Nat.card_eq_fintype_card]; decide
  have hidx : (threeCore.prod threeCore).index = 4 := by
    have hi := (threeCore.prod threeCore).card_mul_index
    rw [hc, card_group] at hi
    omega
  have hquot : IsPGroup 2 (G ⧸ threeCore.prod threeCore) :=
    IsPGroup.of_card (show Nat.card (G ⧸ threeCore.prod threeCore) = 2 ^ 2 by
      rw [← index_eq_card, hidx]; decide)
  exact (le_pResidual_of_isPPerfect N hp).trans (sInf_le ⟨inferInstance, hquot⟩)

private theorem axis_of_invariant_cycle : ∀ x : G, x ^ 3 = 1 →
    (∃ n : Fin 3, (Equiv.swap (0 : Fin 3) 1, (1 : S3)) * x *
      (Equiv.swap (0 : Fin 3) 1, (1 : S3))⁻¹ = x ^ (n : ℕ)) →
    x.1 = 1 ∨ x.2 = 1 := by decide +kernel

private theorem normal_card_three (N : Subgroup G) [N.Normal] (hc : Nat.card N = 3)
    (hN : N ≤ threeCore.prod threeCore) : N = leftThree ∨ N = rightThree := by
  classical
  have hne : N ≠ ⊥ := by rintro rfl; norm_num at hc
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ N, x ≠ 1 := by
    by_contra! hn
    exact hne (N.eq_bot_iff_forall.mpr hn)
  have ho : orderOf x = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (hc ▸ N.orderOf_dvd_natCard hx) with h | h
    · exact (hx1 (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have hgen : zpowers x = N :=
    eq_of_le_of_card_ge (zpowers_le_of_mem hx) (by rw [Nat.card_zpowers, ho, hc])
  have hcj : (Equiv.swap (0 : Fin 3) 1, (1 : S3)) * x *
      (Equiv.swap (0 : Fin 3) 1, (1 : S3))⁻¹ ∈ zpowers x := by
    rw [hgen]
    exact (inferInstance : N.Normal).conj_mem x hx _
  rw [mem_zpowers_iff_mem_range_orderOf, ho] at hcj
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hcj
  have haxis := axis_of_invariant_cycle x (by simpa only [ho] using pow_orderOf_eq_one x)
    ⟨⟨n, Finset.mem_range.mp hn⟩, he.symm⟩
  rcases haxis with h | h
  · right
    apply eq_of_le_of_card_ge _ (by rw [hc, card_rightThree])
    rw [← hgen]
    exact zpowers_le_of_mem (show x ∈ rightThree from ⟨h, (hN hx).2⟩)
  · left
    apply eq_of_le_of_card_ge _ (by rw [hc, card_leftThree])
    rw [← hgen]
    exact zpowers_le_of_mem (show x ∈ leftThree from ⟨(hN hx).1, h⟩)

/-- These are the only normal two-perfect subgroups whose three-part is three. -/
theorem normal_twoPerfect_threePart (N : Subgroup G) [N.Normal]
    (hp : IsPPerfect 2 N) (hc : 3 ^ (Nat.card N).factorization 3 = 3) :
    N = leftThree ∨ N = rightThree := by
  have hN := le_threeCore_square_of_twoPerfect N hp
  have hd : Nat.card N ∣ 3 ^ 2 := by
    have hh := (N.subgroupOf (threeCore.prod threeCore)).card_subgroup_dvd_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hN).toEquiv] at hh
    convert hh using 1
    rw [Nat.card_eq_fintype_card]; decide
  obtain ⟨k, _, hk⟩ := Nat.dvd_prime_pow Nat.prime_three |>.mp hd
  have hk1 : k = 1 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 3)
    simpa only [hk, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.Prime.factorization_self Nat.prime_three, Finsupp.single_eq_same, mul_one, pow_one] using hc
  exact normal_card_three N (by rw [hk, hk1, pow_one]) hN

end SymmetricThreeProduct
