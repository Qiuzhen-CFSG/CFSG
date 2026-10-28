module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Quaternion-sixteen actions on ternary groups

Let Q₁₆ act on a finite nontrivial 3-group A, with its central involution
acting by inversion. Then |A| is at least 81. This supplies the degree bound
needed in the application of Aschbacher's (45.8) to the odd-kernel quotient
in the degree-three amalgam analysis.

Every nonidentity element of Q₁₆ has a power equal to the central involution.
Inversion fixes only the identity in a 3-group, so the Q₁₆ action is free away
from the identity. The orbit decomposition gives 16 ∣ |A| − 1. The smaller
nontrivial powers of three, namely 3, 9, and 27, fail this divisibility.
The elementary-abelian specialization applies to the actual Frattini quotient
and does not require an additional faithful-action premise.
-/

open MulAction Subgroup

namespace Theory.GroupAction.QuaternionSixteenTernaryDegree

private theorem fixed_eq_one {A : Type*} [Group A] (hA : IsPGroup 3 A)
    (ρ : QuaternionGroup 4 →* MulAut A)
    (hz : ∀ a : A, ρ (QuaternionGroup.a 4) a = a⁻¹)
    (g : QuaternionGroup 4) (hg : g ≠ 1) (a : A) (ha : ρ g a = a) : a = 1 := by
  have hp (n : ℕ) : ρ (g ^ n) a = a := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, map_mul, MulAut.mul_apply, ha, ih]
  have hcases : ∀ g : QuaternionGroup 4, g ≠ 1 →
      g = QuaternionGroup.a 4 ∨ g ^ 2 = QuaternionGroup.a 4 ∨
        g ^ 4 = QuaternionGroup.a 4 := by decide
  have hzfix : ρ (QuaternionGroup.a 4) a = a := by
    rcases hcases g hg with h | h | h
    · rwa [← h]
    · rw [← h]; exact hp 2
    · rw [← h]; exact hp 4
  have hsquare : a ^ 2 = 1 := by
    rw [hz a] at hzfix
    exact (pow_two a).trans (inv_eq_iff_mul_eq_one.mp hzfix)
  by_contra hne
  have hd : 3 ∣ 2 := (hA.dvd_orderOf hne).trans (orderOf_dvd_of_pow_eq_one hsquare)
  norm_num at hd


/-- The quaternion group acts freely on the nonidentity points when its central
involution inverts the ternary group. Thus every such orbit has sixteen points. -/
public theorem sixteen_dvd_card_sub_one {A : Type*} [Group A] [Finite A] (hA : IsPGroup 3 A)
    (ρ : QuaternionGroup 4 →* MulAut A)
    (hz : ∀ a : A, ρ (QuaternionGroup.a 4) a = a⁻¹) :
    16 ∣ Nat.card A - 1 := by
  classical
  let X := {a : A // a ≠ 1}
  let _ : MulAction (QuaternionGroup 4) X := {
    smul g a := ⟨ρ g a, by
      intro heq
      exact a.property ((ρ g).injective (heq.trans (map_one (ρ g)).symm))⟩
    one_smul a := by
      apply Subtype.ext
      change ρ 1 a = a
      simp
    mul_smul g k a := by
      apply Subtype.ext
      change ρ (g * k) a = ρ g (ρ k a)
      simp [MulAut.mul_apply] }
  have hstab (a : X) : stabilizer (QuaternionGroup 4) a = ⊥ := by
    apply eq_bot_iff.mpr
    intro g hg
    apply mem_bot.mpr
    by_contra hne
    exact a.property (fixed_eq_one hA ρ hz g hne a (congrArg Subtype.val hg))
  have hcount := Nat.card_congr (selfEquivOrbitsQuotientProd hstab)
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := QuaternionGroup 4),
    QuaternionGroup.card] at hcount
  have hX : Nat.card X = Nat.card A - 1 := by
    let _ : Fintype A := Fintype.ofFinite A
    change Nat.card {a : A // ¬a = 1} = Nat.card A - 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [Nat.card_eq_fintype_card]
  rw [hX] at hcount
  exact ⟨Nat.card (Quotient (orbitRel (QuaternionGroup 4) X)), by
    simpa only [Nat.mul_comm] using hcount⟩

/-- A nontrivial finite 3-group inverted by the central involution of a
quaternion-sixteen action has at least eighty-one elements. No faithfulness,
commutativity, or elementary-abelian hypothesis is needed. -/
public theorem card_ge_eighty_one_of_inversion {A : Type*} [Group A] [Finite A] [Nontrivial A]
    (hA : IsPGroup 3 A) (ρ : QuaternionGroup 4 →* MulAut A)
    (hz : ∀ a : A, ρ (QuaternionGroup.a 4) a = a⁻¹) : 81 ≤ Nat.card A := by
  have hd := sixteen_dvd_card_sub_one hA ρ hz
  have hnontriv : 1 < Nat.card A := Finite.one_lt_card
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  by_contra hbound
  have hnlt : n < 4 := by
    by_contra h
    have := Nat.pow_le_pow_right (by decide : 0 < 3) (show 4 ≤ n by omega)
    omega
  interval_cases n <;> norm_num [hn] at *

/-- The elementary ternary specialization, with the same marked central
involution and the original automorphism homomorphism. -/
public theorem card_ge_eighty_one_of_elementary_inversion
    {A : Type*} [Group A] [Finite A] [Nontrivial A] [IsElementaryAbelian 3 A]
    (ρ : QuaternionGroup 4 →* MulAut A)
    (hz : ∀ a : A, ρ (QuaternionGroup.a 4) a = a⁻¹) : 81 ≤ Nat.card A :=
  card_ge_eighty_one_of_inversion (IsElementaryAbelian.isPGroup 3 A) ρ hz

end Theory.GroupAction.QuaternionSixteenTernaryDegree
