module

public import Theory.GroupTheory.Perm.PrimeDegreeNormalizer
public import Theory.Mathieu.M23.Properties.Order
public import Mathlib.NumberTheory.Divisors

/-!
# The odd-subgroup obstruction in M23

An odd subgroup with order divisible by 3795 would have order 3795, 11385,
26565, or 79695. Its faithful degree-23 action makes its Sylow-23 subgroup
self-centralizing, with normalizer order 23 or 253. Sylow's congruence excludes
all eight possibilities. Only the concrete permutation action and the proved
order of M23 enter this argument.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 5.2.21, printed p.657 (PDF p.674).
-/

namespace Sporadic.Mathieu.M23Geometry

open Subgroup Theory.GroupTheory

/-- No odd-order subgroup of the concrete M23 has order divisible by 3795. -/
public theorem odd_subgroup_card_not_dvd_3795 (H : Subgroup M23) (ho : Odd (Nat.card H)) :
    ¬ 3795 ∣ Nat.card H := by
  intro hd
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  let P : Sylow 23 H := Classical.choice inferInstance
  have hH : Nat.card H ∣ 10200960 := m23_order ▸ H.card_subgroup_dvd_card
  have h23 : 23 ∣ Nat.card H := (by norm_num : 23 ∣ 3795).trans hd
  have hsq : ¬ 23 ^ 2 ∣ Nat.card H := by
    intro h
    have := h.trans hH
    norm_num at this
  have hP := P.card_eq_prime_of_dvd_of_not_sq_dvd h23 hsq
  let f : H →* Equiv.Perm (Fin 23) := M23.subtype.comp H.subtype
  have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  obtain ⟨m, hm, hN⟩ := prime_degree_normalizer_card f hf P hP
  have hmH : m ∣ Nat.card H := (show m ∣ Nat.card (normalizer (P : Set H)) by
    rw [hN]; exact dvd_mul_left _ _).trans (normalizer (P : Set H)).card_subgroup_dvd_card
  have hmo := ho.of_dvd_nat hmH
  have hm' : m = 1 ∨ m = 11 := by
    have ha : ∀ m ∈ Nat.divisors 22, Odd m → m = 1 ∨ m = 11 := by decide +kernel
    exact ha m (Nat.mem_divisors.mpr ⟨hm, by decide⟩) hmo
  have hcong := P.card_div_prime_modEq_of_normalizer_card hN
  have horders : Nat.card H = 3795 ∨ Nat.card H = 11385 ∨ Nat.card H = 26565 ∨
      Nat.card H = 79695 := by
    obtain ⟨k, hk⟩ := hd
    have hkdiv : k ∣ 2688 := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 3795) (hk ▸ hH)
    have hko : Odd k := ho.of_dvd_nat (hk ▸ dvd_mul_left _ _)
    have ha : ∀ k ∈ Nat.divisors 2688, Odd k → k = 1 ∨ k = 3 ∨ k = 7 ∨ k = 21 := by
      decide +kernel
    rcases ha k (Nat.mem_divisors.mpr ⟨hkdiv, by decide⟩) hko with rfl | rfl | rfl | rfl <;>
      omega
  rcases hm' with rfl | rfl <;>
    rcases horders with he | he | he | he <;> norm_num [Nat.ModEq, he] at hcong

end Sporadic.Mathieu.M23Geometry
