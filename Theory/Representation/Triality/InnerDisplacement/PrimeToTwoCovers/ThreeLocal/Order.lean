module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Tactic.NormNum.Prime

/-!
# Triality torus indices at the prime three

The actual fixed Bruhat count gives the indices of tori of orders
(q³ − 1)(q − 1) and (q³ + 1)(q + 1). In the corresponding congruence class
modulo three, the index is not divisible by nine. Consequently its Sylow
three subgroup needs exactly one additional factor of three, independently
of the valuation of q − 1 or q + 1.

The split torus is the already constructed subgroup of the original carrier.
The nonsplit calculation takes a subgroup with the specified order; its
construction and actions remain the responsibility of the nonsplit branch.
At q = 2, the actual Sylow order is 81, ruling out a normalized torus of
order nine with a supplement of order three.

Source: GLS3 §6.1, Theorem 6.1.4 and Tables 6.1.2–3; the carrier order is
derived from the fixed Bruhat cells of GLS3 §§2.3–2.4.
-/

public section

namespace Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal

open Standard ConcreteBruhat Parabolics Subgroup

/-- The order formula for the literal binary graph-field carrier. -/
theorem card_binaryCarrier (n : ℕ) (hn : 0 < n) :
    Nat.card (BinaryCarrier n hn) =
      (2 ^ n) ^ 12 * (((2 ^ n) ^ 3 - 1) * (2 ^ n - 1)) *
        (((2 ^ n) ^ 3 + 1) * (2 ^ n + 1) * ((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1)) := by
  rw [FixedCellCount.card_carrier n hn, FixedCellCount.card_borel]
  simp only [binaryParameters_q]

/-- Exact ambient index of the existing split torus. -/
theorem split_torus_index (n : ℕ) (hn : 0 < n) :
    (torus (binaryParameters n hn)).index =
      (2 ^ n) ^ 12 * (((2 ^ n) ^ 3 + 1) * (2 ^ n + 1) *
        ((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1)) := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := torus (binaryParameters n hn)))
  rw [card_mul_index, FixedCellCount.card_carrier n hn, FixedCellCount.card_borel n hn,
    TorusCoordinates.card_torus _ rfl]
  simp only [binaryParameters_q]
  ring

/-- The nonsplit order specifies the exact index of an actual carrier subgroup. -/
theorem nonsplit_torus_index (n : ℕ) (hn : 0 < n) (A : Subgroup (BinaryCarrier n hn))
    (hA : Nat.card A = ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1)) :
    A.index = (2 ^ n) ^ 12 * (((2 ^ n) ^ 3 - 1) * (2 ^ n - 1) *
      ((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1)) := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := A))
  rw [card_mul_index, card_binaryCarrier n hn, hA]
  ring

private theorem split_mod (q : ℕ) (hq : q % 3 = 1) :
    ¬ 9 ∣ q ^ 12 * ((q ^ 3 + 1) * (q + 1) * (q ^ 8 + q ^ 4 + 1)) := by
  have hcalc : ∀ a : Fin 9, a.val % 3 = 1 →
      (a.val ^ 12 * ((a.val ^ 3 + 1) * (a.val + 1) *
        (a.val ^ 8 + a.val ^ 4 + 1))) % 9 ≠ 0 := by decide +kernel
  have hq9 : (q % 9) % 3 = 1 := by
    simpa only [Nat.mod_mod_of_dvd q (by decide : 3 ∣ 9)] using hq
  have h := hcalc ⟨q % 9, Nat.mod_lt _ (by decide)⟩ hq9
  simpa only [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod, Nat.pow_mod,
    Nat.mod_mod, Nat.mod_eq_of_lt (by decide : 1 < 9)] using h

private theorem nonsplit_mod (q : ℕ) (hqpos : 1 ≤ q) (hq : q % 3 = 2) :
    ¬ 9 ∣ q ^ 12 * ((q ^ 3 - 1) * (q - 1) * (q ^ 8 + q ^ 4 + 1)) := by
  have hcalc : ∀ a : Fin 9, a.val % 3 = 2 →
      (a.val ^ 12 * ((a.val ^ 3 + 8) * (a.val + 8) *
        (a.val ^ 8 + a.val ^ 4 + 1))) % 9 ≠ 0 := by decide +kernel
  have hq9 : (q % 9) % 3 = 2 := by
    simpa only [Nat.mod_mod_of_dvd q (by decide : 3 ∣ 9)] using hq
  have h := hcalc ⟨q % 9, Nat.mod_lt _ (by decide)⟩ hq9
  have hmod (m : ℕ) (hm : 1 ≤ m) : (m - 1) % 9 = (m + 8) % 9 := by omega
  have hpow : 1 ≤ q ^ 3 := Nat.one_le_pow 3 q hqpos
  simpa only [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, hmod q hqpos, hmod (q ^ 3) hpow,
    Nat.add_mod, Nat.pow_mod, Nat.mod_mod, Nat.mod_eq_of_lt (by decide : 1 < 9),
    Nat.mod_eq_of_lt (by decide : 8 < 9)] using h

/-- No restriction on the three-adic valuation of q − 1 is imposed. -/
theorem nine_not_dvd_split_torus_index (n : ℕ) (hn : 0 < n) (hd : 3 ∣ 2 ^ n - 1) :
    ¬ 9 ∣ (torus (binaryParameters n hn)).index := by
  rw [split_torus_index]
  apply split_mod
  have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  obtain ⟨k, hk⟩ := hd
  omega

/-- No restriction on the three-adic valuation of q + 1 is imposed. -/
theorem nine_not_dvd_nonsplit_torus_index (n : ℕ) (hn : 0 < n)
    (A : Subgroup (BinaryCarrier n hn))
    (hA : Nat.card A = ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1)) (hd : 3 ∣ 2 ^ n + 1) :
    ¬ 9 ∣ A.index := by
  rw [nonsplit_torus_index n hn A hA]
  apply nonsplit_mod _ (Nat.one_le_pow n 2 (by decide))
  obtain ⟨k, hk⟩ := hd
  omega

/-- Every binary parameter belongs to one of the two torus branches. -/
theorem three_dvd_sub_one_or_add_one (n : ℕ) : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
  have hnot : ¬ 3 ∣ 2 ^ n :=
    fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  simp only [Nat.dvd_iff_mod_eq_zero] at hnot ⊢
  omega

/-- The fixed-cell count includes the smallest parameter: its Sylow order is 81. -/
theorem card_three_sylow_at_two (Q : Sylow 3 (BinaryCarrier 1 (by decide))) :
    Nat.card Q = 81 := by
  have hc : Nat.card (BinaryCarrier 1 (by decide)) = 2 ^ 12 * 3 ^ 4 * 7 ^ 2 * 13 := by
    rw [card_binaryCarrier]
    norm_num
  rw [Q.card_eq_multiplicity, hc,
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul]
  norm_num

/-- An order-nine torus and an order-three normalizing supplement are too small
at q = 2, even if their intersection is not specified. -/
theorem not_nine_torus_generates_at_two
    (Q : Sylow 3 (BinaryCarrier 1 (by decide)))
    (T : Subgroup (BinaryCarrier 1 (by decide))) (hT : Nat.card T = 9)
    (c : BinaryCarrier 1 (by decide)) (hc : orderOf c = 3)
    (hn : c ∈ normalizer (T : Set (BinaryCarrier 1 (by decide)))) :
    T ⊔ zpowers c ≠ (Q : Subgroup (BinaryCarrier 1 (by decide))) := by
  intro he
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes T (zpowers c) (zpowers_le.mpr hn)
  rw [hT, Nat.card_zpowers, hc, he, card_three_sylow_at_two] at h
  have hpos : 0 < Nat.card (T ⊓ zpowers c : Subgroup (BinaryCarrier 1 (by decide))) := Nat.card_pos
  omega

end Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal
