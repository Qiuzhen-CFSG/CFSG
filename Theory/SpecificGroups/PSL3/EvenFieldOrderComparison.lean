module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-!
# Comparing the orders of degree-three projective groups over even fields

The scalar kernel has order between one and three. Doubling the field order
increases the numerator q³(q³−1)(q²−1) by more than a factor of three, so
PSL₃(2^f) has nondecreasing order as the positive exponent f increases.
This comparison detects strict parameter descent from an injection into a
proper subgroup, without assuming a subgroup classification or a subfield map.

The underlying order computation is in `LinearThreeSylow.Order`.
Application: GLS3, Theorem 6.5.3(f), `refs/KGroup/GLS3/chapter6.tex`.
-/

namespace Matrix.PSL3.LinearThree

open scoped MatrixGroups

/-- Doubling the field order outweighs every possible scalar-kernel factor. -/
public theorem order_polynomial_growth {a b : ℕ} (ha : 1 < a) (hab : 2 * a ≤ b) :
    3 * (a ^ 3 * (a ^ 3 - 1) * (a ^ 2 - 1)) <
      b ^ 3 * (b ^ 3 - 1) * (b ^ 2 - 1) := by
  have ha0 : 0 < a := by omega
  have h3 : 3 * a ^ 3 < b ^ 3 := by
    calc
      3 * a ^ 3 < 8 * a ^ 3 := by nlinarith [pow_pos ha0 3]
      _ = (2 * a) ^ 3 := by ring
      _ ≤ b ^ 3 := Nat.pow_le_pow_left hab 3
  have hab' : a ≤ b := by omega
  have ha3 : 0 < a ^ 3 - 1 := by
    have := Nat.pow_le_pow_left (show 2 ≤ a by omega) 3
    omega
  have ha2 : 0 < a ^ 2 - 1 := by
    have := Nat.pow_le_pow_left (show 2 ≤ a by omega) 2
    omega
  calc
    3 * (a ^ 3 * (a ^ 3 - 1) * (a ^ 2 - 1)) =
        (3 * a ^ 3) * (a ^ 3 - 1) * (a ^ 2 - 1) := by ring
    _ < b ^ 3 * (a ^ 3 - 1) * (a ^ 2 - 1) :=
      Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right h3 ha3) ha2
    _ ≤ b ^ 3 * (b ^ 3 - 1) * (b ^ 2 - 1) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.pow_le_pow_left hab' 3) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hab' 2) 1)

public theorem card_even_mono {f m : ℕ} (hf : 0 < f) (hfm : f ≤ m)
    (F E : Type*) [Field F] [Finite F] [Field E] [Finite E]
    (hF : Nat.card F = 2 ^ f) (hE : Nat.card E = 2 ^ m) :
    Nat.card PSL(3,F) ≤ Nat.card PSL(3,E) := by
  rcases hfm.eq_or_lt with rfl | hfm
  · rw [card_projective F, card_projective E, hF, hE]
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow_iff.mpr (by omega)
  have hg := order_polynomial_growth hq (show 2 * 2 ^ f ≤ 2 ^ m from by
    rw [mul_comm, ← pow_succ]
    exact Nat.pow_le_pow_right (by decide) hfm)
  have h1 := card_projective_mul_scalar F
  have h2 := card_projective_mul_scalar E
  rw [hF] at h1
  rw [hE] at h2
  have hd1 : 1 ≤ Nat.gcd 3 (2 ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by decide)
  have hd2 : Nat.gcd 3 (2 ^ m - 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
  have hl : Nat.card PSL(3,F) ≤ (2 ^ f) ^ 3 * ((2 ^ f) ^ 3 - 1) * ((2 ^ f) ^ 2 - 1) := by
    calc
      Nat.card PSL(3,F) ≤ Nat.card PSL(3,F) * Nat.gcd 3 (2 ^ f - 1) := Nat.le_mul_of_pos_right _ hd1
      _ = _ := h1
  have hr : (2 ^ m) ^ 3 * ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) ≤ 3 * Nat.card PSL(3,E) := by
    rw [← h2, mul_comm]
    exact Nat.mul_le_mul_right _ hd2
  omega


end Matrix.PSL3.LinearThree
