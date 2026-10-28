module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The characteristic part of the order of GL₂(p)

The formula |GL₂(p)| = p(p−1)(p²−1) shows that its order is not divisible
by p². Consequently normal p-subgroups of its subgroups are Hall subgroups.
This is the counting input to the complement argument for Aschbacher–Smith,
*The Classification of Quasithin Groups*, A.1.25(2), printed p.25.
-/

namespace Matrix.GeneralLinearGroup

/-- The order of GL₂(p) is not divisible by the square of the characteristic. -/
public theorem prime_sq_not_dvd_card {p : ℕ} [Fact p.Prime] :
    ¬ p ^ 2 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := by
  have hp := (Fact.out : p.Prime)
  have hp1 := hp.one_lt
  have hc : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) =
      p * ((p - 1) * (p ^ 2 - 1)) := by
    rw [Matrix.card_GL_field]
    simp only [Fin.prod_univ_two, ZMod.card, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    rw [show p ^ 2 - p = p * (p - 1) by rw [Nat.mul_sub_left_distrib, mul_one, pow_two]]
    ring
  rw [hc, pow_two, Nat.mul_dvd_mul_iff_left hp.pos, hp.dvd_mul]
  rw [not_or]
  constructor
  · exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  · intro hd
    have hsum : p ∣ (p * p - 1) + 1 := by
      rw [Nat.sub_add_cancel (by nlinarith : 1 ≤ p * p)]
      exact dvd_mul_right p p
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right hd).mpr hsum)


end Matrix.GeneralLinearGroup
