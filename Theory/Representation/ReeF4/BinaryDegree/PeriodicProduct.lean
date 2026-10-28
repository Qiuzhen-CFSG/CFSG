module

public import Mathlib.Data.Nat.Periodic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The dimension estimate for repeated tensor factors

Let positive integers `a i` repeat with period `s`, and suppose one of them
is at least `b ≥ 2`. The product of `s * t` factors is the `t`-th power of
the first block product. For `s,t > 0`, multiplying this product by `s`
gives at least `b * (s * t)`.

The block product contains a large factor, after reducing its index modulo
`s`. The estimate then follows from `b * t ≤ b ^ t`. This is the numerical
part of binary descent for the exceptional tensor products in GLS3 §2.8,
Corollary 2.8.6(b) and Remark 2.8.8. It makes no assertion that a particular
group's irreducibles admit such tensor products.
-/

public section

namespace Representation.FrobeniusTensor

/-- A product over repeated periods is a power of the product over one period. -/
theorem prod_range_mul_of_periodic {a : ℕ → ℕ} {s : ℕ}
    (ha : Function.Periodic a s) (t : ℕ) :
    (∏ i ∈ Finset.range (s * t), a i) = (∏ i ∈ Finset.range s, a i) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.mul_succ, Finset.prod_range_add, ih, pow_succ]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      simpa only [Nat.cast_id, Nat.mul_comm, Nat.add_comm] using ha.nat_mul t i

private theorem mul_le_pow {b t : ℕ} (hb : 2 ≤ b) (ht : 0 < t) :
    b * t ≤ b ^ t := by
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
      rw [pow_succ]
      have hbt : b ≤ b * t := Nat.le_mul_of_pos_right b ht
      nlinarith

/-- The Schur degree times a repeated tensor product bounds the full field
exponent, even when the Schur field is a proper subfield. -/
theorem mul_prod_range_ge {a : ℕ → ℕ} {s t b : ℕ}
    (hs : 0 < s) (ht : 0 < t) (hb : 2 ≤ b)
    (ha : Function.Periodic a s) (hpos : ∀ i, 0 < a i)
    (hlarge : ∃ i, b ≤ a i) :
    b * (s * t) ≤ s * ∏ i ∈ Finset.range (s * t), a i := by
  obtain ⟨i, hi⟩ := hlarge
  have hblock : b ≤ ∏ j ∈ Finset.range s, a j := by
    have hle := Finset.single_le_prod' (f := a) (s := Finset.range s)
      (fun j _ => hpos j) (Finset.mem_range.mpr (Nat.mod_lt i hs))
    rw [ha.map_mod_nat] at hle
    exact hi.trans hle
  rw [prod_range_mul_of_periodic ha]
  calc
    b * (s * t) = s * (b * t) := by ring
    _ ≤ s * b ^ t := Nat.mul_le_mul_left s (mul_le_pow hb ht)
    _ ≤ s * (∏ j ∈ Finset.range s, a j) ^ t :=
      Nat.mul_le_mul_left s (Nat.pow_le_pow_left hblock t)

end Representation.FrobeniusTensor
