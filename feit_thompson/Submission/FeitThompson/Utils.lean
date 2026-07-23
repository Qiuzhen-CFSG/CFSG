module

public import Mathlib.Data.Nat.Prime.Defs

public lemma pow_two_gt_prime {p : ℕ} [Fact p.Prime] : p < p ^ 2 := by
  simpa [pow_two] using
    Nat.mul_lt_mul_of_pos_left (Fact.out : Nat.Prime p).one_lt (Fact.out : Nat.Prime p).pos
