module
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting binomial coefficients nonzero modulo a prime

For n < p^m, the number of binomial coefficients in row n not divisible
by the prime p is the product of one plus each of the first m base-p
digits of n. Leading zero digits contribute one, including the empty
digit sequence when m=0 and the row n=0.

The one-digit Lucas congruence separates an admissible index into its
remainder modulo p and its quotient by p. A digit binomial coefficient
is not divisible by p precisely when its lower digit is at most its upper
digit, by the factorial formula. The resulting quotient/remainder
bijection gives a cardinal recurrence, whose induction yields the product.

This field-independent counting lemma supplies the dimension count for
concrete SL2 highest-weight spans. Its number-theoretic input is Mathlib's
Lucas theorem in `Mathlib.Data.Nat.Choose.Lucas`.
-/

namespace Nat

private theorem not_dvd_choose_digit {p a b : ℕ} (hp : p.Prime) (ha : a < p) :
    ¬ p ∣ a.choose b ↔ b ≤ a := by
  constructor
  · intro h
    by_contra hab
    exact h (by rw [Nat.choose_eq_zero_of_lt (by omega)]; exact dvd_zero p)
  · intro hba hd
    have hf : p ∣ a.factorial := by
      rw [← Nat.choose_mul_factorial_mul_factorial hba]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
    exact (Nat.not_le_of_lt ha) (hp.dvd_factorial.mp hf)

private theorem not_dvd_choose_iff_mod_div {p n r : ℕ} (hp : p.Prime) :
    ¬ p ∣ n.choose r ↔ r % p ≤ n % p ∧ ¬ p ∣ (n / p).choose (r / p) := by
  let : Fact p.Prime := ⟨hp⟩
  have h := (Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (p := p) (n := n) (k := r)).dvd_iff (dvd_refl p)
  rw [h, hp.dvd_mul, not_or, not_dvd_choose_digit hp (Nat.mod_lt n hp.pos)]

private def notDvdChooseEquiv (p n : ℕ) (hp : p.Prime) :
    {r : Fin (n + 1) // ¬ p ∣ n.choose (r : ℕ)} ≃
      Fin (n % p + 1) × {r : Fin (n / p + 1) // ¬ p ∣ (n / p).choose (r : ℕ)} where
  toFun r :=
    (⟨(r.val : ℕ) % p, Nat.lt_succ_of_le ((not_dvd_choose_iff_mod_div hp).mp r.property).1⟩,
      ⟨⟨(r.val : ℕ) / p, Nat.lt_succ_of_le (Nat.div_le_div_right r.val.is_le)⟩,
        ((not_dvd_choose_iff_mod_div hp).mp r.property).2⟩)
  invFun r := by
    have ha : (r.1 : ℕ) < p :=
      r.1.is_lt.trans_le (Nat.succ_le_of_lt (Nat.mod_lt n hp.pos))
    have hbound : (r.1 : ℕ) + p * (r.2.val : ℕ) ≤ n := by
      calc
        (r.1 : ℕ) + p * (r.2.val : ℕ) ≤ n % p + p * (n / p) :=
          Nat.add_le_add r.1.is_le (Nat.mul_le_mul_left p r.2.val.is_le)
        _ = n := Nat.mod_add_div n p
    refine ⟨⟨(r.1 : ℕ) + p * (r.2.val : ℕ), Nat.lt_succ_of_le hbound⟩, ?_⟩
    apply (not_dvd_choose_iff_mod_div hp).mpr
    simpa [Nat.add_mod, Nat.mod_eq_of_lt ha, Nat.add_mul_div_left,
      hp.pos, Nat.div_eq_of_lt ha] using And.intro r.1.is_le r.2.property
  left_inv r := by
    apply Subtype.ext
    apply Fin.ext
    exact Nat.mod_add_div (r.val : ℕ) p
  right_inv r := by
    have ha : (r.1 : ℕ) < p :=
      r.1.is_lt.trans_le (Nat.succ_le_of_lt (Nat.mod_lt n hp.pos))
    apply Prod.ext
    · apply Fin.ext
      simp [Nat.add_mod, Nat.mod_eq_of_lt ha]
    · apply Subtype.ext
      apply Fin.ext
      simp [Nat.add_mul_div_left, hp.pos, Nat.div_eq_of_lt ha]

/-- Lucas's theorem counts the nonzero coefficients by independent base-p digits. -/
public theorem card_not_dvd_choose_eq_prod_digits (p : ℕ) (hp : p.Prime)
    (n m : ℕ) (hn : n < p ^ m) :
    Nat.card {r : Fin (n + 1) // ¬ p ∣ n.choose (r : ℕ)} =
      ∏ i : Fin m, (n / p ^ (i : ℕ) % p + 1) := by
  induction m generalizing n with
  | zero =>
      have hn0 : n = 0 := by simpa using hn
      subst n
      simp [hp.not_dvd_one]
  | succ m ih =>
      have hdiv : n / p < p ^ m := by
        apply Nat.div_lt_of_lt_mul
        simpa only [pow_succ, mul_comm] using hn
      rw [Nat.card_congr (notDvdChooseEquiv p n hp), Nat.card_prod, Nat.card_fin,
        ih (n / p) hdiv, Fin.prod_univ_succ]
      simp only [Fin.val_zero, pow_zero, Nat.div_one]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      simp only [Fin.val_succ, pow_succ, Nat.div_div_eq_div_mul, mul_comm]

end Nat
