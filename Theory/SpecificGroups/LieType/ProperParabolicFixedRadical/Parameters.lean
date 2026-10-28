module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Logic.Function.Iterate

/-!
# Periodic parameters for root orbits

For root maps of the form `x_alpha(t) -> x_{r alpha}(c_alpha t^(p^e_alpha))`,
composition multiplies the nonzero scalar factors and adds the Frobenius
exponents. A positive total exponent gives a nonzero periodic parameter over
an algebraically closed field. Positivity over the common permutation period
also implies positivity over the particular orbit's period.

This calculation retains arbitrary nonzero coefficients and unequal exponents,
including zero exponents on individual roots. It therefore does not impose
untwisted or equal-root-length conventions. The actual root formulas and the
positive exponent sum still have to be supplied from the source sigma setup.

Source: GLS3, §§2.1 and 2.4, including the root formulas of Table 2.4.
-/

namespace Theory.AlgebraicGroup.ProperParabolicFixedRadical

open scoped BigOperators

/-- Positivity over any number of steps implies positivity over a full period
of the chosen root. This lets the common permutation period be replaced by
the actual orbit length before taking an orbit product. -/
public theorem orbit_exponent_sum_pos_of_period
    {A : Type*} (r : Equiv.Perm A) (e : A → ℕ) (α : A)
    (m : ℕ) (hm : 0 < m) (hperiod : (r ^ m) α = α)
    (n : ℕ) (hpositive : 0 < ∑ i ∈ Finset.range n, e ((r ^ i) α)) :
    0 < ∑ i ∈ Finset.range m, e ((r ^ i) α) := by
  by_contra hnot
  have hzero : ∑ i ∈ Finset.range m, e ((r ^ i) α) = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hsmall (i : ℕ) (hi : i < m) : e ((r ^ i) α) = 0 := by
    have hle := Finset.single_le_sum (f := fun j => e ((r ^ j) α))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
    omega
  have hall (i : ℕ) : e ((r ^ i) α) = 0 := by
    induction i using Nat.strong_induction_on with
    | h i ih =>
      by_cases hi : i < m
      · exact hsmall i hi
      · have hmi : m ≤ i := Nat.le_of_not_gt hi
        have heq : (r ^ i) α = (r ^ (i - m)) α := by
          calc
            (r ^ i) α = (r ^ ((i - m) + m)) α := by rw [Nat.sub_add_cancel hmi]
            _ = (r ^ (i - m)) α := by rw [pow_add, Equiv.Perm.mul_apply, hperiod]
        rw [heq]
        exact ih (i - m) (by omega)
  have : ∑ i ∈ Finset.range n, e ((r ^ i) α) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hall i
  omega

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- Solve the nonzero fixed-parameter equation by taking a `(q - 1)`st root
of the inverse coefficient. -/
public theorem exists_nonzero_scaled_power_fixed (c : k) (hc : c ≠ 0)
    (q : ℕ) (hq : 1 < q) : ∃ t : k, t ≠ 0 ∧ c * t ^ q = t := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ (Nat.sub_pos_of_lt hq)
  have ht0 : t ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by omega : q - 1 ≠ 0)] at ht
    exact (inv_ne_zero hc) ht.symm
  refine ⟨t, ht0, ?_⟩
  rw [show q = (q - 1) + 1 by omega, pow_succ, ← mul_assoc, ht,
    mul_inv_cancel₀ hc, one_mul]

omit [IsAlgClosed k] in
/-- Iterating possibly unequal root exponents adds the exponents and retains
a nonzero scalar coefficient. Individual exponents may be zero. -/
public theorem iterate_root_power_parameters
    {A G : Type*} (f : G → G) (x : A → k → G) (r : Equiv.Perm A)
    (p : ℕ) (c : A → k) (e : A → ℕ) (hc : ∀ α, c α ≠ 0)
    (hstep : ∀ α t, f (x α t) = x (r α) (c α * t ^ (p ^ e α)))
    (α : A) (n : ℕ) :
    ∃ a : k, a ≠ 0 ∧ ∀ t : k,
      (f^[n]) (x α t) = x ((r ^ n) α)
        (a * t ^ (p ^ ∑ i ∈ Finset.range n, e ((r ^ i) α))) := by
  induction n with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha, hiter⟩ := ih
    refine ⟨c ((r ^ n) α) * a ^ (p ^ e ((r ^ n) α)),
      mul_ne_zero (hc _) (pow_ne_zero _ ha), ?_⟩
    intro t
    rw [Function.iterate_succ_apply', hiter, hstep, pow_succ', Equiv.Perm.mul_apply]
    congr 1
    rw [Finset.sum_range_succ, pow_add, mul_pow, ← pow_mul]
    exact (mul_assoc _ _ _).symm

/-- A positive exponent sum around a root orbit gives a nonzero periodic
parameter, with no uniform exponent or sign convention assumed. -/
public theorem exists_nonzero_periodic_root_parameter
    {A G : Type*} (f : G → G) (x : A → k → G) (r : Equiv.Perm A)
    (p : ℕ) (hp : 1 < p) (c : A → k) (e : A → ℕ)
    (hc : ∀ α, c α ≠ 0)
    (hstep : ∀ α t, f (x α t) = x (r α) (c α * t ^ (p ^ e α)))
    (α : A) (m : ℕ) (hperiod : (r ^ m) α = α)
    (hexponent : 0 < ∑ i ∈ Finset.range m, e ((r ^ i) α)) :
    ∃ t : k, t ≠ 0 ∧ (f^[m]) (x α t) = x α t := by
  obtain ⟨a, ha, hiter⟩ := iterate_root_power_parameters f x r p c e hc hstep α m
  have hq : 1 < p ^ ∑ i ∈ Finset.range m, e ((r ^ i) α) :=
    Nat.one_lt_pow hexponent.ne' hp
  obtain ⟨t, ht, hfix⟩ := exists_nonzero_scaled_power_fixed a ha _ hq
  refine ⟨t, ht, ?_⟩
  rw [hiter, hperiod, hfix]

end Theory.AlgebraicGroup.ProperParabolicFixedRadical
