module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.Exponent

/-!
# Exponents of binary norm-one tori

The kernel of x ↦ x σ(x) on GF(2^(2n))ˣ consists of elements annihilated
by the power 2^n+1, since σ is the 2^n-power Frobenius. A product of two
such kernels has the same exponent bound. No order bound for the product
is claimed.

The concrete consumer is the orthogonal centralizer branch of
Aschbacher--Smith, 10.1.2(5) and 10.2.3, printed pp.742,745, via
`Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Action`.
-/

@[expose] public section
namespace FiniteField.BinaryNormOne

/-- The multiplicative norm x ↦ x σ(x), with σ the quadratic Frobenius. -/
noncomputable def normHom (n : ℕ) :
    (GaloisField 2 (2 * n))ˣ →*
      (GaloisField 2 (2 * n))ˣ where
  toFun x := x * Units.map
    (iterateFrobeniusEquiv (GaloisField 2 (2 * n)) 2 n).toMonoidHom x
  map_one' := by simp
  map_mul' x y := by simp [mul_comm, mul_left_comm, mul_assoc]

/-- The norm-one subgroup in the specified binary quadratic extension. -/
noncomputable def torus (n : ℕ) := (normHom n).ker

/-- Norm one gives the exponent bound directly from the Frobenius formula. -/
theorem exponent_dvd (n : ℕ) : Monoid.exponent (torus n) ∣ 2 ^ n + 1 := by
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  apply Subtype.ext
  apply Units.ext
  have hx := congrArg Units.val x.property
  change (x.val : GaloisField 2 (2 * n)) *
    iterateFrobeniusEquiv (GaloisField 2 (2 * n)) 2 n x.val = 1 at hx
  rw [iterateFrobeniusEquiv_def] at hx
  change (x.val : GaloisField 2 (2 * n)) ^ (2 ^ n + 1) = 1
  simpa only [pow_succ, mul_comm] using hx

/-- Two norm-one factors have the same exponent bound. -/
theorem pair_exponent_dvd (n : ℕ) :
    Monoid.exponent (torus n × torus n) ∣ 2 ^ n + 1 := by
  rw [Monoid.exponent_prod, lcm_eq_nat_lcm, Nat.lcm_self]
  exact exponent_dvd n


end FiniteField.BinaryNormOne
