module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# Scalar Laurent expressions and formal coefficients

A polynomial agreeing with a finite Laurent expression on `1 + s*t ≠ 0`
can be compared with a multiplicative integral-exponent family of formal power
series. We clear a common denominator, extend the resulting polynomial identity
across the omitted point, and cancel the denominator as a formal-series unit.
This gives the coefficient-shift formula in `rankOne_laurent_series_coeff`.

Specializing the formal-series family to the rescaled integral binomial series
gives `rankOne_laurent_coeff` and its finite-type version
`rankOne_laurent_coeff_fintype`. They hold over every infinite field, including
algebraically closed fields of characteristic two. Binomial coefficients are
formed in ℤ before casting into the field, so negative exponents are allowed.
No factorial division or representation identity is used; zero scalars, the
constant coefficient, and empty sums are included.

Source motivation: the SL₂ root homomorphisms and Gauss decomposition underlying
Steinberg, Representations of algebraic groups (1963), §§2–3.
-/

public noncomputable section
open Polynomial
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension

variable {k ι : Type*} [Field k] [Infinite k]


omit [Infinite k] in
private theorem laurent_clear_scalar (u : k) (hu : u ≠ 0) (m : ℤ) (N : ℕ)
    (h : 0 ≤ m + (N : ℤ)) :
    u ^ m * u ^ N = u ^ (m + (N : ℤ)).toNat := by
  rw [← zpow_natCast u N, ← zpow_add₀ hu]
  simpa only [zpow_natCast] using
    (congrArg (fun z : ℤ => u ^ z) (Int.toNat_of_nonneg h)).symm

private theorem laurent_chart_ext (s : k) {p q : k[X]}
    (h : ∀ t : k, 1 + s * t ≠ 0 → p.eval t = q.eval t) : p = q := by
  have hL : (1 + C s * X : k[X]) ≠ 0 := by
    intro he
    have := congrArg (Polynomial.eval 0) he
    simp at this
  apply mul_left_cancel₀ hL
  apply Polynomial.funext
  intro t
  by_cases ht : 1 + s * t = 0
  · simp [Polynomial.eval_mul, ht]
  · simp only [Polynomial.eval_mul]
    rw [h t ht]

private theorem laurent_clear (S : Finset ι) (c : ι → k) (a : ι → ℕ)
    (m : ι → ℤ) (s : k) (p : k[X]) (N : ℕ)
    (hN : ∀ i ∈ S, 0 ≤ m i + (N : ℤ))
    (h : ∀ t : k, 1 + s * t ≠ 0 →
      p.eval t = ∑ i ∈ S, c i * t ^ a i * (1 + s * t) ^ m i) :
    p * (1 + C s * X) ^ N =
      ∑ i ∈ S, C (c i) * X ^ a i * (1 + C s * X) ^ (m i + (N : ℤ)).toNat := by
  apply laurent_chart_ext s
  intro t ht
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_finsetSum]
  rw [h t ht, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc, laurent_clear_scalar _ ht _ _ (hN i hi)]

private theorem laurent_common_denominator (S : Finset ι) (m : ι → ℤ) :
    ∃ N : ℕ, ∀ i ∈ S, 0 ≤ m i + (N : ℤ) := by
  refine ⟨∑ i ∈ S, (m i).natAbs, ?_⟩
  intro i hi
  have hb : (m i).natAbs ≤ ∑ j ∈ S, (m j).natAbs :=
    Finset.single_le_sum (fun j hj => Nat.zero_le (m j).natAbs) hi
  have hn := neg_le_abs (m i)
  rw [← Int.natCast_natAbs] at hn
  omega

private theorem laurent_series_identity (S : Finset ι) (c : ι → k) (a : ι → ℕ)
    (m : ι → ℤ) (s : k) (p : k[X])
    (B : ℤ → PowerSeries k)
    (hBadd : ∀ x y, B (x + y) = B x * B y)
    (hBnat : ∀ N : ℕ, B (N : ℤ) = (1 + PowerSeries.C s * PowerSeries.X) ^ N)
    (h : ∀ t : k, 1 + s * t ≠ 0 →
      p.eval t = ∑ i ∈ S, c i * t ^ a i * (1 + s * t) ^ m i) :
    (p : PowerSeries k) = ∑ i ∈ S, PowerSeries.C (c i) * PowerSeries.X ^ a i * B (m i) := by
  obtain ⟨N, hN⟩ := laurent_common_denominator S m
  have hp := laurent_clear S c a m s p N hN h
  have hb : IsUnit (B (N : ℤ)) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨B (-(N : ℤ)), ?_⟩
    rw [← hBadd, add_neg_cancel]
    simpa using hBnat 0
  apply hb.mul_right_cancel
  rw [Finset.sum_mul]
  have he := congrArg (Polynomial.coeToPowerSeries.ringHom (R := k)) hp
  simp only [map_mul, map_pow, map_add, map_one, map_sum,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X] at he
  rw [hBnat]
  refine he.trans (Finset.sum_congr rfl ?_)
  intro i hi
  simp only [← hBnat, Int.toNat_of_nonneg (hN i hi), hBadd, mul_assoc]

/-- Transfer a scalar Laurent identity to the coefficients of an integral-exponent
formal-series family with the specified addition and natural-power laws. -/
theorem rankOne_laurent_series_coeff (S : Finset ι) (c : ι → k) (a : ι → ℕ)
    (m : ι → ℤ) (s : k) (p : k[X])
    (B : ℤ → PowerSeries k)
    (hBadd : ∀ x y, B (x + y) = B x * B y)
    (hBnat : ∀ N : ℕ, B (N : ℤ) = (1 + PowerSeries.C s * PowerSeries.X) ^ N)
    (h : ∀ t : k, 1 + s * t ≠ 0 →
      p.eval t = ∑ i ∈ S, c i * t ^ a i * (1 + s * t) ^ m i) (j : ℕ) :
    p.coeff j = ∑ i ∈ S, if a i ≤ j then c i * PowerSeries.coeff (j - a i) (B (m i)) else 0 := by
  have he := congrArg (PowerSeries.coeff j) (laurent_series_identity S c a m s p B hBadd hBnat h)
  simpa only [Polynomial.coeff_coe, map_sum, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', mul_ite, mul_zero] using he

/-- Extract a coefficient from a finite Laurent expression regular at the origin.
Integer binomial coefficients are cast into the field only after their formation.
The statement includes negative exponents, `s = 0`, and an empty index set. -/
theorem rankOne_laurent_coeff (S : Finset ι) (c : ι → k) (a : ι → ℕ)
    (m : ι → ℤ) (s : k) (p : k[X])
    (h : ∀ t : k, 1 + s * t ≠ 0 →
      p.eval t = ∑ i ∈ S, c i * t ^ a i * (1 + s * t) ^ m i) (j : ℕ) :
    p.coeff j = ∑ i ∈ S,
      if a i ≤ j then c i * s ^ (j - a i) * (Ring.choose (m i) (j - a i) : ℤ) else 0 := by
  let B : ℤ → PowerSeries k := fun z =>
    PowerSeries.rescale s (PowerSeries.binomialSeries k z)
  have hBadd : ∀ x y, B (x + y) = B x * B y := by
    intro x y
    simp only [B, PowerSeries.binomialSeries_add, map_mul]
  have hBnat : ∀ N : ℕ,
      B (N : ℤ) = (1 + PowerSeries.C s * PowerSeries.X) ^ N := by
    intro N
    simp only [B, PowerSeries.binomialSeries_nat, map_pow, map_add, map_one,
      PowerSeries.rescale_X]
  have he := rankOne_laurent_series_coeff S c a m s p B hBadd hBnat h j
  simpa only [B, PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff,
    zsmul_eq_mul, mul_one, mul_assoc] using he

/-- The finite-type version of `rankOne_laurent_coeff`. -/
theorem rankOne_laurent_coeff_fintype [Fintype ι] (c : ι → k) (a : ι → ℕ)
    (m : ι → ℤ) (s : k) (p : k[X])
    (h : ∀ t : k, 1 + s * t ≠ 0 →
      p.eval t = ∑ i, c i * t ^ a i * (1 + s * t) ^ m i) (j : ℕ) :
    p.coeff j = ∑ i,
      if a i ≤ j then c i * s ^ (j - a i) * (Ring.choose (m i) (j - a i) : ℤ) else 0 :=
  rankOne_laurent_coeff Finset.univ c a m s p h j

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
