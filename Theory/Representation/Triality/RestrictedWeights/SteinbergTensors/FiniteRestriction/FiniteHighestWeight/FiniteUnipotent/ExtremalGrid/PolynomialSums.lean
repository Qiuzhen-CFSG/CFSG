module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Scalar sums on products of finite fields

A monomial sums to zero when its exponent in one coordinate is less than the
size of that coordinate field minus one. Consequently a polynomial whose other
monomials have such a coordinate has grid sum equal to its top coefficient,
up to the sign determined by the number of coordinates. A positive weighted
degree bound suffices; separate degree bounds on every variable are not needed.

The fields may differ between coordinates. This accommodates the cubic and
singleton root orbits of twisted D4 without identifying the group with a grid.
The later cell comparison must supply actual coordinates and a covariant
regular function. Source context: Steinberg, `Chapter2St2.tex`, Sections
13.2(d) and 13.3(a); the scalar argument is finite-field power summation.
-/

@[expose] public noncomputable section
open scoped BigOperators
open MvPolynomial
open scoped Classical

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.PolynomialSums
variable {k σ : Type*} [Field k] [Fintype σ]
variable (F : σ → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
variable (ι : ∀ i, F i →+* k)

def topExponent : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => Fintype.card (F i) - 1)

omit [∀ i, Field (F i)] in
@[simp] theorem topExponent_apply (i : σ) :
    topExponent F i = Fintype.card (F i) - 1 := rfl

omit [Fintype σ] in
theorem mapped_sum_power (i : σ) :
    (∑ x : F i, (ι i x) ^ (Fintype.card (F i) - 1)) = -1 := by
  classical
  have hpos : 0 < Fintype.card (F i) - 1 := by
    have := Fintype.one_lt_card (α := F i)
    omega
  have h : (∑ x : F i, x ^ (Fintype.card (F i) - 1)) = -1 := by
    calc
      _ = ∑ x : F i, (1 - if x = 0 then (1 : F i) else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : x = 0
        · simp [h, zero_pow hpos.ne']
        · simp [h, FiniteField.pow_card_sub_one_eq_one x h]
      _ = -1 := by simp [Finset.sum_sub_distrib]
  simpa only [map_sum, map_pow, map_neg, map_one] using congrArg (ι i) h

omit [Fintype σ] in
theorem mapped_sum_power_lt (i : σ) (m : ℕ)
    (hm : m < Fintype.card (F i) - 1) :
    (∑ x : F i, (ι i x) ^ m) = 0 := by
  simpa only [map_sum, map_pow, map_zero] using
    congrArg (ι i) (FiniteField.sum_pow_lt_card_sub_one (F i) m hm)

theorem grid_sum_monomial (d : σ →₀ ℕ) (c : k) :
    (∑ x : ∀ i, F i, eval (fun i => ι i (x i)) (monomial d c)) =
      c * ∏ i, ∑ t : F i, (ι i t) ^ d i := by
  classical
  simp only [eval_monomial]
  simp_rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [← Finset.mul_sum, Fintype.prod_sum]

theorem grid_sum_monomial_eq_zero (d : σ →₀ ℕ) (c : k)
    (hd : ∃ i, d i < Fintype.card (F i) - 1) :
    (∑ x : ∀ i, F i, eval (fun i => ι i (x i)) (monomial d c)) = 0 := by
  classical
  rw [grid_sum_monomial]
  obtain ⟨i, hi⟩ := hd
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (mapped_sum_power_lt F ι i (d i) hi),
    mul_zero]

theorem grid_sum_top (c : k) :
    (∑ x : ∀ i, F i,
      eval (fun i => ι i (x i)) (monomial (topExponent F) c)) =
        c * (-1) ^ Fintype.card σ := by
  rw [grid_sum_monomial]
  simp only [topExponent_apply, mapped_sum_power, Finset.prod_const, Finset.card_univ]

theorem grid_sum_eq_top_coefficient (p : MvPolynomial σ k)
    (hp : ∀ d ∈ p.support, d ≠ topExponent F →
      ∃ i, d i < Fintype.card (F i) - 1) :
    (∑ x : ∀ i, F i, eval (fun i => ι i (x i)) p) =
      p.coeff (topExponent F) * (-1) ^ Fintype.card σ := by
  classical
  conv_lhs => arg 2; intro x; rw [← p.support_sum_monomial_coeff]
  simp only [map_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single (topExponent F)]
  · exact grid_sum_top F ι _
  · intro d hd hne
    exact grid_sum_monomial_eq_zero F ι d _ (hp d hd hne)
  · intro hnot
    rw [notMem_support_iff.mp hnot]
    simp

theorem grid_sum_eq_top_coefficient_of_weighted_bound (p : MvPolynomial σ k)
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (hp : ∀ d ∈ p.support,
      (∑ i, w i * d i) ≤ ∑ i, w i * (Fintype.card (F i) - 1)) :
    (∑ x : ∀ i, F i, eval (fun i => ι i (x i)) p) =
      p.coeff (topExponent F) * (-1) ^ Fintype.card σ := by
  apply grid_sum_eq_top_coefficient F ι p
  intro d hd hne
  by_contra! h
  have heq : (∑ i, w i * (Fintype.card (F i) - 1)) = ∑ i, w i * d i :=
    le_antisymm (Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (h i))) (hp d hd)
  have hi := (Finset.sum_eq_sum_iff_of_le
    (fun i (_ : i ∈ (Finset.univ : Finset σ)) => Nat.mul_le_mul_left (w i) (h i))).mp heq
  apply hne
  ext i
  exact (Nat.eq_of_mul_eq_mul_left (hw i) (hi i (Finset.mem_univ i))).symm

theorem grid_sum_ne_zero_of_top_coefficient (p : MvPolynomial σ k)
    (hp : ∀ d ∈ p.support, d ≠ topExponent F →
      ∃ i, d i < Fintype.card (F i) - 1)
    (hc : p.coeff (topExponent F) ≠ 0) :
    (∑ x : ∀ i, F i, eval (fun i => ι i (x i)) p) ≠ 0 := by
  rw [grid_sum_eq_top_coefficient F ι p hp]
  exact mul_ne_zero hc (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.PolynomialSums
