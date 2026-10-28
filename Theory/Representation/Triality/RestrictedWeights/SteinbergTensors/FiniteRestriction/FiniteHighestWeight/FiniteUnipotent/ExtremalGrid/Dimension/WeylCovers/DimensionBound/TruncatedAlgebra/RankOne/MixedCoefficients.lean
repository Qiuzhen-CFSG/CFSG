module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RankOne.LaurentJets
public import Mathlib.Algebra.BigOperators.Intervals
/-!
# Two successive coefficients of the rank-one Laurent expansion

Extracting the second variable first gives degree `b+j-a` in the first.
Its degree-i coefficient forces `a=j-r` and `b=i-r`, leaving the integer
binomial with exponent `m+i-j`. Finite support permits enlarging both ranges,
so the result holds for all i,j, including degrees outside the original bounds.

Source: integral divided-power straightening from SL₂ Gauss decomposition,
as used in Steinberg, *Representations of algebraic groups* (1963), §§2–3.
-/

public noncomputable section
open Polynomial
open scoped BigOperators
open scoped Pointwise
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
variable {k : Type*} [Field k] [Infinite k]

/-- Extract the second coefficient after the Laurent coefficient in the first variable. -/
private theorem mixed_coeff_bounded (M N i j : ℕ) (hi : i < M) (hj : j < N)
    (w : ℕ → ℕ → k) (m : ℤ) (P : k → k[X]) (Q : k[X])
    (hQ : ∀ s, Q.eval s = (P s).coeff j)
    (hP : ∀ s t, 1 + s * t ≠ 0 → (P s).eval t =
      ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range M,
        (t ^ a * s ^ b * (1 + s * t) ^ (m + (b : ℤ) - (a : ℤ))) * w a b) :
    Q.coeff i = ∑ r ∈ Finset.range (min i j + 1),
      ((Ring.choose (m + (i : ℤ) - (j : ℤ)) r : ℤ) : k) * w (j-r) (i-r) := by
  classical
  have hpoly : Q = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range M,
      if a ≤ j then C (w a b * (Ring.choose (m + (b : ℤ) - (a : ℤ)) (j-a) : ℤ)) * X ^ (b+j-a)
      else 0 := by
    apply Polynomial.funext
    intro s
    rw [hQ]
    have h := rankOne_laurent_coeff ((Finset.range N) ×ˢ (Finset.range M))
      (fun ab => s ^ ab.2 * w ab.1 ab.2) Prod.fst
      (fun ab => m + (ab.2 : ℤ) - (ab.1 : ℤ)) s (P s) ?_ j
    · rw [Finset.sum_product] at h
      rw [h]
      simp only [Polynomial.eval_finsetSum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      split_ifs with haj
      · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        rw [show b+j-a = b+(j-a) by omega, pow_add]
        ring
      · simp
    · intro t ht
      rw [hP s t ht]
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
  rw [hpoly]
  simp only [Polynomial.finsetSum_coeff]
  have ha (a : ℕ) (haj : a ≤ j) :
      (∑ b ∈ Finset.range M,
        (C (w a b * (Ring.choose (m + (b : ℤ) - (a : ℤ)) (j-a) : ℤ)) * X ^ (b+j-a)).coeff i) =
      if j-a ≤ i then
        ((Ring.choose (m + (i : ℤ) - (j : ℤ)) (j-a) : ℤ) : k) * w a (i-(j-a)) else 0 := by
    simp only [Polynomial.coeff_C_mul_X_pow]
    by_cases hji : j-a ≤ i
    · rw [if_pos hji, Finset.sum_eq_single (i-(j-a))]
      · rw [if_pos (by omega)]
        rw [show m + ((i-(j-a) : ℕ) : ℤ) - (a : ℤ) = m + (i : ℤ) - (j : ℤ) by omega]
        exact mul_comm _ _
      · intro b hb hne
        rw [if_neg (by omega)]
      · intro hn
        exact (hn (Finset.mem_range.mpr (by omega))).elim
    · rw [if_neg hji]
      apply Finset.sum_eq_zero
      intro b hb
      rw [if_neg (by omega)]
  have hsum : (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range M,
      (if a ≤ j then C (w a b * (Ring.choose (m + (b : ℤ) - (a : ℤ)) (j-a) : ℤ)) * X ^ (b+j-a) else 0).coeff i) =
      ∑ a ∈ Finset.range (j+1),
        if j-a ≤ i then ((Ring.choose (m+(i:ℤ)-(j:ℤ)) (j-a) : ℤ) : k) * w a (i-(j-a)) else 0 := by
    rw [← Finset.sum_subset (Finset.range_mono (by omega : j+1 ≤ N))]
    · apply Finset.sum_congr rfl
      intro a ha'
      have haj : a ≤ j := by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp ha'))
      simp only [if_pos haj]
      exact ha a haj
    · intro a ha' han
      have haj : ¬a ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using han
      simp [haj]
  rw [hsum, ← Finset.sum_range_reflect _ (j+1)]
  simp only [Nat.add_sub_cancel]
  calc
    (∑ r ∈ Finset.range (j+1),
      if j-(j-r) ≤ i then ((Ring.choose (m+(i:ℤ)-(j:ℤ)) (j-(j-r)) : ℤ) : k) *
        w (j-r) (i-(j-(j-r))) else 0) =
      ∑ r ∈ Finset.range (j+1), if r ≤ i then
        ((Ring.choose (m+(i:ℤ)-(j:ℤ)) r : ℤ) : k) * w (j-r) (i-r) else 0 := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Nat.sub_sub_self (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hr)]
    _ = _ := by
      rw [← Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (min_le_right i j) 1))]
      · apply Finset.sum_congr rfl
        intro r hr
        rw [if_pos (by have := Finset.mem_range.mp hr; omega)]
      · intro r hr hnr
        rw [if_neg (by have := Finset.mem_range.mp hr; simp only [Finset.mem_range] at hnr; omega)]
/-- Finite support removes all restrictions on the two requested coefficient degrees. -/
theorem rankOne_mixed_laurent_coeff (M N i j : ℕ)
    (w : ℕ → ℕ → k) (m : ℤ) (P : k → k[X]) (Q : k[X])
    (hM : ∀ a b, M ≤ b → w a b = 0)
    (hN : ∀ a b, N ≤ a → w a b = 0)
    (hQ : ∀ s, Q.eval s = (P s).coeff j)
    (hP : ∀ s t, 1 + s * t ≠ 0 → (P s).eval t =
      ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range M,
        (t ^ a * s ^ b * (1 + s * t) ^ (m + (b : ℤ) - (a : ℤ))) * w a b) :
    Q.coeff i = ∑ r ∈ Finset.range (min i j + 1),
      ((Ring.choose (m + (i : ℤ) - (j : ℤ)) r : ℤ) : k) * w (j-r) (i-r) := by
  apply mixed_coeff_bounded (max M (i+1)) (max N (j+1)) i j (by omega) (by omega) w m P Q hQ
  intro s t ht
  rw [hP s t ht]
  calc
    _ = ∑ a ∈ Finset.range (max N (j+1)), ∑ b ∈ Finset.range M,
        (t ^ a * s ^ b * (1 + s * t) ^ (m + (b : ℤ) - (a : ℤ))) * w a b := by
      apply Finset.sum_subset (Finset.range_mono (le_max_left _ _))
      intro a ha han
      apply Finset.sum_eq_zero
      intro b hb
      rw [hN a b (by simpa only [Finset.mem_range, not_lt] using han), mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_subset (Finset.range_mono (le_max_left _ _))
      intro b hb hbn
      rw [hM a b (by simpa only [Finset.mem_range, not_lt] using hbn), mul_zero]

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
