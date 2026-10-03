module

public import Theory.Character.AbelianLinearCharacters

/-!
# Squared norms of linear character combinations

First character orthogonality evaluates the unnormalized squared norm of a
real linear combination of distinct linear characters. Expanding both sums
leaves only the diagonal terms. No completeness assumption is needed.
-/

public section
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace AbelianLinearCharacters
variable {A I : Type*} [Group A] [Finite A] [Fintype I]
/-- Parseval's identity for a real linear combination of distinct linear characters. -/
theorem sum_normSq_real_combination (χ : I → A →* ℂ) (hi : Function.Injective χ) (a : I → ℝ) :
    ∑ x : A, Complex.normSq (∑ i, (a i : ℂ) * χ i x) =
      (Nat.card A : ℝ) * ∑ i, a i ^ 2 := by
  have hc : (Nat.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have ho (i j : I) : (∑ x : A, χ i x * star (χ j x)) =
      if i = j then (Nat.card A : ℂ) else 0 := by
    have hh := orthogonal (χ i) (χ j)
    change (Nat.card A : ℂ)⁻¹ * _ = _ at hh
    rw [hi.eq_iff] at hh
    by_cases he : i = j
    · simp only [he, if_true] at hh ⊢
      have hh := congrArg (fun z => (Nat.card A : ℂ) * z) hh
      simpa [← mul_assoc, hc] using hh
    · simp only [he, if_false] at hh ⊢
      have hh := congrArg (fun z => (Nat.card A : ℂ) * z) hh
      simpa [← mul_assoc, hc] using hh
  have hs : (∑ x : A, (∑ i, (a i : ℂ) * χ i x) *
      star (∑ i, (a i : ℂ) * χ i x)) =
      (Nat.card A : ℂ) * ∑ i, (a i : ℂ) ^ 2 := by
    calc
      _ = ∑ x : A, ∑ i, ∑ j, ((a i : ℂ) * (a j : ℂ)) *
          (χ i x * star (χ j x)) := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [star_sum, star_mul, RCLike.star_def, Complex.conj_ofReal,
          Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i, ∑ j, ∑ x : A, ((a i : ℂ) * (a j : ℂ)) *
          (χ i x * star (χ j x)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        simp_rw [← Finset.mul_sum, ho]
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [← Finset.sum_mul]
        simp only [pow_two]
        ring
  have hh : ((∑ x : A, Complex.normSq (∑ i, (a i : ℂ) * χ i x) : ℝ) : ℂ) =
      ((Nat.card A : ℝ) * ∑ i, a i ^ 2 : ℝ) := by
    push_cast
    simpa only [RCLike.star_def, Complex.mul_conj] using hs
  exact_mod_cast hh
end AbelianLinearCharacters
