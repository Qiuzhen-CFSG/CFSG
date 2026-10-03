module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveOddElements
public import Theory.Character.AbelianLinearNorm
public import Theory.Character.ModularBlock.SmallQuotientBrauerNorm

/-!
# Local odd-section norms from complement-fiber cardinalities

The identity complement fiber contains only the identity odd element. When
the other four fibers have sixteen odd elements, summation by fibers weights
the complement Fourier sum by sixteen and subtracts fifteen identity values.
Character orthogonality and the five-variable pair-difference identity then
give the involution contribution numerator in Lyons's equation (3.3).

This module isolates the counting hypothesis so the group-theoretic fiber
calculation and the character calculation have separate interfaces.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 373–374.
-/

public section

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Stellmacher.Recognition.LyonsU3Four
variable {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (α : FiveComplement →* MulAut S)
omit [Finite G] in
/-- There is exactly one odd-order element over the identity of the complement. -/
theorem localFive_odd_identity_fiber_card :
    Nat.card {u : LocalFiveGroup S α // Odd (orderOf u) ∧ u.right = 1} = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨1, by simp⟩, ?_⟩
  intro u
  exact Subtype.ext ((localFive_odd_right_eq_one_iff S α u.1 u.2.1).mp u.2.2)

/-- Sum a complement function using the odd-element cardinality of each fiber. -/
theorem localFive_odd_sum_of_fiber_card (hcount : ∀ a : FiveComplement,
    Nat.card {u : LocalFiveGroup S α // Odd (orderOf u) ∧ u.right = a} =
      if a = 1 then 1 else 16) (f : FiveComplement → ℝ) :
    (∑ u : LocalFiveGroup S α, if Odd (orderOf u) then f u.right else 0) =
      16 * ∑ a, f a - 15 * f 1 := by
  have hc (a : FiveComplement) :
      (((Finset.univ : Finset (LocalFiveGroup S α)).filter
        (fun u => Odd (orderOf u))).filter (fun u => u.right = a)).card =
          if a = 1 then 1 else 16 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.filter_filter] using hcount a
  rw [← Finset.sum_filter]
  rw [← Finset.sum_fiberwise'
    (Finset.univ.filter (fun u : LocalFiveGroup S α => Odd (orderOf u)))
    (fun u : LocalFiveGroup S α => u.right) f]
  simp only [Finset.sum_const, nsmul_eq_mul, hc]
  have he (a : FiveComplement) :
      ((if a = 1 then 1 else 16 : ℕ) : ℝ) * f a =
        16 * f a - if a = 1 then 15 * f a else 0 := by
    split_ifs <;> norm_num
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

/-- The Fourier numerator equals the sum-of-squares numerator in (3.3). -/
theorem five_pair_difference_identity (a : Fin 5 → ℤ) :
    16 * (∑ i, a i ^ 2) - 3 * (∑ i, a i) ^ 2 =
      (∑ i, a i ^ 2) + 3 * ∑ i, ∑ k ∈ Finset.Iio i, (a k - a i)^2 := by
  simp only [← Finset.filter_gt_eq_Iio, Finset.sum_filter]
  simp [Fin.sum_univ_succ]
  ring

/-- The actual local odd-element norm, conditional only on the fiber counts. -/
theorem localFive_normalizedOddNorm_of_fiber_card (h : SylowStructure S)
    (hcount : ∀ x : FiveComplement,
      Nat.card {u : LocalFiveGroup S α // Odd (orderOf u) ∧ u.right = x} =
        if x = 1 then 1 else 16)
    (e : Fin 5 ≃ FiveLinearIndex) (a : Fin 5 → ℤ) :
    ModularBlock.Cartan.normalizedOddNorm (fun u : LocalFiveGroup S α =>
      ∑ i, (a i : ℂ) * e i u.right) =
        (((∑ i, a i ^ 2) + 3 * ∑ i, ∑ k ∈ Finset.Iio i, (a k - a i)^2 : ℤ) : ℝ) / 64 := by
  have hp := AbelianLinearCharacters.sum_normSq_real_combination
    (fun i => e i) e.injective (fun i => (a i : ℝ))
  have hcard : Nat.card FiveComplement = 5 := by
    simp [FiveComplement, Nat.card_eq_fintype_card]
  simp only [Complex.ofReal_intCast, hcard, Nat.cast_ofNat] at hp
  have hp' : (∑ x : FiveComplement, Complex.normSq (∑ i, (a i : ℂ) * e i x)) =
      5 * ∑ i, (a i : ℝ)^2 := by
    convert hp using 1
    congr 2
    exact Subsingleton.elim _ _
  rw [← five_pair_difference_identity a]
  rw [ModularBlock.Cartan.normalizedOddNorm_eq, localFiveGroup_card S h α,
    localFive_odd_sum_of_fiber_card S α hcount (fun x =>
      Complex.normSq (∑ i, (a i : ℂ) * e i x))]
  rw [hp']
  simp only [map_one, mul_one]
  simp [Complex.normSq_apply]
  ring
end Stellmacher.Recognition.LyonsU3Four
