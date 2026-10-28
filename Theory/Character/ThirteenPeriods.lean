module

public import Theory.Character.FiniteOrderTrace
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Periods of three thirteenth roots

A rational sum of three nontrivial thirteenth roots would be an integer
congruent to three modulo thirteen. Its absolute value is at most three,
so it equals three. The equality case of the finite-order trace bound then
forces every root to be one, a contradiction. A partition of the twelve
nontrivial roots into four triples has total period sum minus one.

These elementary facts supply the irrationality and degree-equation steps
for cyclic blocks with inertial index three. Source application:
Alperin--Brauer--Gorenstein, III.8 Proposition 5, printed pp.116--117.
-/

public section

noncomputable section
namespace ThirteenPeriods
open scoped BigOperators

theorem sum_three_not_rational {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 13)
    (a : Fin 3 → ℕ) (ha : ∀ i, 0 < a i ∧ a i < 13) :
    ¬ ∃ q : ℚ, (∑ i, ζ ^ a i) = (q : ℂ) := by
  rintro ⟨q, hq⟩
  have hint : IsIntegral ℤ (∑ i, ζ ^ a i) :=
    IsIntegral.sum _ (fun i _ => (hζ.isIntegral (by decide)).pow _)
  rw [hq] at hint
  have hqint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ ℂ)).mp hint
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqint
  have hzval : (∑ i, ζ ^ a i) = (z : ℂ) := by rw [hq, ← hz]; simp
  let M : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i => ζ ^ a i)
  let f : Module.End ℂ (Fin 3 → ℂ) := Matrix.toLinAlgEquiv' M
  have hMp : M ^ 13 = 1 := by
    change (Matrix.diagonal (fun i => ζ ^ a i)) ^ 13 = 1
    rw [Matrix.diagonal_pow]
    have hfun : (fun i => ζ ^ a i) ^ 13 = fun _ => (1 : ℂ) := by
      funext i
      change (ζ ^ a i) ^ 13 = 1
      rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [hfun, Matrix.diagonal_one]
  have hfp : f ^ 13 = 1 := by
    change (Matrix.toLinAlgEquiv' M) ^ 13 = 1
    rw [← map_pow, hMp, map_one]
  have htrace : LinearMap.trace ℂ (Fin 3 → ℂ) f = (z : ℂ) := by
    change LinearMap.trace ℂ _ (Matrix.toLin' M) = _
    simpa [M] using hzval
  have hmod : (13 : ℤ) ∣ z - 3 := by
    simpa using prime_dvd_integer_trace_sub_finrank f (by decide : Nat.Prime 13) hfp z htrace
  have habs : |(z : ℝ)| ≤ 3 := by
    have hb := finite_order_end_norm_trace_le_finrank f (by decide : 13 ≠ 0) hfp
    simpa [htrace] using hb
  have hlo : (-3 : ℤ) ≤ z := by exact_mod_cast (abs_le.mp habs).1
  have hhi : z ≤ (3 : ℤ) := by exact_mod_cast (abs_le.mp habs).2
  have hz3 : z = 3 := by omega
  have hf : f = 1 := finite_order_end_eq_one_of_trace_eq_finrank f
    (by decide : 13 ≠ 0) hfp (by simpa [hz3] using htrace)
  have hM : M = 1 := Matrix.toLinAlgEquiv'.injective (by simpa [f] using hf)
  have hroot : ζ ^ a 0 = 1 := by
    simpa [M] using congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 0 0) hM
  have hdvd := (hζ.pow_eq_one_iff_dvd _).mp hroot
  have hle := Nat.le_of_dvd (ha 0).1 hdvd
  exact (not_le_of_gt (ha 0).2) hle

/-- A triple in a partition of the nontrivial thirteenth roots. -/
@[expose] def period (ζ : ℂ) (a : Fin 4 × Fin 3 ≃ Fin 12) (i : Fin 4) : ℂ :=
  ∑ j : Fin 3, ζ ^ ((a (i, j)).val + 1)

theorem sum_periods {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 13) (a : Fin 4 × Fin 3 ≃ Fin 12) :
    ∑ i : Fin 4, period ζ a i = -1 := by
  have hgeom := hζ.geom_sum_eq_zero (by decide : 1 < 13)
  rw [show 13 = 12 + 1 from rfl, Finset.sum_range_succ'] at hgeom
  simp only [pow_zero] at hgeom
  have hs : ∑ i : Fin 4, period ζ a i = ∑ j ∈ Finset.range 12, ζ ^ (j + 1) := by
    unfold period
    rw [← Fintype.sum_prod_type (fun ij : Fin 4 × Fin 3 => ζ ^ ((a ij).val + 1)),
      a.sum_comp (fun j : Fin 12 => ζ ^ (j.val + 1))]
    exact Fin.sum_univ_eq_sum_range (fun j => ζ ^ (j + 1)) 12
  rw [hs]
  exact eq_neg_of_add_eq_zero_left hgeom

/-- No period in such a partition is rational. -/
theorem period_not_rational {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 13)
    (a : Fin 4 × Fin 3 ≃ Fin 12) (i : Fin 4) :
    ¬ ∃ q : ℚ, period ζ a i = (q : ℂ) := by
  apply sum_three_not_rational hζ
  intro j
  have := (a (i, j)).isLt
  omega

/-- Changing a period by a sign preserves its irrationality. -/
theorem signed_period_not_rational {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 13)
    (a : Fin 4 × Fin 3 ≃ Fin 12) (i : Fin 4)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ¬ ∃ q : ℚ, -(ε : ℂ) * period ζ a i = (q : ℂ) := by
  rintro ⟨q, hq⟩
  apply period_not_rational hζ a i
  rcases hε with rfl | rfl
  · refine ⟨-q, ?_⟩
    simpa using congrArg Neg.neg hq
  · exact ⟨q, by simpa using hq⟩

end ThirteenPeriods
