module

public import Theory.Character.FiniteOrderTrace
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Periods of two seventh roots

A rational sum of two nontrivial seventh roots would be an integer
congruent to two modulo seven. Its absolute value is at most two,
so it equals two. The equality case of the finite-order trace bound then
forces every root to be one, a contradiction. A partition of the six
nontrivial roots into three pairs has total period sum minus one.

These elementary facts supply the irrationality and degree-equation steps
for cyclic blocks with inertial index two. Source application: Fong (1967), printed p.75, citing Brauer (1942).
Adapted from `Theory.Character.ThirteenPeriods`.
-/

public section

noncomputable section
namespace SevenPeriods
open scoped BigOperators

theorem sum_two_not_rational {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 7)
    (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i ∧ a i < 7) :
    ¬ ∃ q : ℚ, (∑ i, ζ ^ a i) = (q : ℂ) := by
  rintro ⟨q, hq⟩
  have hint : IsIntegral ℤ (∑ i, ζ ^ a i) :=
    IsIntegral.sum _ (fun i _ => (hζ.isIntegral (by decide)).pow _)
  rw [hq] at hint
  have hqint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ ℂ)).mp hint
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqint
  have hzval : (∑ i, ζ ^ a i) = (z : ℂ) := by rw [hq, ← hz]; simp
  let M : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun i => ζ ^ a i)
  let f : Module.End ℂ (Fin 2 → ℂ) := Matrix.toLinAlgEquiv' M
  have hMp : M ^ 7 = 1 := by
    change (Matrix.diagonal (fun i => ζ ^ a i)) ^ 7 = 1
    rw [Matrix.diagonal_pow]
    have hfun : (fun i => ζ ^ a i) ^ 7 = fun _ => (1 : ℂ) := by
      funext i
      change (ζ ^ a i) ^ 7 = 1
      rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [hfun, Matrix.diagonal_one]
  have hfp : f ^ 7 = 1 := by
    change (Matrix.toLinAlgEquiv' M) ^ 7 = 1
    rw [← map_pow, hMp, map_one]
  have htrace : LinearMap.trace ℂ (Fin 2 → ℂ) f = (z : ℂ) := by
    change LinearMap.trace ℂ _ (Matrix.toLin' M) = _
    simpa [M] using hzval
  have hmod : (7 : ℤ) ∣ z - 2 := by
    simpa using prime_dvd_integer_trace_sub_finrank f (by decide : Nat.Prime 7) hfp z htrace
  have habs : |(z : ℝ)| ≤ 2 := by
    have hb := finite_order_end_norm_trace_le_finrank f (by decide : 7 ≠ 0) hfp
    simpa [htrace] using hb
  have hlo : (-2 : ℤ) ≤ z := by exact_mod_cast (abs_le.mp habs).1
  have hhi : z ≤ (2 : ℤ) := by exact_mod_cast (abs_le.mp habs).2
  have hz3 : z = 2 := by omega
  have hf : f = 1 := finite_order_end_eq_one_of_trace_eq_finrank f
    (by decide : 7 ≠ 0) hfp (by simpa [hz3] using htrace)
  have hM : M = 1 := Matrix.toLinAlgEquiv'.injective (by simpa [f] using hf)
  have hroot : ζ ^ a 0 = 1 := by
    simpa [M] using congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) hM
  have hdvd := (hζ.pow_eq_one_iff_dvd _).mp hroot
  have hle := Nat.le_of_dvd (ha 0).1 hdvd
  exact (not_le_of_gt (ha 0).2) hle

/-- A pair in a partition of the nontrivial seventh roots. -/
@[expose] def period (ζ : ℂ) (a : Fin 3 × Fin 2 ≃ Fin 6) (i : Fin 3) : ℂ :=
  ∑ j : Fin 2, ζ ^ ((a (i, j)).val + 1)

theorem sum_periods {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 7) (a : Fin 3 × Fin 2 ≃ Fin 6) :
    ∑ i : Fin 3, period ζ a i = -1 := by
  have hgeom := hζ.geom_sum_eq_zero (by decide : 1 < 7)
  rw [show 7 = 6 + 1 from rfl, Finset.sum_range_succ'] at hgeom
  simp only [pow_zero] at hgeom
  have hs : ∑ i : Fin 3, period ζ a i = ∑ j ∈ Finset.range 6, ζ ^ (j + 1) := by
    unfold period
    rw [← Fintype.sum_prod_type (fun ij : Fin 3 × Fin 2 => ζ ^ ((a ij).val + 1)),
      a.sum_comp (fun j : Fin 6 => ζ ^ (j.val + 1))]
    exact Fin.sum_univ_eq_sum_range (fun j => ζ ^ (j + 1)) 6
  rw [hs]
  exact eq_neg_of_add_eq_zero_left hgeom

/-- No period in such a partition is rational. -/
theorem period_not_rational {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 7)
    (a : Fin 3 × Fin 2 ≃ Fin 6) (i : Fin 3) :
    ¬ ∃ q : ℚ, period ζ a i = (q : ℂ) := by
  apply sum_two_not_rational hζ
  intro j
  have := (a (i, j)).isLt
  omega

/-- Changing a period by a sign preserves its irrationality. -/
theorem signed_period_not_rational {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 7)
    (a : Fin 3 × Fin 2 ≃ Fin 6) (i : Fin 3)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ¬ ∃ q : ℚ, -(ε : ℂ) * period ζ a i = (q : ℂ) := by
  rintro ⟨q, hq⟩
  apply period_not_rational hζ a i
  rcases hε with rfl | rfl
  · refine ⟨-q, ?_⟩
    simpa using congrArg Neg.neg hq
  · exact ⟨q, by simpa using hq⟩

end SevenPeriods
