/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Fischer/ScalarGeometry.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Fischer.Scalars

/-!
# Hermitian geometry over the Fischer scalars

Weighted Hermitian forms use the linear-first convention on exact
Eisenstein coordinates. Termwise conjugation and positivity of the scalar
norm prove covariance and positive definiteness for positive weights.

Source: Gerald Höhn, ATLAS, `Atlas/Fischer/ScalarGeometry.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for downstream coordinate calculations.
-/

@[expose] public section

namespace Atlas.Fischer
open Atlas.Algebra

/-- Conjugation agrees with squaring on exactly the three normalized phases. -/
theorem cube_root_conjugate {z : Scalar} (hz : z ^ 3 = 1) : star z = z ^ 2 := by
  rcases (cube_eq_one_iff z).mp hz with rfl | rfl | rfl
  · simp
  · exact omega_conjugate
  · rw [star_pow, omega_conjugate]

theorem cube_root_unit_norm {z : Scalar} (hz : z ^ 3 = 1) : star z * z = 1 := by
  rw [cube_root_conjugate hz, ← pow_succ, hz]

theorem mu3_conjugate (z : Mu3) : star (z.val.val : Scalar) = z.val.val ^ 2 :=
  cube_root_conjugate ((mem_rootsOfUnity' _ _).mp z.prop)

theorem scalarToComplex_normSq (z : Scalar) :
    Complex.normSq (scalarToComplex z) = (eisensteinReal (star z * z) : ℝ) := by
  have h := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := scalarToComplex z))
  change Complex.normSq (scalarToComplex z) = (star (scalarToComplex z) * scalarToComplex z).re at h
  simpa only [Complex.ofReal_re, ← scalarToComplex_star, ← map_mul,
    scalarToComplex_real] using h

theorem scalar_norm_positive (z : Scalar) (hz : z ≠ 0) :
    0 < (scalarToComplex (star z * z)).re := by
  rw [scalarToComplex_real]
  exact_mod_cast lt_of_le_of_ne (eisensteinReal_star_mul_self_nonneg z)
    (Ne.symm (mt (eisensteinReal_star_mul_self_eq_zero z).mp hz))

/-- Weighted exact Hermitian coordinates with the manuscript's linear-first convention. -/
def weightedHermitian {ι : Type*} [Fintype ι] (w : ι → ℚ)
    (x y : ι → Scalar) : Scalar :=
  ∑ i, (w i : Scalar) * x i * star (y i)

theorem weightedHermitian_add_left {ι : Type*} [Fintype ι] (w : ι → ℚ)
    (x y z : ι → Scalar) :
    weightedHermitian w (x + y) z = weightedHermitian w x z + weightedHermitian w y z := by
  simp [weightedHermitian, mul_add, add_mul, Finset.sum_add_distrib]

theorem weightedHermitian_smul_left {ι : Type*} [Fintype ι] (w : ι → ℚ)
    (a : Scalar) (x y : ι → Scalar) :
    weightedHermitian w (a • x) y = a * weightedHermitian w x y := by
  simp only [weightedHermitian, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weightedHermitian_star {ι : Type*} [Fintype ι] (w : ι → ℚ)
    (x y : ι → Scalar) : star (weightedHermitian w x y) = weightedHermitian w y x := by
  simp only [weightedHermitian, star_sum, star_mul, star_star, star_ratCast]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weightedHermitian_smul_right {ι : Type*} [Fintype ι] (w : ι → ℚ)
    (a : Scalar) (x y : ι → Scalar) :
    weightedHermitian w x (a • y) = star a * weightedHermitian w x y := by
  rw [← star_star (weightedHermitian w x (a • y)), weightedHermitian_star,
    weightedHermitian_smul_left, star_mul, weightedHermitian_star]
  exact mul_comm _ _

theorem weightedHermitian_real_self {ι : Type*} [Fintype ι] (w : ι → ℚ)
    (x : ι → Scalar) :
    eisensteinReal (weightedHermitian w x x) =
      ∑ i, w i * eisensteinReal (star (x i) * x i) := by
  classical
  simp only [weightedHermitian]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [eisensteinReal]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, eisensteinReal_add, ih]
    congr 1
    simp [eisensteinReal]
    ring

theorem weightedHermitian_positive {ι : Type*} [Fintype ι] (w : ι → ℚ)
    (hw : ∀ i, 0 < w i) (x : ι → Scalar) (hx : x ≠ 0) :
    0 < eisensteinReal (weightedHermitian w x x) := by
  classical
  rw [weightedHermitian_real_self]
  have he : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    simpa using not_exists.mp h i
  obtain ⟨i, hi⟩ := he
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hw j).le (eisensteinReal_star_mul_self_nonneg _)
  · exact ⟨i, Finset.mem_univ i, mul_pos (hw i)
      (lt_of_le_of_ne (eisensteinReal_star_mul_self_nonneg _)
        (Ne.symm (mt (eisensteinReal_star_mul_self_eq_zero _).mp hi)))⟩

end Atlas.Fischer
