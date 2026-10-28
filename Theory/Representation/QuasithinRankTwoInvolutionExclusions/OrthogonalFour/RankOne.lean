module
public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Theory.LinearAlgebra.QuadraticRankOneDisplacement
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Rank-one determinant isometries

A nonidentity rank-one isometry has displacement `M ↦ f(M) v`.
Preservation of the determinant forces `f` to be its polar pairing with the
nonsingular direction `v`, divided by `det(v)`. Over F₄, scaling that direction
by its determinant gives a determinant-one matrix A and the formula
`M ↦ A adj(M) A`. The consumer identifies this with a conjugate of the factor
swap on the actual binary orthogonal module.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.11.2(7), printed p.364 (PDF p.375), and the exclusion in the proof of
6.2.19, printed p.691 (PDF p.708).
-/

@[expose] public noncomputable section
namespace Representation.RankTwo.OrthogonalFour
open ClassicalOrthogonal.FourPlusMatrix
open ClassicalOrthogonal.FourPlusMatrix.Binary
open Matrix Module

section General
variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
private lemma polar_det (M N : Mat (F := K)) :
    determinantForm.polarBilin M N =
      M 0 0 * N 1 1 + N 0 0 * M 1 1 - M 0 1 * N 1 0 - N 0 1 * M 1 0 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    determinantForm_apply, Matrix.det_fin_two, Matrix.add_apply]
  ring

omit [CharP K 2] in
private lemma polar_separating : (determinantForm (F := K)).polarBilin.SeparatingLeft := by
  intro M hM
  have h00 := hM !![0, 0; 0, 1]
  have h01 := hM !![0, 0; 1, 0]
  have h10 := hM !![0, 1; 0, 0]
  have h11 := hM !![1, 0; 0, 0]
  rw [polar_det] at h00 h01 h10 h11
  simp at h00 h01 h10 h11
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

omit [CharP K 2] in
private lemma product_functionals (f l : Mat (F := K) →ₗ[K] K) (hf : f ≠ 0)
    (h : ∀ x, f x * l x = 0) : l = 0 := by
  obtain ⟨z, hz⟩ : ∃ z, f z ≠ 0 := by
    by_contra! hn
    exact hf (LinearMap.ext hn)
  have hlz : l z = 0 := (mul_eq_zero.mp (h z)).resolve_left hz
  apply LinearMap.ext
  intro x
  by_cases hx : f x = 0
  · have hxz : f (z + x) ≠ 0 := by simpa [hx] using hz
    have := (mul_eq_zero.mp (h (z + x))).resolve_left hxz
    simpa [hlz] using this
  · exact (mul_eq_zero.mp (h x)).resolve_left hx

/-- Every nonidentity rank-one determinant isometry is the symmetry in a
nonsingular matrix line. -/
theorem rank_one_symmetry (t : Mat (F := K) ≃ₗ[K] Mat (F := K)) (hne : t ≠ 1)
    (hr : finrank K (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 1)
    (ht : ∀ M, (t M).det = M.det) :
    ∃ v : Mat (F := K), v.det ≠ 0 ∧ ∀ M,
      t M = M + (determinantForm.polarBilin M v / v.det) • v := by
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr hr
  have he' (M : Mat (F := K)) : t M = M + f M • v :=
    congrArg (fun l : Mat (F := K) →ₗ[K] Mat (F := K) => l M) he
  have hf : f ≠ 0 := by
    intro h
    apply hne
    apply LinearEquiv.ext
    intro M
    simp [he', h]
  have hv : v ≠ 0 := by
    intro h
    apply hne
    apply LinearEquiv.ext
    intro M
    simp [he', h]
  let q : QuadraticForm K (Mat (F := K)) := determinantForm
  let l : Mat (F := K) →ₗ[K] K := (q v) • f + q.polarBilin.flip v
  have hl : l = 0 := by
    apply product_functionals f l hf
    intro M
    have h : q (t M) = q M := by
      simpa only [q, determinantForm_apply] using ht M
    rw [he', QuadraticMap.map_add q, q.map_smul,
      QuadraticMap.polar_smul_right, smul_eq_mul, smul_eq_mul] at h
    change f M * (q v * f M + q.polarBilin M v) = 0
    change q M + (f M * f M) * q v + f M * q.polarBilin M v = q M at h
    linear_combination h
  have hl' (M : Mat (F := K)) : q v * f M + q.polarBilin M v = 0 :=
    LinearMap.congr_fun hl M
  have hqv : q v ≠ 0 := by
    intro hzero
    apply hv
    apply polar_separating
    intro M
    change q.polarBilin v M = 0
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
      ← QuadraticMap.polarBilin_apply_apply]
    simpa only [hzero, zero_mul, zero_add] using hl' M
  have hdv : v.det ≠ 0 := by simpa only [q, determinantForm_apply] using hqv
  refine ⟨v, hdv, fun M => ?_⟩
  rw [he']
  congr 1
  congr 1
  apply (eq_div_iff hdv).mpr
  have h := hl' M
  simp only [q, determinantForm_apply, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
  exact (mul_comm _ _).trans h


omit [CharP K 2] in
private lemma sandwich (A M : Mat (F := K)) :
    A * M.adjugate * A = determinantForm.polarBilin M A • A - A.det • M := by
  rw [polar_det]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two,
      Matrix.det_fin_two] <;> ring

private theorem rank_one_sandwich_of_cube
    (cube : ∀ c : K, c ≠ 0 → c ^ 3 = 1)
    (t : Mat (F := K) ≃ₗ[K] Mat (F := K)) (hne : t ≠ 1)
    (hr : finrank K (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 1)
    (ht : ∀ M, (t M).det = M.det) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) K, ∀ M,
      t M = A.val * M.adjugate * A.val := by
  obtain ⟨v, hv, he⟩ := rank_one_symmetry t hne hr ht
  let A : Matrix.SpecialLinearGroup (Fin 2) K := ⟨v.det • v, by
    rw [Matrix.det_smul]
    simpa [pow_succ] using cube v.det hv⟩
  refine ⟨A, fun M => ?_⟩
  have hneg : -(M : Mat (F := K)) = M := by
    apply Matrix.ext
    intro i j
    exact CharTwo.neg_eq (M i j)
  rw [sandwich, A.property, one_smul, sub_eq_add_neg, hneg, add_comm, he]
  congr 1
  change (determinantForm.polarBilin M v / v.det) • v =
    determinantForm.polarBilin M (v.det • v) • (v.det • v)
  rw [map_smul, smul_eq_mul, smul_smul]
  congr 1
  apply (div_eq_iff hv).mpr
  have hc := cube v.det hv
  calc
    _ = determinantForm.polarBilin M v * 1 := (mul_one _).symm
    _ = _ := by rw [← hc]; ring

end General

/-- In F₄ every nonsingular moved line has a determinant-one generator. -/
theorem rank_one_sandwich (t : V ≃ₗ[F] V) (hne : t ≠ 1)
    (hr : finrank F (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 1)
    (ht : ∀ M, (t M).det = M.det) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F, ∀ M,
      t M = A.val * M.adjugate * A.val :=
  rank_one_sandwich_of_cube (by decide +kernel) t hne hr ht

end Representation.RankTwo.OrthogonalFour
