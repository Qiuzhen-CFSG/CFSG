/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Changes: Lean 4.33 modules, narrow imports, and CFSG quadratic-isometry carriers.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.RankOneComparison.Action

/-!
# The scalar kernel of trace-zero conjugation

Adapted from ATLAS `LinearGroups/Orthogonal/B1ConjugationKernel.lean`.
Testing a scalar action on the two off-diagonal matrix units and the
trace-zero diagonal matrix forces the scalar to be one and the SL₂ matrix
to be central. Conversely every central SL₂ matrix acts trivially.
This proves the kernel needed for the B₁/A₁ comparison of GLS3 §2.7.
-/
@[expose] public noncomputable section
namespace ClassicalOrthogonal.RankOneComparison
open Matrix
variable {F : Type*} [Field F]

theorem scalar_commutation (g : SL (F := F)) (c : F)
    (h : ∀ v, (toOrthogonal g).val v = c • v)
    (M : TraceZero (F := F)) : g.val * M.val = c • (M.val * g.val) := by
  have ht := onB_coordinates g (coordinates.symm M)
  change (coordinates ((toOrthogonal g).val (coordinates.symm M))).val = _ at ht
  rw [h,map_smul,LinearEquiv.apply_symm_apply] at ht
  have hh := congrArg (fun N : Mat (F := F) => N * g.val) ht.symm
  change (g.val * M.val * g⁻¹.val) * g.val = (c • M.val) * g.val at hh
  rw [mul_assoc, ← SpecialLinearGroup.coe_mul,inv_mul_cancel,SpecialLinearGroup.coe_one,mul_one,
    Matrix.smul_mul] at hh
  exact hh

/-- Scalar conjugation on trace-zero matrices is identity, and its source matrix is central. -/
theorem scalar_action_implies_center (g : SL (F := F)) (c : F)
    (h : ∀ v, (toOrthogonal g).val v = c • v) :
    c = 1 ∧ g ∈ Subgroup.center (SL (F := F)) := by
  have h12 := scalar_commutation g c h
    (⟨!![0,1;0,0],by simp [Matrix.trace,Fin.sum_univ_two]⟩ : TraceZero (F := F))
  have h21 := scalar_commutation g c h
    (⟨!![0,0;1,0],by simp [Matrix.trace,Fin.sum_univ_two]⟩ : TraceZero (F := F))
  have hH := scalar_commutation g c h
    (⟨!![1,0;0,-1],by simp [Matrix.trace,Fin.sum_univ_two]⟩ : TraceZero (F := F))
  have h10 : g.val 1 0 = 0 := by
    have hh := congrArg (fun M : Mat (F := F) => M 1 1) h12
    simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.vecHead,Matrix.vecTail,Fin.sum_univ_two] using hh
  have h01 : g.val 0 1 = 0 := by
    have hh := congrArg (fun M : Mat (F := F) => M 0 0) h21
    simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.vecHead,Matrix.vecTail,Fin.sum_univ_two] using hh
  have ha : g.val 0 0 ≠ 0 := by
    intro hz
    have hd := g.det_coe
    rw [Matrix.det_fin_two] at hd
    simp [hz,h01,h10] at hd
  have hc : c = 1 := by
    have hh := congrArg (fun M : Mat (F := F) => M 0 0) hH
    have he : g.val 0 0 = c * g.val 0 0 := by
      simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.vecHead,Matrix.vecTail,Fin.sum_univ_two] using hh
    exact mul_right_cancel₀ ha (by simpa using he.symm)
  have hd : g.val 0 0 = g.val 1 1 := by
    have hh := congrArg (fun M : Mat (F := F) => M 0 1) h12
    simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.vecHead,Matrix.vecTail,Fin.sum_univ_two,hc] using hh
  refine ⟨hc,?_⟩
  rw [Subgroup.mem_center_iff]
  intro B
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,h01,h10,hd,mul_comm]

theorem toOrthogonal_eq_one_of_center (g : SL (F := F))
    (hg : g ∈ Subgroup.center (SL (F := F))) : toOrthogonal g = 1 := by
  obtain ⟨a,ha,hga⟩ := SpecialLinearGroup.mem_center_iff.mp hg
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply coordinates.injective
  apply Subtype.ext
  change (coordinates (onB g v)).val = (coordinates v).val
  rw [onB_coordinates]
  have hm : g.val * (coordinates v).val = (coordinates v).val * g.val := by
    rw [← hga]
    ext i j
    simp [Matrix.scalar_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,mul_comm]
  rw [hm,mul_assoc,← SpecialLinearGroup.coe_mul,mul_inv_cancel,SpecialLinearGroup.coe_one,mul_one]

theorem toOrthogonal_eq_one_iff_center (g : SL (F := F)) :
    toOrthogonal g = 1 ↔ g ∈ Subgroup.center (SL (F := F)) := by
  constructor
  · intro hg
    exact (scalar_action_implies_center g 1 (by rw [hg]; intro v; exact (one_smul F v).symm)).2
  · exact toOrthogonal_eq_one_of_center g

theorem toOrthogonal_kernel : (toOrthogonal (F := F)).ker = Subgroup.center (SL (F := F)) := by
  ext g
  exact toOrthogonal_eq_one_iff_center g

end ClassicalOrthogonal.RankOneComparison
