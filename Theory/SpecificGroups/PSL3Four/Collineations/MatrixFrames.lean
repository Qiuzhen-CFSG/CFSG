module

public import Theory.Combinatorics.ProjectivePlaneMatrixAction
public import Theory.SpecificGroups.PSL3Four.FieldExtension.SemilinearInclusion
public import Theory.SpecificGroups.PSL3Four.FieldExtension.PairedAction

/-!
# Matrix normalization of frames in PG(2,4)

The first three images of a projective frame have linearly independent
representatives: pairing against the three opposite line covectors gives
an invertible diagonal matrix. Rescaling its columns realizes the fourth
image as well. Passing to PGL retains the point action and avoids counting
scalar matrices more than once.

This is the elementary frame argument used for the plane-action comparison
in Aschbacher–Smith F.4.8(2), printed p.278. The pairing proof adapts the
existing `ProjectivePlaneThreeFrameRealization` argument to the four-element
field; no classification of collineations is assumed.
-/

open Matrix Projectivization
namespace Matrix.GeneralLinearGroup
variable {K : Type*} [Field K]
private def contra (A : GeneralLinearGroup (Fin 3) K) : GeneralLinearGroup (Fin 3) K where
  val := (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K).transpose
  inv := (↑A : Matrix (Fin 3) (Fin 3) K).transpose
  val_inv := by rw [← Matrix.transpose_mul]; simp
  inv_val := by rw [← Matrix.transpose_mul]; simp
end Matrix.GeneralLinearGroup
namespace Configuration
variable {K : Type*} [Field K]
private noncomputable def generalLinearCollineation
    (A : Matrix.GeneralLinearGroup (Fin 3) K) :
    Collineation (Projectivization K (Fin 3 → K)) (Projectivization K (Fin 3 → K)) :=
  ⟨(MulAction.toPerm A, MulAction.toPerm (Matrix.GeneralLinearGroup.contra A)), by
    intro p l
    induction p using Projectivization.ind with | h v hv =>
    induction l using Projectivization.ind with | h w hw =>
    simp only [MulAction.toPerm_apply, smul_mk, ofField.mem_iff, orthogonal_mk]
    change (A.val *ᵥ v) ⬝ᵥ (A⁻¹.val.transpose *ᵥ w) = 0 ↔ v ⬝ᵥ w = 0
    rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, dotProduct_comm]⟩
end Configuration
namespace Configuration.PlaneFour
open Matrix.PSL3Four
open scoped Matrix
noncomputable section
local instance : DecidableEq F := Classical.decEq _
public abbrev FullCollineation := Collineation PG PG
@[expose] public def frameVector : Fin 4 → Fin 3 → F :=
  ![![1,0,0], ![0,1,0], ![0,0,1], ![1,1,1]]
public theorem frameVector_ne_zero (i : Fin 4) : frameVector i ≠ 0 := by
  fin_cases i <;> simp [frameVector, funext_iff, Fin.forall_fin_succ]
@[expose] public def frame (i : Fin 4) : PG :=
  Projectivization.mk F (frameVector i) (frameVector_ne_zero i)
open Matrix Projectivization
open scoped Matrix

private theorem frame_coord_mem (i j : Fin 3) :
    frame i.castSucc ∈ frame j.castSucc ↔ i ≠ j := by
  fin_cases i <;> fin_cases j <;>
    simp [frame, ofField.mem_iff, orthogonal_mk, frameVector, dotProduct, Fin.sum_univ_succ]

private theorem frame_last_not_mem (j : Fin 3) : ¬ frame 3 ∈ frame j.castSucc := by
  fin_cases j <;>
    simp [frame, ofField.mem_iff, orthogonal_mk, frameVector, dotProduct, Fin.sum_univ_succ]

private theorem dot_rep_eq_zero_iff (p l : PG) : p.rep ⬝ᵥ l.rep = 0 ↔ p ∈ l := by
  simpa only [mk_rep] using
    ((ofField.mem_iff (mk F p.rep p.rep_nonzero)
      (mk F l.rep l.rep_nonzero)).trans
        (orthogonal_mk p.rep_nonzero l.rep_nonzero)).symm

private noncomputable def imageVector (c : FullCollineation) (i : Fin 4) :
    Fin 3 → F := (Collineation.pointHom PG PG c (frame i)).rep

private noncomputable def imageCovector (c : FullCollineation) :
    Matrix (Fin 3) (Fin 3) F :=
  fun i => (Collineation.lineHom PG PG c (frame i.castSucc)).rep

private noncomputable def imageMatrix (c : FullCollineation) :
    Matrix (Fin 3) (Fin 3) F := fun i j => imageVector c j.castSucc i

private theorem image_pairing (c : FullCollineation) (i : Fin 4) (j : Fin 3) :
    imageCovector c j ⬝ᵥ imageVector c i = 0 ↔ frame i ∈ frame j.castSucc := by
  rw [dotProduct_comm]
  exact (dot_rep_eq_zero_iff _ _).trans (Collineation.mem_iff c _ _)

private theorem image_diagonal (c : FullCollineation) :
    imageCovector c * imageMatrix c =
      diagonal (fun i => imageCovector c i ⬝ᵥ imageVector c i.castSucc) := by
  ext i j
  change imageCovector c i ⬝ᵥ imageVector c j.castSucc = _
  by_cases h : i = j
  · subst j
    simp
  · rw [diagonal_apply_ne _ h]
    exact (image_pairing c _ _).mpr ((frame_coord_mem j i).mpr (Ne.symm h))

private theorem imageMatrix_det_ne_zero (c : FullCollineation) :
    (imageMatrix c).det ≠ 0 := by
  have hd : ∀ i : Fin 3, imageCovector c i ⬝ᵥ imageVector c i.castSucc ≠ 0 := by
    intro i hi
    exact (frame_coord_mem i i).mp ((image_pairing c _ _).mp hi) rfl
  have hprod : (imageCovector c * imageMatrix c).det ≠ 0 := by
    rw [image_diagonal, det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
  rw [det_mul] at hprod
  exact (mul_ne_zero_iff.mp hprod).2

private theorem imageMatrix_isUnit (c : FullCollineation) : IsUnit (imageMatrix c) :=
  (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (imageMatrix_det_ne_zero c))

private theorem exists_image_coordinates (c : FullCollineation) :
    ∃ x : Fin 3 → F, (∀ i, x i ≠ 0) ∧ imageMatrix c *ᵥ x = imageVector c 3 := by
  obtain ⟨x, hx⟩ := mulVec_surjective_iff_isUnit.mpr (imageMatrix_isUnit c) (imageVector c 3)
  refine ⟨x, ?_, hx⟩
  intro i hi
  apply frame_last_not_mem i
  apply (image_pairing c 3 i).mp
  change (imageCovector c *ᵥ imageVector c 3) i = 0
  rw [← hx, mulVec_mulVec, image_diagonal, mulVec_diagonal, hi, mul_zero]

private theorem frameVector_coord (i : Fin 3) :
    frameVector i.castSucc = Pi.single i 1 := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [frameVector]


private theorem exists_generalLinear_frame (c : FullCollineation) :
    ∃ A : Matrix.GeneralLinearGroup (Fin 3) F, ∀ i : Fin 4,
      Collineation.pointHom PG PG c (frame i) = A • frame i := by
  obtain ⟨x, hx, hMx⟩ := exists_image_coordinates c
  let B := imageMatrix c * diagonal x
  have hB : B.det ≠ 0 := by
    dsimp [B]
    rw [det_mul, det_diagonal]
    exact mul_ne_zero (imageMatrix_det_ne_zero c)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hx i))
  let A : Matrix.GeneralLinearGroup (Fin 3) F :=
    (isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hB) |>.unit
  have hAB : A.val = B := IsUnit.unit_spec _
  have hcoord (i : Fin 3) :
      A.val *ᵥ frameVector i.castSucc = x i • imageVector c i.castSucc := by
    rw [hAB, frameVector_coord, mulVec_single_one]
    ext j
    simp [B, mul_diagonal, imageMatrix, mul_comm]
  have hlast : A.val *ᵥ frameVector 3 = imageVector c 3 := by
    rw [hAB]
    change (imageMatrix c * diagonal x) *ᵥ frameVector 3 = _
    rw [← mulVec_mulVec]
    have hone : diagonal x *ᵥ frameVector 3 = x := by
      ext i
      fin_cases i <;> simp [mulVec_diagonal, frameVector]
    rw [hone, hMx]
  refine ⟨A, ?_⟩
  intro i
  suffices ∃ a : F, A.val *ᵥ frameVector i = a • imageVector c i by
    obtain ⟨a, heq⟩ := this
    symm
    change mk F (A.val *ᵥ frameVector i) _ = _
    rw [← mk_rep (Collineation.pointHom PG PG c (frame i))]
    exact (mk_eq_mk_iff' F _ _ _ _).mpr ⟨a, heq.symm⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact ⟨1, by simpa using hlast⟩
  · exact ⟨x j, hcoord j⟩

public def pglCollineation (g : PGL) : FullCollineation :=
  generalLinearCollineation (ProjGenLinGroup.mk_surjective g).choose

public theorem pglCollineation_point (g : PGL) (p : PG) :
    Collineation.pointHom PG PG (pglCollineation g) p = g • p := by
  let A := (ProjGenLinGroup.mk_surjective g).choose
  have hA : ProjGenLinGroup.mk A = g := (ProjGenLinGroup.mk_surjective g).choose_spec
  change A • p = g • p
  rw [← hA]
  induction p using Projectivization.ind with | h v hv => rfl

public theorem exists_projectiveLinear_frame (c : FullCollineation) :
    ∃ A : PGL, ∀ i : Fin 4,
      Collineation.pointHom PG PG (pglCollineation A) (frame i) =
        Collineation.pointHom PG PG c (frame i) := by
  obtain ⟨A,hA⟩ := exists_generalLinear_frame c
  refine ⟨ProjGenLinGroup.mk A, fun i => ?_⟩
  rw [pglCollineation_point, hA]
  rfl
end
end Configuration.PlaneFour
