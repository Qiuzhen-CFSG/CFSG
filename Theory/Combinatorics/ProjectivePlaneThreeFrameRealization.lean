module

public import Theory.Combinatorics.ProjectivePlaneThreeAction

/-!
# Realizing the image of a projective frame over the three-element field

Every incidence collineation of PG(2,3) agrees on the standard ordered frame
with a determinant-one matrix. The images of the three coordinate lines pair
diagonally, with nonzero diagonal, against representatives of the first three
image points. Thus these representatives are a basis. Pairing with the same
lines shows that the fourth image has three nonzero coordinates in this basis.
Rescale the columns by these coordinates, then multiply the whole matrix by its
determinant: over F₃ this makes the determinant one without changing any
projective image.

This is the frame-normalization step in the elementary coordinate proof of
the collineation theorem for PG(2,3), toward Wong, Theorem 6(b), printed p. 111.
-/

namespace Configuration.PlaneThree

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
    ((ofField.mem_iff (mk (ZMod 3) p.rep p.rep_nonzero)
      (mk (ZMod 3) l.rep l.rep_nonzero)).trans
        (orthogonal_mk p.rep_nonzero l.rep_nonzero)).symm

private noncomputable def imageVector (c : FullCollineation) (i : Fin 4) :
    Fin 3 → ZMod 3 := (Collineation.pointHom PG PG c (frame i)).rep

private noncomputable def imageCovector (c : FullCollineation) :
    Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  fun i => (Collineation.lineHom PG PG c (frame i.castSucc)).rep

private noncomputable def imageMatrix (c : FullCollineation) :
    Matrix (Fin 3) (Fin 3) (ZMod 3) := fun i j => imageVector c j.castSucc i

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

/-- The first three image representatives form a linearly independent family. -/
public theorem linearIndependent_frame_images (c : FullCollineation) :
    LinearIndependent (ZMod 3)
      (fun i : Fin 3 => (Collineation.pointHom PG PG c (frame i.castSucc)).rep) :=
  linearIndependent_cols_iff_isUnit.mpr (imageMatrix_isUnit c)

private theorem exists_image_coordinates (c : FullCollineation) :
    ∃ x : Fin 3 → ZMod 3, (∀ i, x i ≠ 0) ∧ imageMatrix c *ᵥ x = imageVector c 3 := by
  obtain ⟨x, hx⟩ := mulVec_surjective_iff_isUnit.mpr (imageMatrix_isUnit c) (imageVector c 3)
  refine ⟨x, ?_, hx⟩
  intro i hi
  apply frame_last_not_mem i
  apply (image_pairing c 3 i).mp
  change (imageCovector c *ᵥ imageVector c 3) i = 0
  rw [← hx, mulVec_mulVec, image_diagonal, mulVec_diagonal, hi, mul_zero]

private theorem frameVector_coord (i : Fin 3) :
    frameVector i.castSucc = Pi.single i 1 := by
  fin_cases i <;> ext j <;> fin_cases j <;> decide

/-- Every full collineation agrees with an actual determinant-one matrix on the frame. -/
public theorem exists_specialLinear_frame (c : FullCollineation) :
    ∃ A : Matrix.PSL3Three.SL, ∀ i : Fin 4,
      Configuration.Collineation.pointHom PG PG c (frame i) = A • frame i := by
  obtain ⟨x, hx, hMx⟩ := exists_image_coordinates c
  let B := imageMatrix c * diagonal x
  have hB : B.det ≠ 0 := by
    dsimp [B]
    rw [det_mul, det_diagonal]
    exact mul_ne_zero (imageMatrix_det_ne_zero c)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hx i))
  have hdet : (B.det • B).det = 1 := by
    rw [det_smul]
    have hfield : ∀ d : ZMod 3, d ≠ 0 → d ^ 3 * d = 1 := by decide
    exact hfield B.det hB
  let A : Matrix.PSL3Three.SL := ⟨B.det • B, hdet⟩
  have hcoord (i : Fin 3) :
      A.val *ᵥ frameVector i.castSucc = (B.det * x i) • imageVector c i.castSucc := by
    change (B.det • B) *ᵥ frameVector i.castSucc = _
    rw [smul_mulVec, frameVector_coord, mulVec_single_one]
    ext j
    simp [B, mul_diagonal, imageMatrix, mul_comm, mul_left_comm, mul_assoc]
  have hlast : A.val *ᵥ frameVector 3 = B.det • imageVector c 3 := by
    change (B.det • B) *ᵥ frameVector 3 = _
    rw [smul_mulVec]
    congr 1
    change (imageMatrix c * diagonal x) *ᵥ frameVector 3 = _
    rw [← mulVec_mulVec]
    have hone : diagonal x *ᵥ frameVector 3 = x := by
      ext i
      fin_cases i <;> simp [mulVec_diagonal, frameVector]
    rw [hone, hMx]
  refine ⟨A, ?_⟩
  intro i
  suffices ∃ a : ZMod 3, a ≠ 0 ∧ A.val *ᵥ frameVector i = a • imageVector c i by
    obtain ⟨a, _, heq⟩ := this
    symm
    change mk (ZMod 3) (A.val *ᵥ frameVector i) _ = _
    rw [← mk_rep (Collineation.pointHom PG PG c (frame i))]
    exact (mk_eq_mk_iff' (ZMod 3) _ _ _ _).mpr ⟨a, heq.symm⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact ⟨B.det, hB, hlast⟩
  · exact ⟨B.det * x j, mul_ne_zero hB (hx j), hcoord j⟩

end Configuration.PlaneThree
