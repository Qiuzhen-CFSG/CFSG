module

public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.SpecificGroups.SL2.Affine

/-!
# Affine coordinates for the degree-three local groups

A line-local matrix has the form [[A,v],[0,1]], giving its equivalence with
F² ⋊ SL₂(F) by direct multiplication. Inverse transpose followed by coordinate
reversal interchanges the actual point and line local groups. This also
identifies the point radical's contragredient action with a natural action.

No simplicity, core, or short-group property is assumed in these equivalences.
Source: Aschbacher–Smith, F.1.12(I)(1), printed pp.262–264.
-/

@[expose] public section
open Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F]
def affineToLine (g : Matrix.SL2.Affine F) : lineLocalSL F :=
  ⟨⟨!![g.right.val 0 0, g.right.val 0 1, Multiplicative.toAdd g.left 0;
      g.right.val 1 0, g.right.val 1 1, Multiplicative.toAdd g.left 1;
      0, 0, 1], by
    have hg := g.right.property
    rw [det_fin_two] at hg
    simpa [det_fin_three] using hg⟩,
    (mem_lineLocalSL_iff F _).mpr ⟨rfl, rfl, rfl⟩⟩
theorem affineToLine_mul (g h : Matrix.SL2.Affine F) :
    affineToLine F (g * h) = affineToLine F g * affineToLine F h := by
  apply Subtype.ext
  apply Subtype.ext
  change (affineToLine F (g * h)).val.val =
    (affineToLine F g).val.val * (affineToLine F h).val.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [affineToLine, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_two, mulVec, dotProduct, add_comm]
def lineToAffine (g : lineLocalSL F) : Matrix.SL2.Affine F :=
  ⟨Multiplicative.ofAdd ![g.val.val 0 2, g.val.val 1 2],
    ⟨!![g.val.val 0 0, g.val.val 0 1; g.val.val 1 0, g.val.val 1 1], by
      have hg := (mem_lineLocalSL_iff F g.val).mp g.property
      have hd := g.val.property
      rw [det_fin_three, hg.1, hg.2.1, hg.2.2] at hd
      simpa [det_fin_two] using hd⟩⟩
theorem lineToAffine_affineToLine (g : Matrix.SL2.Affine F) :
    lineToAffine F (affineToLine F g) = g := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> rfl
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

theorem affineToLine_lineToAffine (g : lineLocalSL F) :
    affineToLine F (lineToAffine F g) = g := by
  have hg := (mem_lineLocalSL_iff F g.val).mp g.property
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [affineToLine, lineToAffine, hg.1, hg.2.1, hg.2.2]

def lineLocalAffineEquiv : lineLocalSL F ≃* Matrix.SL2.Affine F :=
  { toFun := lineToAffine F
    invFun := affineToLine F
    left_inv := affineToLine_lineToAffine F
    right_inv := lineToAffine_affineToLine F
    map_mul' := by
      intro g h
      apply (Function.LeftInverse.injective (lineToAffine_affineToLine F))
      rw [affineToLine_mul, affineToLine_lineToAffine, affineToLine_lineToAffine,
        affineToLine_lineToAffine] }

private def reverseTranspose (g : SL(3, F)) : SL(3, F) :=
  ⟨g.val.transpose.submatrix Fin.rev Fin.rev, by
    exact (det_submatrix_equiv_self Fin.revPerm g.val.transpose).trans
      ((det_transpose g.val).trans g.property)⟩

private theorem reverseTranspose_one : reverseTranspose F 1 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem reverseTranspose_mul (g h : SL(3, F)) :
    reverseTranspose F (g * h) = reverseTranspose F h * reverseTranspose F g := by
  apply Subtype.ext
  change (g.val * h.val).transpose.submatrix Fin.rev Fin.rev =
    h.val.transpose.submatrix Fin.rev Fin.rev * g.val.transpose.submatrix Fin.rev Fin.rev
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_three, submatrix, transpose_apply]
  ring

private theorem reverseTranspose_involutive (g : SL(3, F)) :
    reverseTranspose F (reverseTranspose F g) = g := by
  apply Subtype.ext
  ext i j
  simp [reverseTranspose, submatrix]

private theorem reverseTranspose_inv (g : SL(3, F)) :
    reverseTranspose F g⁻¹ = (reverseTranspose F g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← reverseTranspose_mul, mul_inv_cancel, reverseTranspose_one]

/-- The graph automorphism, followed by reversal of the three coordinates. -/
def flagDuality : SL(3, F) ≃* SL(3, F) where
  toFun g := ⟨g⁻¹.val.transpose.submatrix Fin.rev Fin.rev,
    (det_submatrix_equiv_self Fin.revPerm g⁻¹.val.transpose).trans
      ((det_transpose g⁻¹.val).trans g⁻¹.property)⟩
  invFun g := ⟨g⁻¹.val.transpose.submatrix Fin.rev Fin.rev,
    (det_submatrix_equiv_self Fin.revPerm g⁻¹.val.transpose).trans
      ((det_transpose g⁻¹.val).trans g⁻¹.property)⟩
  left_inv g := by
    change reverseTranspose F ((reverseTranspose F g⁻¹)⁻¹) = g
    rw [reverseTranspose_inv F g, inv_inv, reverseTranspose_involutive]
  right_inv g := by
    change reverseTranspose F ((reverseTranspose F g⁻¹)⁻¹) = g
    rw [reverseTranspose_inv F g, inv_inv, reverseTranspose_involutive]
  map_mul' g h := by
    change reverseTranspose F (g * h)⁻¹ = reverseTranspose F g⁻¹ * reverseTranspose F h⁻¹
    rw [_root_.mul_inv_rev, reverseTranspose_mul]

theorem flagDuality_point_mem (g : pointLocalSL F) :
    flagDuality F g ∈ lineLocalSL F := by
  have hg := (mem_pointLocalSL_iff F _).mp ((pointLocalSL F).inv_mem g.property)
  rw [mem_lineLocalSL_iff]
  exact ⟨hg.2.2, hg.2.1, hg.1⟩

theorem flagDuality_line_mem (g : lineLocalSL F) :
    flagDuality F g ∈ pointLocalSL F := by
  have hg := (mem_lineLocalSL_iff F _).mp ((lineLocalSL F).inv_mem g.property)
  rw [mem_pointLocalSL_iff]
  exact ⟨hg.2.2, hg.2.1, hg.1⟩

/-- Point and line local groups are interchanged by contragredience. -/
def pointLineLocalEquiv : pointLocalSL F ≃* lineLocalSL F where
  toFun g := ⟨flagDuality F g, flagDuality_point_mem F g⟩
  invFun g := ⟨flagDuality F g, flagDuality_line_mem F g⟩
  left_inv g := Subtype.ext ((flagDuality F).left_inv g)
  right_inv g := Subtype.ext ((flagDuality F).right_inv g)
  map_mul' g h := Subtype.ext ((flagDuality F).map_mul g h)

def pointLocalAffineEquiv : pointLocalSL F ≃* Matrix.SL2.Affine F :=
  (pointLineLocalEquiv F).trans (lineLocalAffineEquiv F)

/-- The actual projective point-local subgroup has the same affine coordinates. -/
noncomputable def pointLocalEquivAffine : pointLocal F ≃* Matrix.SL2.Affine F :=
  (pointLocalProjectEquiv F).symm.trans (pointLocalAffineEquiv F)

/-- The actual projective line-local subgroup has the same affine coordinates. -/
noncomputable def lineLocalEquivAffine : lineLocal F ≃* Matrix.SL2.Affine F :=
  (lineLocalProjectEquiv F).symm.trans (lineLocalAffineEquiv F)

@[simp] theorem pointLocalEquivAffine_project (g : pointLocalSL F) :
    pointLocalEquivAffine F (pointLocalProjectEquiv F g) = pointLocalAffineEquiv F g :=
  congrArg (pointLocalAffineEquiv F) ((pointLocalProjectEquiv F).symm_apply_apply g)

@[simp] theorem lineLocalEquivAffine_project (g : lineLocalSL F) :
    lineLocalEquivAffine F (lineLocalProjectEquiv F g) = lineLocalAffineEquiv F g :=
  congrArg (lineLocalAffineEquiv F) ((lineLocalProjectEquiv F).symm_apply_apply g)

end Matrix.PSL3.LinearThree
