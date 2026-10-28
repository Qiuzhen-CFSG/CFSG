module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionCentralizerSetup
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Matrix invariants for the center of the concrete Lyons involution subgroup

The proved word relations force determinant one on the entire matrix group.
Consequently no represented element is the negative of another represented
element, since the dimension is odd and the characteristic is five. An invariant
bilinear form for the two local generators is invariant under their subgroup.

These facts reduce the local center bound to two independent finite matrix
certificates: a two-dimensional commutant, and a form that restricts that
commutant to the four matrices `1`, `t`, `-1`, and `-t`. Neither certificate is
asserted here. In particular, the ATLAS label `2.A11` is not a proof input.

Source matrices and subgroup words: R. A. Wilson et al., ATLAS of Finite Group
Representations, `LyG1-f5r111B0` and `LyG1-max4W1`. Their original data and
attribution are retained in `Atlas111Source/` and `Atlas111InvolutionSource/`.
-/

namespace Lyons.SimplicityCertificate

private def localCenterDetHom : LyonsGroup →* (ZMod 5)ˣ where
  toFun g :=
    { val := (matrixRepresentation g).det
      inv := (matrixRepresentation g⁻¹).det
      val_inv := by
        rw [← Matrix.det_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.det_one]
      inv_val := by
        rw [← Matrix.det_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.det_one] }
  map_one' := Units.ext (by dsimp only; rw [map_one, Matrix.det_one, Units.val_one])
  map_mul' g h := Units.ext (by
    dsimp only
    rw [map_mul, Matrix.det_mul, Units.val_mul])

private theorem localCenterDetHom_val (g : LyonsGroup) :
    (localCenterDetHom g).val = (matrixRepresentation g).det := rfl

/-- The actual ambient matrix group has determinant one, by the proved relations. -/
public theorem matrixRepresentation_det_one (g : LyonsGroup) :
    (matrixRepresentation g).det = 1 := by
  have hf : localCenterDetHom = 1 := hom_to_commGroup_eq_one generatorB_pow_five
    generatorAB_pow_fourteen perfectWord_pow_sixty_seven localCenterDetHom
  have h : localCenterDetHom g = 1 := DFunLike.congr_fun hf g
  rw [← localCenterDetHom_val, h, Units.val_one]

/-- Odd dimension excludes negatives of represented group elements. -/
public theorem matrixRepresentation_ne_neg (g h : LyonsGroup) :
    matrixRepresentation g ≠ -matrixRepresentation h := by
  intro heq
  have hd := matrixRepresentation_det_one g
  rw [heq, Matrix.det_neg, matrixRepresentation_det_one] at hd
  norm_num at hd
  exact (by decide : (-1 : ZMod 5) ≠ 1) hd

/-- The proposed central element squares to one unconditionally. -/
public theorem involutionLocalT_sq : involutionLocalT ^ 2 = 1 := by
  rw [involutionLocalT, ← pow_mul]
  exact generatorAB_pow_fourteen

/-- The candidate two-dimensional matrix commutant. -/
@[expose] public def involutionLocalScalarMatrix (u v : ZMod 5) : AtlasMatrix :=
  u • (1 : AtlasMatrix) + v • matrixRepresentation involutionLocalT

/-- The precise linear algebra certificate still required for the local commutant. -/
@[expose] public def InvolutionLocalCommutantCertificate : Prop :=
  ∀ M : AtlasMatrix,
    M * matrixRepresentation involutionLocalA = matrixRepresentation involutionLocalA * M →
    M * matrixRepresentation involutionLocalB = matrixRepresentation involutionLocalB * M →
    ∃ u v : ZMod 5, M = involutionLocalScalarMatrix u v

/-- The independent invariant-form certificate. Its last clause concerns only
the 25 scalar combinations, without any subgroup membership assumption. -/
@[expose] public def InvolutionLocalFormCertificate : Prop :=
  ∃ F : AtlasMatrix,
    (matrixRepresentation involutionLocalA).transpose * F *
      matrixRepresentation involutionLocalA = F ∧
    (matrixRepresentation involutionLocalB).transpose * F *
      matrixRepresentation involutionLocalB = F ∧
    ∀ u v : ZMod 5,
      (involutionLocalScalarMatrix u v).transpose * F * involutionLocalScalarMatrix u v = F →
      involutionLocalScalarMatrix u v = 1 ∨
      involutionLocalScalarMatrix u v = matrixRepresentation involutionLocalT ∨
      involutionLocalScalarMatrix u v = -(1 : AtlasMatrix) ∨
      involutionLocalScalarMatrix u v = -matrixRepresentation involutionLocalT

set_option maxRecDepth 10000 in
/-- Central elements of the subgroup commute with each generator in the faithful
matrix representation. -/
public theorem involutionLocal_center_matrix_commutes
    (z : involutionLocalSubgroup) (hz : z ∈ Subgroup.center involutionLocalSubgroup)
    (g : LyonsGroup) (hg : g ∈ involutionLocalSubgroup) :
    matrixRepresentation (z : LyonsGroup) * matrixRepresentation g =
      matrixRepresentation g * matrixRepresentation (z : LyonsGroup) := by
  have h := Subgroup.mem_center_iff.mp hz ⟨g, hg⟩
  exact (congrArg (fun x : involutionLocalSubgroup =>
    matrixRepresentation (x : LyonsGroup)) h).symm

/-- Invariance under the two literal output words propagates to their closure. -/
public theorem involutionLocal_preserves_form (F : AtlasMatrix)
    (ha : (matrixRepresentation involutionLocalA).transpose * F *
      matrixRepresentation involutionLocalA = F)
    (hb : (matrixRepresentation involutionLocalB).transpose * F *
      matrixRepresentation involutionLocalB = F)
    (g : LyonsGroup) (hg : g ∈ involutionLocalSubgroup) :
    (matrixRepresentation g).transpose * F * matrixRepresentation g = F := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ha
    · rcases hx with rfl
      exact hb
  | one => simp only [map_one, Matrix.transpose_one, one_mul, mul_one]
  | mul x y hx hy ihx ihy =>
    simp only [map_mul, Matrix.transpose_mul]
    calc
      _ = (matrixRepresentation y).transpose *
          ((matrixRepresentation x).transpose * F * matrixRepresentation x) *
          matrixRepresentation y := by simp only [Matrix.mul_assoc]
      _ = F := by rw [ihx, ihy]
  | inv x hx ih =>
    calc
      _ = (matrixRepresentation x⁻¹).transpose *
          ((matrixRepresentation x).transpose * F * matrixRepresentation x) *
          matrixRepresentation x⁻¹ := by rw [ih]
      _ = (matrixRepresentation x * matrixRepresentation x⁻¹).transpose * F *
          (matrixRepresentation x * matrixRepresentation x⁻¹) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = F := by rw [← map_mul, mul_inv_cancel, map_one]; simp

end Lyons.SimplicityCertificate
