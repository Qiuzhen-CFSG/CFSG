module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.Models
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition.TensorAssembly
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Tensor comparisons with the literal G.9.3 models

The map v tensor w to v w^t identifies the two-dimensional tensor with
matrix space. Twisting the right SL₂ factor by inverse transpose turns its
action into M ↦ A M B⁻¹. Determinant coordinates and elementaryEquiv then
identify the actual nonprojective Ω₄⁺ action, with binary scalar restriction.

In dimension three, the proved PSL₃(2)-to-linear-group comparison identifies
the tensor with precisely threeTensor. These are action comparisons, not
family tags. Source: Aschbacher--Smith, G.9.3(14),(15), printed pp.354,356.
-/

@[expose] public noncomputable section

open scoped MatrixGroups TensorProduct

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition

open ClassicalOrthogonal.FourPlusMatrix

variable {F : Type*} [Field F]

private theorem transpose_mul {d : ℕ} (g h : SL(d,F)) :
    (g * h).transpose = h.transpose * g.transpose :=
  Subtype.ext (Matrix.transpose_mul _ _)

private theorem transpose_one {d : ℕ} : (1 : SL(d,F)).transpose = 1 :=
  Subtype.ext Matrix.transpose_one

private theorem transpose_transpose {d : ℕ} (g : SL(d,F)) :
    g.transpose.transpose = g := Subtype.ext (Matrix.transpose_transpose _)

private theorem transpose_inv {d : ℕ} (g : SL(d,F)) :
    g⁻¹.transpose = g.transpose⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← transpose_mul, mul_inv_cancel, transpose_one]

private def inverseTranspose {d : ℕ} : MulAut SL(d,F) where
  toFun g := g⁻¹.transpose
  invFun g := g⁻¹.transpose
  left_inv g := by simp only [transpose_inv, inv_inv, transpose_transpose]
  right_inv g := by simp only [transpose_inv, inv_inv, transpose_transpose]
  map_mul' g h := by rw [mul_inv_rev, transpose_mul]

private def tensorMatrix : ((Fin 2 → F) ⊗[F] (Fin 2 → F)) ≃ₗ[F] Mat (F := F) :=
  (TensorProduct.piScalarRight F F (Fin 2 → F) (Fin 2)).trans
    (Matrix.transposeLinearEquiv _ _ F F)

private theorem tensorMatrix_tmul (v w : Fin 2 → F) :
    tensorMatrix (v ⊗ₜ[F] w) = Matrix.vecMulVec v w := by
  ext i j
  change w j * v i = v i * w j
  exact mul_comm _ _

private theorem tensorMatrix_intertwines (g : SL(2,F) × SL(2,F))
    (z : (Fin 2 → F) ⊗[F] (Fin 2 → F)) :
    tensorMatrix (TensorProduct.map (Representation.specialLinearNatural 2 g.1)
      (Representation.specialLinearNatural 2 g.2) z) =
      representation (g.1, inverseTranspose g.2) (tensorMatrix z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v w =>
    rw [TensorProduct.map_tmul, tensorMatrix_tmul, tensorMatrix_tmul]
    change Matrix.vecMulVec (g.1.val.mulVec v) (g.2.val.mulVec w) =
      g.1.val * Matrix.vecMulVec v w * (inverseTranspose g.2)⁻¹.val
    have hi : (inverseTranspose g.2)⁻¹.val = g.2.val.transpose := by
      change (g.2⁻¹.transpose)⁻¹.val = g.2.val.transpose
      rw [transpose_inv, inv_inv]
      rfl
    rw [hi]
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring

/-- The natural two-by-two tensor is the nonprojective elementary orthogonal
module. The right group coordinate is twisted by inverse transpose. -/
theorem naturalTensor_fourOrthogonal (n : ℕ) :
    Quasiequivalent
      (Representation.restrictScalars (k := ZMod 2)
        (externalTensor (Representation.specialLinearNatural (k := GaloisField 2 n) 2)
          (Representation.specialLinearNatural 2)))
      (fourOrthogonal n) := by
  let e := ((MulEquiv.refl SL(2,GaloisField 2 n)).prodCongr inverseTranspose).trans
    elementaryEquiv
  let f := ((tensorMatrix (F := GaloisField 2 n)).trans coordinates.symm).restrictScalars (ZMod 2)
  refine ⟨e, f, ?_⟩
  intro g v
  apply coordinates.injective
  change coordinates (coordinates.symm (tensorMatrix
    (TensorProduct.map (Representation.specialLinearNatural 2 g.1)
      (Representation.specialLinearNatural 2 g.2) v))) =
    coordinates ((toOrthogonal (g.1, inverseTranspose g.2)).val
      (coordinates.symm (tensorMatrix v)))
  rw [LinearEquiv.apply_symm_apply, toOrthogonal_coordinates,
    LinearEquiv.apply_symm_apply, tensorMatrix_intertwines]
  rfl

/-- The natural SL₃(2) tensor uses exactly the PSL₃(2) carrier of `threeTensor`. -/
theorem naturalTensor_threeTensor :
    Quasiequivalent
      (Representation.restrictScalars (k := ZMod 2)
        (externalTensor (Representation.specialLinearNatural (k := ZMod 2) 3)
          (Representation.specialLinearNatural 3))) threeTensor := by
  let e := (BinaryLinear.OuterCyclic.projectiveEquivSL (n := 3) (by decide)).symm
  refine ⟨e.prodCongr e, LinearEquiv.refl _ _, ?_⟩
  intro g v
  change TensorProduct.map (Representation.specialLinearNatural 3 g.1)
    (Representation.specialLinearNatural 3 g.2) v =
    TensorProduct.map (threeNatural (e g.1)) (threeNatural (e g.2)) v
  have hn (a : SL(3,ZMod 2)) : threeNatural (e a) = Representation.specialLinearNatural 3 a := by
    apply LinearMap.ext
    intro x
    change BinaryLinear.OuterCyclic.slEquivLinear 3
      (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide) (e a)) x = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [hn, hn]

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition
