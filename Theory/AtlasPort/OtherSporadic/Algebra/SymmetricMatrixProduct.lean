/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/SymmetricMatrixProduct.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Algebra.SymmetricMatrixSpace
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Linearization on symmetric matrices

A semibilinear product induces a semilinear map on symmetric matrices.
Rank-one squares recover diagonal values; polarization then proves uniqueness.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/SymmetricMatrixProduct.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports;
polarization cancels the unit scalar two directly, and simplification lists
omit redundant entries. Definitions remain exposed for downstream calculations.
-/

@[expose] public section

noncomputable section
namespace Atlas.Algebra
open scoped BigOperators

variable {K I W : Type*} [Field K] [Fintype I] [DecidableEq I]
  [AddCommGroup W] [Module K W] (σ : K →+* K)

/-- Linearization on actual symmetric matrices. Both arguments of B use the same
scalar automorphism; this includes bilinear and conjugate-bilinear products. -/
def symmetricMatrixProduct
    (B : (I → K) →ₛₗ[σ] (I → K) →ₛₗ[σ] W) :
    symmetricMatrixSpace K I →ₛₗ[σ] W where
  toFun M := ∑ i, ∑ j, σ (M.val i j) • B (Pi.single i 1) (Pi.single j 1)
  map_add' M N := by
    simp only [Submodule.coe_add, Matrix.add_apply, map_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' a M := by
    simp only [Submodule.coe_smul, Matrix.smul_apply, smul_eq_mul, map_mul,
      mul_smul, Finset.smul_sum]

theorem coordinate_sum_smul_single (x : I → K) :
    (∑ i, x i • Pi.single i (1 : K)) = x := by
  funext j
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]

/-- The diagonal of B is represented by the genuine symmetric rank-one matrix. -/
theorem symmetricMatrixProduct_square
    (B : (I → K) →ₛₗ[σ] (I → K) →ₛₗ[σ] W) (x : I → K) :
    symmetricMatrixProduct σ B (symmetricMatrixSquare x) = B x x := by
  conv_rhs => rw [← coordinate_sum_smul_single x]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum, symmetricMatrixProduct]
  change (∑ i, ∑ j, σ (x i * x j) • B (Pi.single i 1) (Pi.single j 1)) = _
  simp only [map_mul, mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ _ _

/-- For symmetric bilinear or conjugate-bilinear maps in characteristic not two,
values on diagonal vectors whose squares form a basis determine the entire map. -/
theorem symmetricMatrixProduct_ext {J : Type*}
    (b : Module.Basis J K (symmetricMatrixSpace K I)) (v : J → I → K)
    (hb : ∀ j, b j = symmetricMatrixSquare (v j)) (h2 : (2 : K) ≠ 0)
    (B C : (I → K) →ₛₗ[σ] (I → K) →ₛₗ[σ] W)
    (hB : ∀ x y, B x y = B y x) (hC : ∀ x y, C x y = C y x)
    (hd : ∀ j, B (v j) (v j) = C (v j) (v j)) : B = C := by
  have hl : symmetricMatrixProduct σ B = symmetricMatrixProduct σ C := by
    apply b.ext
    intro j
    rw [hb, symmetricMatrixProduct_square, symmetricMatrixProduct_square, hd]
  have hdiag (x : I → K) : B x x = C x x := by
    have h := DFunLike.congr_fun hl (symmetricMatrixSquare x)
    simpa only [symmetricMatrixProduct_square] using h
  ext x y
  apply (IsUnit.smul_left_cancel (isUnit_iff_ne_zero.mpr h2)).mp
  have h := hdiag (x + y)
  simp only [map_add, LinearMap.add_apply] at h
  rw [hB y x, hC y x, hdiag x, hdiag y] at h
  simpa only [two_smul] using (show B x y + B x y = C x y + C x y by
    have h' : (C x x + (B x y + B x y)) + C y y =
        (C x x + (C x y + C x y)) + C y y := by
      simpa only [add_assoc] using h
    exact add_left_cancel (add_right_cancel h'))

end Atlas.Algebra
