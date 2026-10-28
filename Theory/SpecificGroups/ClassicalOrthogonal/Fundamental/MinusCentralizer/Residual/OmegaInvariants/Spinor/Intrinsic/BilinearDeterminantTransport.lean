/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from Atlas/LinearAlgebra/BilinearDeterminantTransport.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Changes: CFSG imports and reflection APIs, Lean 4.33 public module boundaries,
and the existing shared Atlas.SquareClass quotient (where needed).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.Intrinsic.BilinearDeterminantClass
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.Intrinsic.BilinearLineSplit

/-! # Transport and line factorization of bilinear determinant square classes

Reindexing and isometric transport preserve the Gram determinant class.
The explicit right-perpendicular splitting gives the product formula for
a nonzero diagonal line; this is consumed by the Wall reflection law.
-/
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace Atlas.Bilinear
variable {F V W ι κ : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]
variable (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)

theorem determinantClass_reindex (b : Module.Basis ι F V) (e : ι ≃ κ) :
    determinantClass B hB (b.reindex e) = determinantClass B hB b := by
  apply congrArg (Atlas.squareClass F)
  apply Units.ext
  change (LinearMap.BilinForm.toMatrix (b.reindex e) B).det =
    (LinearMap.BilinForm.toMatrix b B).det
  have hm : LinearMap.BilinForm.toMatrix (b.reindex e) B =
      Matrix.reindex e e (LinearMap.BilinForm.toMatrix b B) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply]
  rw [hm, Matrix.det_reindex_self]

/-- Basis independence also holds for different finite index types. -/
theorem determinantClass_basis_independent_any (b : Module.Basis ι F V)
    (c : Module.Basis κ F V) : determinantClass B hB b = determinantClass B hB c := by
  rw [← determinantClass_reindex B hB b (b.indexEquiv c)]
  exact determinantClass_basis_independent B hB _ _

theorem determinantClass_transport (C : LinearMap.BilinForm F W) (hC : C.Nondegenerate)
    (e : V ≃ₗ[F] W) (he : ∀ x y, C (e x) (e y) = B x y)
    (b : Module.Basis ι F V) :
    determinantClass C hC (b.map e) = determinantClass B hB b := by
  apply congrArg (Atlas.squareClass F)
  apply Units.ext
  change (LinearMap.BilinForm.toMatrix (b.map e) C).det =
    (LinearMap.BilinForm.toMatrix b B).det
  congr 1
  ext i j
  simpa only [LinearMap.BilinForm.toMatrix_apply, Module.Basis.map_apply] using he (b i) (b j)

/-- Intrinsic square-class factorization at a nonzero diagonal vector. -/
theorem determinantClass_line (a : V) (ha : B a a ≠ 0)
    (b : Module.Basis ι F (linePerp B a)) :
    determinantClass B hB (lineBasis B a ha b) =
      Atlas.squareClass F (Units.mk0 (B a a) ha) *
        determinantClass (linePerpForm B a) (linePerpForm_nondegenerate B a ha b hB) b := by
  unfold determinantClass
  rw [← map_mul]
  apply congrArg (Atlas.squareClass F)
  apply Units.ext
  change (LinearMap.BilinForm.toMatrix (lineBasis B a ha b) B).det =
    B a a * (LinearMap.BilinForm.toMatrix b (linePerpForm B a)).det
  exact lineBasis_det B a ha b

end Atlas.Bilinear

