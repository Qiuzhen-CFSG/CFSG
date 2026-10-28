/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from Atlas/LinearAlgebra/BilinearLineSplit.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Changes: CFSG imports and reflection APIs, Lean 4.33 public module boundaries,
and the existing shared Atlas.SquareClass quotient (where needed).
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! # Splitting a bilinear form at a vector with nonzero diagonal

A vector with nonzero diagonal splits off from its right-perpendicular
space using its bilinear coordinate. The resulting Gram matrix is block
triangular, yielding determinant factorization and nondegeneracy of the
complement without assuming symmetry.
-/
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace Atlas.Bilinear
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (B : LinearMap.BilinForm F V) (a : V)

abbrev linePerp : Submodule F V := (B a).ker

def lineCoordinate : V →ₗ[F] F := (B a a)⁻¹ • B a

variable (ha : B a a ≠ 0)

include ha in
theorem lineCoordinate_self : lineCoordinate B a a = 1 := inv_mul_cancel₀ ha

theorem lineCoordinate_perp (x : linePerp B a) : lineCoordinate B a x.val = 0 := by
  change (B a a)⁻¹ * B a x.val = 0
  have hx : B a x.val = 0 := x.prop
  rw [hx, mul_zero]

include ha in
theorem lineRemainder_mem (x : V) : x - lineCoordinate B a x • a ∈ linePerp B a := by
  change B a (x-lineCoordinate B a x • a) = 0
  rw [map_sub, map_smul, smul_eq_mul]
  change B a x - ((B a a)⁻¹ * B a x) * B a a = 0
  field_simp
  ring

def lineSplit : V ≃ₗ[F] F × linePerp B a where
  toFun x := (lineCoordinate B a x, ⟨x-lineCoordinate B a x • a, lineRemainder_mem B a ha x⟩)
  invFun x := x.1 • a + x.2.val
  left_inv x := by change lineCoordinate B a x • a + (x-lineCoordinate B a x • a) = x; abel
  right_inv x := by
    apply Prod.ext
    · change lineCoordinate B a (x.1 • a + x.2.val) = x.1
      rw [map_add, map_smul, lineCoordinate_self B a ha, lineCoordinate_perp, smul_eq_mul, mul_one, add_zero]
    · apply Subtype.ext
      change x.1 • a + x.2.val - lineCoordinate B a (x.1 • a+x.2.val) • a = x.2.val
      rw [map_add, map_smul, lineCoordinate_self B a ha, lineCoordinate_perp, smul_eq_mul, mul_one, add_zero]
      abel
  map_add' x y := by
    apply Prod.ext
    · exact map_add _ _ _
    · apply Subtype.ext
      change x+y-lineCoordinate B a (x+y) • a = (x-lineCoordinate B a x • a)+(y-lineCoordinate B a y • a)
      rw [map_add, _root_.add_smul]
      abel
  map_smul' c x := by
    apply Prod.ext
    · exact map_smul _ _ _
    · apply Subtype.ext
      change c • x-lineCoordinate B a (c • x) • a = c • (x-lineCoordinate B a x • a)
      rw [map_smul, smul_sub, smul_smul, smul_eq_mul]

include ha in
theorem linePerp_finrank [FiniteDimensional F V] : Module.finrank F (linePerp B a) + 1 = Module.finrank F V := by
  have h := (lineSplit B a ha).finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_self, Nat.add_comm] using h.symm


def linePerpForm : LinearMap.BilinForm F (linePerp B a) :=
  B.compl₁₂ (linePerp B a).subtype (linePerp B a).subtype

variable {ι : Type*} (b : Module.Basis ι F (linePerp B a))

def lineBasis : Module.Basis (Unit ⊕ ι) F V :=
  ((Module.Basis.singleton Unit F).prod b).map (lineSplit B a ha).symm

@[simp] theorem lineBasis_inl (i : Unit) : lineBasis B a ha b (Sum.inl i) = a := by
  change (((Module.Basis.singleton Unit F).prod b) (Sum.inl i)).1 • a +
    (((Module.Basis.singleton Unit F).prod b) (Sum.inl i)).2.val = a
  rw [Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd,
    Module.Basis.singleton_apply]
  simp

@[simp] theorem lineBasis_inr (i : ι) : lineBasis B a ha b (Sum.inr i) = (b i).val := by
  change (((Module.Basis.singleton Unit F).prod b) (Sum.inr i)).1 • a +
    (((Module.Basis.singleton Unit F).prod b) (Sum.inr i)).2.val = (b i).val
  rw [Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd]
  simp

/-- Triangular Gram factorization; symmetry is not required. -/
theorem lineBasis_det [Fintype ι] [DecidableEq ι] :
    (LinearMap.BilinForm.toMatrix (lineBasis B a ha b) B).det =
      B a a * (LinearMap.BilinForm.toMatrix b (linePerpForm B a)).det := by
  have hm : LinearMap.BilinForm.toMatrix (lineBasis B a ha b) B =
      Matrix.fromBlocks (Matrix.of (fun _ _ : Unit => B a a)) 0
        (Matrix.of (fun i (_ : Unit) => B (b i).val a))
        (LinearMap.BilinForm.toMatrix b (linePerpForm B a)) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [LinearMap.BilinForm.toMatrix_apply]
      | inr j =>
        simp only [LinearMap.BilinForm.toMatrix_apply, lineBasis_inl, lineBasis_inr,
          Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
        exact (b j).prop
    | inr i =>
      cases j with
      | inl j => simp [LinearMap.BilinForm.toMatrix_apply]
      | inr j => simp [LinearMap.BilinForm.toMatrix_apply, linePerpForm]
  rw [hm, Matrix.det_fromBlocks_zero₁₂, Matrix.det_unique]
  rfl

include ha b in
/-- A nonzero diagonal line leaves a nondegenerate right-perpendicular restriction. -/
theorem linePerpForm_nondegenerate [Fintype ι] [DecidableEq ι]
    (hB : B.Nondegenerate) : (linePerpForm B a).Nondegenerate := by
  apply (LinearMap.nondegenerate_iff_det_ne_zero b).mpr
  have h := (LinearMap.nondegenerate_iff_det_ne_zero (lineBasis B a ha b)).mp hB
  change (LinearMap.BilinForm.toMatrix (lineBasis B a ha b) B).det ≠ 0 at h
  rw [lineBasis_det] at h
  exact (mul_ne_zero_iff.mp h).2

end Atlas.Bilinear


