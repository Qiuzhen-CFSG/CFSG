module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/BinaryFieldEmbedding.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and a coefficientwise prime-field extension.
-/

public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.CharP.Two
set_option warningAsError false

/-!
# The binary split-octonion model embeds over every characteristic-two field

The embedding is obtained by taking the matrix of a binary octonion
automorphism in the coordinate basis and applying `ZMod.castHom` entrywise.
The integral multiplication table makes the coefficientwise extension preserve
the concrete octonion product.  This is an actual embedding of the full model;
no order or simplicity statement is used.
-/

@[expose] public section

namespace Atlas.G2

open Atlas.SplitOctonion
open Matrix
noncomputable section

variable {F : Type*} [Field F] [CharP F 2]

/-- The coordinate matrix of a binary octonion automorphism. -/
def binaryMatrix (g : Model (ZMod 2)) : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2) :=
  (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun (ZMod 2) (Fin 8))).symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv g.val)

/-- Entrywise extension of the binary coordinate matrix to `F`. -/
def mappedMatrix (g : Model (ZMod 2)) : Matrix.GeneralLinearGroup (Fin 8) F :=
  Matrix.GeneralLinearGroup.map (ZMod.castHom (dvd_refl 2) F) (binaryMatrix g)

/-- The `F`-linear automorphism represented by the extended matrix. -/
def mappedLinear (g : Model (ZMod 2)) : Carrier F ≃ₗ[F] Carrier F :=
  (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun F (Fin 8)) (mappedMatrix g)).toLinearEquiv

lemma mappedLinear_apply (g : Model (ZMod 2)) (x : Carrier F) :
    mappedLinear g x = Fintype.linearCombination F (Pi.basisFun F (Fin 8))
      (((mappedMatrix (F := F) g : Matrix.GeneralLinearGroup (Fin 8) F) :
        Matrix (Fin 8) (Fin 8) F) *ᵥ x) := by
  exact Matrix.GeneralLinearGroup.toLin'_apply (Pi.basisFun F (Fin 8)) (mappedMatrix g) x

def coeffMap (x : Carrier (ZMod 2)) : Carrier F :=
  fun i => ZMod.castHom (dvd_refl 2) F (x i)

lemma coeffMap_add (x y : Carrier (ZMod 2)) :
    coeffMap (F := F) (x + y) = coeffMap x + coeffMap y := by
  ext i
  exact map_add _ _ _

lemma coeffMap_smul (r : ZMod 2) (x : Carrier (ZMod 2)) :
    coeffMap (F := F) (r • x) = (ZMod.castHom (dvd_refl 2) F r) • coeffMap x := by
  ext i
  exact map_mul _ _ _

lemma coeffMap_mul (x y : Carrier (ZMod 2)) :
    coeffMap (F := F) (mul x y) = mul (coeffMap x) (coeffMap y) := by
  ext i
  fin_cases i <;> simp [coeffMap, mul, CharTwo.neg_eq]

lemma coeffMap_basisVector (i : Fin 8) :
    coeffMap (F := F) (basisVector i : Carrier (ZMod 2)) = basisVector i := by
  ext j
  simp [coeffMap, basisVector, Pi.single_apply, eq_comm]

lemma binaryMatrix_action (g : Model (ZMod 2)) (x : Carrier (ZMod 2)) :
    (binaryMatrix g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x = g.val x := by
  have hg : (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun (ZMod 2) (Fin 8)))
      (binaryMatrix g) = LinearMap.GeneralLinearGroup.ofLinearEquiv g.val := by
    exact (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun (ZMod 2) (Fin 8))).apply_symm_apply _
  have hga := congrArg (fun z : LinearMap.GeneralLinearGroup (ZMod 2)
      (Carrier (ZMod 2)) => z.toLinearEquiv x) hg
  have hrepr : (Pi.basisFun (ZMod 2) (Fin 8)).repr x = x := by
    funext j
    exact Pi.basisFun_repr _ _ _ _
  rw [Matrix.GeneralLinearGroup.toLin'_apply] at hga
  rw [hrepr] at hga
  ext i
  simpa [Matrix.GeneralLinearGroup.toLin'_apply, Pi.basisFun_repr,
    LinearMap.GeneralLinearGroup.coe_ofLinearEquiv, Fintype.linearCombination_apply,
    Matrix.mulVec, dotProduct, Pi.basisFun_apply, Pi.single_apply] using congrFun hga i

lemma mappedMatrix_apply (g : Model (ZMod 2)) (i j : Fin 8) :
    (mappedMatrix (F := F) g : Matrix (Fin 8) (Fin 8) F) i j =
      ZMod.castHom (dvd_refl 2) F ((binaryMatrix g : Matrix (Fin 8) (Fin 8) (ZMod 2)) i j) := by
  exact Matrix.GeneralLinearGroup.map_apply _ _ _ _

lemma mappedLinear_action (g : Model (ZMod 2)) (x : Carrier (ZMod 2)) :
    mappedLinear (F := F) g (coeffMap (F := F) x) = coeffMap (F := F) (g.val x) := by
  classical
  apply funext
  intro i
  rw [mappedLinear_apply]
  simp only [Fintype.linearCombination_apply, Matrix.mulVec, dotProduct,
    Pi.basisFun_apply]
  simp [Pi.single_apply, coeffMap]
  simp_rw [mappedMatrix_apply]
  have hs := congrFun (binaryMatrix_action g x) i
  have hsc := congrArg (ZMod.castHom (dvd_refl 2) F) hs
  change (∑ j, ZMod.castHom (dvd_refl 2) F
      ((binaryMatrix g : Matrix (Fin 8) (Fin 8) (ZMod 2)) i j) *
      ZMod.castHom (dvd_refl 2) F (x j)) =
    ZMod.castHom (dvd_refl 2) F ((g.val x) i)
  simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul] using hsc

lemma mappedLinear_preserves_mul (g : Model (ZMod 2)) (x y : Carrier F) :
    mappedLinear (F := F) g (mul x y) =
      mul (mappedLinear (F := F) g x) (mappedLinear (F := F) g y) := by
  classical
  have hpair (i j : Fin 8) :
      mappedLinear (F := F) g (mul (basisVector i) (basisVector j)) =
        mul (mappedLinear (F := F) g (basisVector i))
          (mappedLinear (F := F) g (basisVector j)) := by
    rw [← coeffMap_basisVector (F := F) i, ← coeffMap_basisVector (F := F) j,
      ← coeffMap_mul]
    rw [mappedLinear_action, mappedLinear_action, mappedLinear_action,
      automorphism_mul, coeffMap_mul]
  have hleft (i : Fin 8) (z : Carrier F) :
      mappedLinear (F := F) g (mul (basisVector i) z) =
        mul (mappedLinear (F := F) g (basisVector i))
          (mappedLinear (F := F) g z) := by
    let A : Carrier F →ₗ[F] Carrier F :=
      { toFun := fun w => mappedLinear (F := F) g (mul (basisVector i) w)
        map_add' := by intro u v; rw [Atlas.SplitOctonion.mul_add, map_add]
        map_smul' := by intro r u; rw [Atlas.SplitOctonion.mul_smul, map_smul]; rfl }
    let B : Carrier F →ₗ[F] Carrier F :=
      { toFun := fun w => mul (mappedLinear (F := F) g (basisVector i))
          (mappedLinear (F := F) g w)
        map_add' := by intro u v; rw [map_add, Atlas.SplitOctonion.mul_add]
        map_smul' := by intro r u; rw [map_smul, Atlas.SplitOctonion.mul_smul]; rfl }
    have hAB : A = B := (Pi.basisFun F (Fin 8)).ext (fun j =>
      by simpa [A, B, basisVector, Pi.basisFun_apply] using hpair i j)
    exact DFunLike.congr_fun hAB z
  let A : Carrier F →ₗ[F] Carrier F :=
    { toFun := fun z => mappedLinear (F := F) g (mul z y)
      map_add' := by intro u v; rw [Atlas.SplitOctonion.add_mul, map_add]
      map_smul' := by intro r u; rw [Atlas.SplitOctonion.smul_mul, map_smul]; rfl }
  let B : Carrier F →ₗ[F] Carrier F :=
    { toFun := fun z => mul (mappedLinear (F := F) g z)
        (mappedLinear (F := F) g y)
      map_add' := by intro u v; rw [map_add, Atlas.SplitOctonion.add_mul]
      map_smul' := by intro r u; rw [map_smul, Atlas.SplitOctonion.smul_mul]; rfl }
  have hAB : A = B := (Pi.basisFun F (Fin 8)).ext (fun i =>
    by simpa [A, B, basisVector, Pi.basisFun_apply] using hleft i y)
  exact DFunLike.congr_fun hAB x

lemma binaryMatrix_one : binaryMatrix (1 : Model (ZMod 2)) = 1 := by
  apply (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun (ZMod 2) (Fin 8))).injective
  simp [binaryMatrix]
  apply Units.ext
  apply LinearMap.ext
  intro x
  rfl

lemma binaryMatrix_mul (g h : Model (ZMod 2)) :
    binaryMatrix (g * h) = binaryMatrix g * binaryMatrix h := by
  apply (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun (ZMod 2) (Fin 8))).injective
  simp [binaryMatrix, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul]

lemma mappedMatrix_one : mappedMatrix (F := F) (1 : Model (ZMod 2)) = 1 := by
  rw [mappedMatrix, binaryMatrix_one]
  exact (Matrix.GeneralLinearGroup.map_one _)

lemma mappedMatrix_mul (g h : Model (ZMod 2)) :
    mappedMatrix (F := F) (g * h) = mappedMatrix g * mappedMatrix h := by
  change Matrix.GeneralLinearGroup.map _ (binaryMatrix (g * h)) =
    Matrix.GeneralLinearGroup.map _ (binaryMatrix g) *
      Matrix.GeneralLinearGroup.map _ (binaryMatrix h)
  rw [binaryMatrix_mul, Matrix.GeneralLinearGroup.map_mul]

/-- The actual embedding of the binary split-octonion automorphism model. -/
def binaryFieldEmbedding : Model (ZMod 2) →* Model F where
  toFun g := ⟨mappedLinear (F := F) g, mappedLinear_preserves_mul (F := F) g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change ((Matrix.GeneralLinearGroup.toLin' (Pi.basisFun F (Fin 8)))
      (mappedMatrix (F := F) (1 : Model (ZMod 2)))).toLinearEquiv x = x
    rw [mappedMatrix_one]
    simp
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change ((Matrix.GeneralLinearGroup.toLin' (Pi.basisFun F (Fin 8)))
      (mappedMatrix (F := F) (g * h))).toLinearEquiv x =
      (((Matrix.GeneralLinearGroup.toLin' (Pi.basisFun F (Fin 8)))
        (mappedMatrix (F := F) g)).toLinearEquiv *
        ((Matrix.GeneralLinearGroup.toLin' (Pi.basisFun F (Fin 8)))
          (mappedMatrix (F := F) h)).toLinearEquiv) x
    rw [mappedMatrix_mul]
    rw [← LinearMap.GeneralLinearGroup.toLinearEquiv_mul]
    rw [← (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun F (Fin 8))).map_mul]

@[simp] theorem binaryFieldEmbedding_action (g : Model (ZMod 2)) (x : Carrier (ZMod 2)) :
    (binaryFieldEmbedding (F := F) g).val (coeffMap (F := F) x) =
      coeffMap (F := F) (g.val x) :=
  mappedLinear_action (F := F) g x

theorem binaryFieldEmbedding_injective : Function.Injective (binaryFieldEmbedding (F := F)) := by
  intro g h e
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hx := congrArg (fun z : Model F => z.val (coeffMap (F := F) x)) e
  rw [binaryFieldEmbedding_action, binaryFieldEmbedding_action] at hx
  ext i
  apply ZMod.castHom_injective F
  exact congrFun hx i

end
end Atlas.G2
