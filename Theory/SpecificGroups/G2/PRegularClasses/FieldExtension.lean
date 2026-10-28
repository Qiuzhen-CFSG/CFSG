module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/BinaryFieldEmbedding.lean, via the checked port
Theory/AtlasPort/LinearGroups/G2/BinaryFieldEmbedding.lean.
Changes: arbitrary field embeddings, characteristic-polynomial and order
compatibility, CFSG import paths and public module boundaries.
-/

public import Theory.SpecificGroups.G2.PRegularClasses.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Extending actual octonion automorphisms along a field embedding

The coordinate matrix of an octonion automorphism extends entrywise to any
larger field. The integral multiplication table is preserved on coordinate
basis vectors, and bilinearity then proves preservation on the full extended
algebra. Thus this is an embedding into the actual octonion automorphism group.
Its action intertwines coefficientwise extension, and it preserves element
orders and maps characteristic polynomials coefficientwise.

This supplies the shared finite-field-to-algebraic-closure comparison for
semisimple torus conjugacy and rational fusion in the G₂ class-count argument.
It assumes no conjugacy or algebraic-group comparison theorem.
-/

public section

namespace Atlas.G2.PRegularClasses.FieldExtension

open Atlas.SplitOctonion
open Matrix
noncomputable section

variable {F K : Type*} [Field F] [Field K]
variable (f : F →+* K)

/-- The coordinate matrix of an octonion automorphism. -/
@[expose] def coordinateMatrix (g : Model F) : Matrix.GeneralLinearGroup (Fin 8) F :=
  (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun F (Fin 8))).symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv g.val)

/-- Entrywise extension of the coordinate matrix to `K`. -/
private def mappedMatrix (g : Model F) : Matrix.GeneralLinearGroup (Fin 8) K :=
  Matrix.GeneralLinearGroup.map f (coordinateMatrix g)

/-- The `K`-linear automorphism represented by the extended matrix. -/
private def mappedLinear (g : Model F) : Carrier K ≃ₗ[K] Carrier K :=
  (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 8)) (mappedMatrix f g)).toLinearEquiv

private lemma mappedLinear_apply (g : Model F) (x : Carrier K) :
    mappedLinear f g x = Fintype.linearCombination K (Pi.basisFun K (Fin 8))
      (((mappedMatrix f g : Matrix.GeneralLinearGroup (Fin 8) K) :
        Matrix (Fin 8) (Fin 8) K) *ᵥ x) := by
  exact Matrix.GeneralLinearGroup.toLin'_apply (Pi.basisFun K (Fin 8)) (mappedMatrix f g) x

@[expose] def coeffMap (x : Carrier F) : Carrier K :=
  fun i => f (x i)

private lemma coeffMap_add (x y : Carrier F) :
    coeffMap f (x + y) = coeffMap f x + coeffMap f y := by
  ext i
  exact map_add _ _ _

private lemma coeffMap_smul (r : F) (x : Carrier F) :
    coeffMap f (r • x) = (f r) • coeffMap f x := by
  ext i
  exact map_mul _ _ _

lemma coeffMap_mul (x y : Carrier F) :
    coeffMap f (mul x y) = mul (coeffMap f x) (coeffMap f y) := by
  ext i
  fin_cases i <;> simp [coeffMap, mul]

lemma coeffMap_basisVector (i : Fin 8) :
    coeffMap f (basisVector i : Carrier F) = basisVector i := by
  ext j
  simp [coeffMap, basisVector, Pi.single_apply, eq_comm]

lemma coordinateMatrix_action (g : Model F) (x : Carrier F) :
    (coordinateMatrix g : Matrix (Fin 8) (Fin 8) F) *ᵥ x = g.val x := by
  have hg : (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun F (Fin 8)))
      (coordinateMatrix g) = LinearMap.GeneralLinearGroup.ofLinearEquiv g.val := by
    exact (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun F (Fin 8))).apply_symm_apply _
  have hga := congrArg (fun z : LinearMap.GeneralLinearGroup F
      (Carrier F) => z.toLinearEquiv x) hg
  have hrepr : (Pi.basisFun F (Fin 8)).repr x = x := by
    funext j
    exact Pi.basisFun_repr _ _ _ _
  rw [Matrix.GeneralLinearGroup.toLin'_apply] at hga
  rw [hrepr] at hga
  ext i
  simpa [Matrix.GeneralLinearGroup.toLin'_apply, Pi.basisFun_repr,
    LinearMap.GeneralLinearGroup.coe_ofLinearEquiv, Fintype.linearCombination_apply,
    Matrix.mulVec, dotProduct, Pi.basisFun_apply, Pi.single_apply] using congrFun hga i

private lemma mappedMatrix_apply (g : Model F) (i j : Fin 8) :
    (mappedMatrix f g : Matrix (Fin 8) (Fin 8) K) i j =
      f ((coordinateMatrix g : Matrix (Fin 8) (Fin 8) F) i j) := by
  exact Matrix.GeneralLinearGroup.map_apply _ _ _ _

private lemma mappedLinear_action (g : Model F) (x : Carrier F) :
    mappedLinear f g (coeffMap f x) = coeffMap f (g.val x) := by
  classical
  apply funext
  intro i
  rw [mappedLinear_apply f]
  simp only [Fintype.linearCombination_apply, Matrix.mulVec, dotProduct,
    Pi.basisFun_apply]
  simp [Pi.single_apply, coeffMap]
  simp_rw [mappedMatrix_apply f]
  have hs := congrFun (coordinateMatrix_action g x) i
  have hsc := congrArg (f) hs
  change (∑ j, f
      ((coordinateMatrix g : Matrix (Fin 8) (Fin 8) F) i j) *
      f (x j)) =
    f ((g.val x) i)
  simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul] using hsc

private lemma mappedLinear_preserves_mul (g : Model F) (x y : Carrier K) :
    mappedLinear f g (mul x y) =
      mul (mappedLinear f g x) (mappedLinear f g y) := by
  classical
  have hpair (i j : Fin 8) :
      mappedLinear f g (mul (basisVector i) (basisVector j)) =
        mul (mappedLinear f g (basisVector i))
          (mappedLinear f g (basisVector j)) := by
    rw [← coeffMap_basisVector f i, ← coeffMap_basisVector f j,
      ← coeffMap_mul f]
    rw [mappedLinear_action f, mappedLinear_action f, mappedLinear_action f,
      automorphism_mul, coeffMap_mul f]
  have hleft (i : Fin 8) (z : Carrier K) :
      mappedLinear f g (mul (basisVector i) z) =
        mul (mappedLinear f g (basisVector i))
          (mappedLinear f g z) := by
    let A : Carrier K →ₗ[K] Carrier K :=
      { toFun := fun w => mappedLinear f g (mul (basisVector i) w)
        map_add' := by intro u v; rw [Atlas.SplitOctonion.mul_add, map_add]
        map_smul' := by intro r u; rw [Atlas.SplitOctonion.mul_smul, map_smul]; rfl }
    let B : Carrier K →ₗ[K] Carrier K :=
      { toFun := fun w => mul (mappedLinear f g (basisVector i))
          (mappedLinear f g w)
        map_add' := by intro u v; rw [map_add, Atlas.SplitOctonion.mul_add]
        map_smul' := by intro r u; rw [map_smul, Atlas.SplitOctonion.mul_smul]; rfl }
    have hAB : A = B := (Pi.basisFun K (Fin 8)).ext (fun j =>
      by simpa [A, B, basisVector, Pi.basisFun_apply] using hpair i j)
    exact DFunLike.congr_fun hAB z
  let A : Carrier K →ₗ[K] Carrier K :=
    { toFun := fun z => mappedLinear f g (mul z y)
      map_add' := by intro u v; rw [Atlas.SplitOctonion.add_mul, map_add]
      map_smul' := by intro r u; rw [Atlas.SplitOctonion.smul_mul, map_smul]; rfl }
  let B : Carrier K →ₗ[K] Carrier K :=
    { toFun := fun z => mul (mappedLinear f g z)
        (mappedLinear f g y)
      map_add' := by intro u v; rw [map_add, Atlas.SplitOctonion.add_mul]
      map_smul' := by intro r u; rw [map_smul, Atlas.SplitOctonion.smul_mul]; rfl }
  have hAB : A = B := (Pi.basisFun K (Fin 8)).ext (fun i =>
    by simpa [A, B, basisVector, Pi.basisFun_apply] using hleft i y)
  exact DFunLike.congr_fun hAB x

private lemma coordinateMatrix_one : coordinateMatrix (1 : Model F) = 1 := by
  apply (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun F (Fin 8))).injective
  simp [coordinateMatrix]
  apply Units.ext
  apply LinearMap.ext
  intro x
  rfl

private lemma coordinateMatrix_mul (g h : Model F) :
    coordinateMatrix (g * h) = coordinateMatrix g * coordinateMatrix h := by
  apply (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun F (Fin 8))).injective
  simp [coordinateMatrix, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul]

private lemma mappedMatrix_one : mappedMatrix f (1 : Model F) = 1 := by
  rw [mappedMatrix, coordinateMatrix_one]
  exact (Matrix.GeneralLinearGroup.map_one _)

private lemma mappedMatrix_mul (g h : Model F) :
    mappedMatrix f (g * h) = mappedMatrix f g * mappedMatrix f h := by
  change Matrix.GeneralLinearGroup.map _ (coordinateMatrix (g * h)) =
    Matrix.GeneralLinearGroup.map _ (coordinateMatrix g) *
      Matrix.GeneralLinearGroup.map _ (coordinateMatrix h)
  rw [coordinateMatrix_mul, Matrix.GeneralLinearGroup.map_mul]

/-- The actual embedding of split-octonion automorphism groups along a field map. -/
def fieldEmbedding : Model F →* Model K where
  toFun g := ⟨mappedLinear f g, mappedLinear_preserves_mul f g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change ((Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 8)))
      (mappedMatrix f (1 : Model F))).toLinearEquiv x = x
    rw [mappedMatrix_one f]
    simp
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change ((Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 8)))
      (mappedMatrix f (g * h))).toLinearEquiv x =
      (((Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 8)))
        (mappedMatrix f g)).toLinearEquiv *
        ((Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 8)))
          (mappedMatrix f h)).toLinearEquiv) x
    rw [mappedMatrix_mul f]
    rw [← LinearMap.GeneralLinearGroup.toLinearEquiv_mul]
    rw [← (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 8))).map_mul]

@[simp] theorem fieldEmbedding_action (g : Model F) (x : Carrier F) :
    (fieldEmbedding f g).val (coeffMap f x) =
      coeffMap f (g.val x) :=
  mappedLinear_action f g x

theorem fieldEmbedding_injective : Function.Injective (fieldEmbedding f) := by
  intro g h e
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hx := congrArg (fun z : Model K => z.val (coeffMap f x)) e
  rw [fieldEmbedding_action f, fieldEmbedding_action f] at hx
  ext i
  apply f.injective
  exact congrFun hx i


@[simp] theorem fieldEmbedding_orderOf (g : Model F) :
    orderOf (fieldEmbedding f g) = orderOf g :=
  orderOf_injective (fieldEmbedding f) (fieldEmbedding_injective f) g

private lemma coordinateMatrix_charpoly (g : Model F) :
    (coordinateMatrix g : Matrix (Fin 8) (Fin 8) F).charpoly = charpoly g := by
  have he : Matrix.toLin' (coordinateMatrix g : Matrix (Fin 8) (Fin 8) F) = action g := by
    apply LinearMap.ext
    intro x
    ext i
    exact congrFun (coordinateMatrix_action g x) i
  rw [← Matrix.charpoly_toLin', he]
  rfl

private lemma mappedLinear_eq_toLin (g : Model F) :
    (mappedLinear f g).toLinearMap =
      Matrix.toLin' (mappedMatrix f g : Matrix (Fin 8) (Fin 8) K) := by
  apply LinearMap.ext
  intro x
  ext i
  have he := congrFun (mappedLinear_apply f g x) i
  simpa [Fintype.linearCombination_apply, Pi.basisFun_apply, Pi.single_apply,
    Matrix.toLin'_apply] using he

@[simp] theorem fieldEmbedding_charpoly (g : Model F) :
    charpoly (fieldEmbedding f g) = (charpoly g).map f := by
  change (mappedLinear f g).toLinearMap.charpoly = _
  rw [mappedLinear_eq_toLin, Matrix.charpoly_toLin']
  change ((coordinateMatrix g : Matrix (Fin 8) (Fin 8) F).map f).charpoly = _
  rw [Matrix.charpoly_map, coordinateMatrix_charpoly]

end
end Atlas.G2.PRegularClasses.FieldExtension
