module

public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Theory.AtlasPort.Algebra.SplitOctonion.BasisChecks
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Field embeddings of symplectic and split-octonion automorphism groups

Extend each linear map by applying the field embedding to its matrix in the
standard octonion basis. Matrix multiplication proves compatibility with
composition and inverses. The integral octonion multiplication table commutes
with coefficient transport, so its 64 basis products prove multiplicativity
of the extended maps. Injectivity is detected on the eight basis vectors.
For symplectic matrices, coefficient transport preserves the standard form.

This supplies genuine embeddings for unequal field orders, in particular the
binary witnesses used for Aschbacher–Smith, proof of 13.8.20(a), printed p.954
(PDF p.971). The concrete multiplication table is the licensed ATLAS port of
Gerald Höhn and the ATLAS contributors; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

namespace Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.FieldEmbeddings
open Atlas.SplitOctonion
variable {K F : Type*} [Field K] [Field F] (φ : K →+* F)

private def coeff (x : Carrier K) : Carrier F := fun i => φ (x i)

private theorem coeff_basis (i : Fin 8) : coeff φ (basisVector i) = basisVector i := by
  ext j
  simp [coeff, basisVector, Pi.single_apply]

private theorem coeff_mul (x y : Carrier K) : coeff φ (mul x y) = mul (coeff φ x) (coeff φ y) := by
  ext i
  fin_cases i <;> simp [coeff, mul]

private noncomputable def extend (g : Carrier K →ₗ[K] Carrier K) : Carrier F →ₗ[F] Carrier F :=
  Matrix.toLin' ((LinearMap.toMatrix' g).map φ)

private theorem extend_coeff (g : Carrier K →ₗ[K] Carrier K) (x : Carrier K) :
    extend φ g (coeff φ x) = coeff φ (g x) := by
  ext i
  simp only [extend, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Matrix.map_apply, coeff, ← map_mul, ← map_sum]
  exact congrArg φ (congrFun (LinearMap.toMatrix'_mulVec g x) i)

private theorem extend_basis (g : Carrier K →ₗ[K] Carrier K) (i : Fin 8) :
    extend φ g (basisVector i) = coeff φ (g (basisVector i)) := by
  rw [← coeff_basis φ i, extend_coeff]

private theorem extend_id : extend φ LinearMap.id = LinearMap.id := by
  apply linearMap_ext
  intro i
  rw [extend_basis]
  exact coeff_basis φ i

private theorem extend_comp (g h : Carrier K →ₗ[K] Carrier K) :
    extend φ (g.comp h) = (extend φ g).comp (extend φ h) := by
  apply LinearMap.toMatrix'.injective
  simp [extend, LinearMap.toMatrix'_comp, Matrix.map_mul]

private noncomputable def extendEquiv (g : Carrier K ≃ₗ[K] Carrier K) : Carrier F ≃ₗ[F] Carrier F where
  toLinearMap := extend φ g.toLinearMap
  invFun := extend φ g.symm.toLinearMap
  left_inv x := by
    have h := extend_comp φ g.symm.toLinearMap g.toLinearMap
    rw [show g.symm.toLinearMap.comp g.toLinearMap = LinearMap.id from
      LinearMap.ext (fun x => g.symm_apply_apply x), extend_id] at h
    exact (LinearMap.congr_fun h x).symm
  right_inv x := by
    have h := extend_comp φ g.toLinearMap g.symm.toLinearMap
    rw [show g.toLinearMap.comp g.symm.toLinearMap = LinearMap.id from
      LinearMap.ext (fun x => g.apply_symm_apply x), extend_id] at h
    exact (LinearMap.congr_fun h x).symm

private noncomputable def extendAut (g : Atlas.G2.Model K) : Atlas.G2.Model F :=
  ⟨extendEquiv φ g.val, by
    apply map_mul_of_basis
    intro i j
    change extend φ g.val.toLinearMap (mul (basisVector i) (basisVector j)) =
      mul (extend φ g.val.toLinearMap (basisVector i)) (extend φ g.val.toLinearMap (basisVector j))
    rw [← coeff_basis φ i, ← coeff_basis φ j, ← coeff_mul, extend_coeff,
      extend_coeff, extend_coeff, ← coeff_mul]
    exact congrArg (coeff φ) (g.property _ _)⟩

/-- Scalar extension of the actual split-octonion automorphism group. -/
public noncomputable def g2 : Atlas.G2.Model K →* Atlas.G2.Model F where
  toFun := extendAut φ
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    exact extend_id φ
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    exact extend_comp φ g.val.toLinearMap h.val.toLinearMap

/-- Field extension is faithful on the full octonion automorphism model. -/
public theorem g2_injective : Function.Injective (g2 φ) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply linearMap_ext
  intro i
  have hh := congrArg (fun a : Atlas.G2.Model F => a.val (basisVector i)) he
  change extend φ g.val.toLinearMap (basisVector i) = extend φ h.val.toLinearMap (basisVector i) at hh
  rw [extend_basis, extend_basis] at hh
  ext j
  exact φ.injective (congrFun hh j)

/-- The extended action agrees with coefficient transport on vectors over
the smaller field. -/
public theorem g2_apply_coeff (g : Atlas.G2.Model K) (x : Carrier K) :
    (g2 φ g).val (fun i => φ (x i)) = fun i => φ (g.val x i) :=
  extend_coeff φ g.val.toLinearMap x

/-- Coefficient extension preserves the standard symplectic form. -/
public noncomputable def symplectic {K F : Type*} [Field K] [Field F] (φ : K →+* F) :
    Matrix.symplecticGroup (Fin 2) K →* Matrix.symplecticGroup (Fin 2) F where
  toFun g := ⟨g.val.map φ, SymplecticGroup.map_mem g.property φ⟩
  map_one' := Subtype.ext (Matrix.map_one φ φ.map_zero φ.map_one)
  map_mul' _ _ := Subtype.ext Matrix.map_mul

/-- Field extension is faithful on the native symplectic matrix group. -/
public theorem symplectic_injective {K F : Type*} [Field K] [Field F] (φ : K →+* F) :
    Function.Injective (symplectic φ) := by
  intro g h he
  apply Subtype.ext
  ext i j
  exact φ.injective (congrArg (fun a : Matrix.symplecticGroup (Fin 2) F => a.val i j) he)

/-- The symplectic embedding is literally entrywise coefficient transport. -/
public theorem symplectic_apply (g : Matrix.symplecticGroup (Fin 2) K) :
    (symplectic φ g).val = g.val.map φ := by rfl

end Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.FieldEmbeddings
