/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechRationalExtension.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechIsometries
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
Unique rational extension of integral Leech automorphisms.
A rational basis obtained from a lattice basis determines the extension and its inverse.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def rationalBasisMatrix : Matrix Omega Omega ℚ :=
  (coordinateBasisMatrix leechBasis).map (Int.castRingHom ℚ)

theorem rationalBasisMatrix_det_ne : rationalBasisMatrix.det ≠ 0 := by
  have h := coordinateBasis_det leechBasis
  have hz : (coordinateBasisMatrix leechBasis).det ≠ 0 := by
    intro hz; rw [hz] at h; norm_num at h
  have hd := (Int.castRingHom ℚ).map_det (coordinateBasisMatrix leechBasis)
  change ((coordinateBasisMatrix leechBasis).det : ℚ) = rationalBasisMatrix.det at hd
  rw [← hd]
  exact_mod_cast hz

def rationalLeechBasis : Module.Basis Omega ℚ RationalCoordinates :=
  (Pi.basisFun ℚ Omega).map
    (Matrix.toLinearEquiv (Pi.basisFun ℚ Omega) rationalBasisMatrix
      (isUnit_iff_ne_zero.mpr rationalBasisMatrix_det_ne))

theorem rationalLeechBasis_apply (i : Omega) :
    rationalLeechBasis i = rationalEmbedding (leechBasis i).val := by
  simp only [rationalLeechBasis,Module.Basis.map_apply,Matrix.toLinearEquiv_apply,
    Matrix.toLin_eq_toLin',Pi.basisFun_apply]
  rw [Matrix.toLin'_apply,Matrix.mulVec_single_one]
  rfl

def extensionMap (f : leech →ₗ[ℤ] leech) : RationalCoordinates →ₗ[ℚ] RationalCoordinates :=
  rationalLeechBasis.constr ℚ (fun i => rationalEmbedding (f (leechBasis i)).val)

theorem extensionMap_basis (f : leech →ₗ[ℤ] leech) (i : Omega) :
    extensionMap f (rationalLeechBasis i) = rationalEmbedding (f (leechBasis i)).val := by
  simp [extensionMap]

theorem extensionMap_agrees (f : leech →ₗ[ℤ] leech) (x : leech) :
    extensionMap f (rationalEmbedding x.val) = rationalEmbedding (f x).val := by
  have he : rationalEmbedding x.val = ∑ i, (leechBasis.repr x i : ℚ) • rationalLeechBasis i := by
    have h := congrArg (fun z : leech => rationalEmbedding z.val) (leechBasis.sum_repr x)
    simp only [rationalLeechBasis_apply]
    ext j
    have hj := congrFun h j
    simp only [rationalEmbedding,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum,
      Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Int.cast_sum,Int.cast_mul] at hj ⊢
    exact hj.symm
  rw [he,map_sum]
  simp only [map_smul,extensionMap_basis]
  have h := congrArg (fun z : leech => rationalEmbedding (f z).val) (leechBasis.sum_repr x)
  ext j
  have hj := congrFun h j
  simp only [map_sum,map_smul,rationalEmbedding,LinearMap.coe_mk,AddHom.coe_mk,
    Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul] at hj ⊢
  exact hj

def rationalExtension (g : leech ≃ₗ[ℤ] leech) : RationalCoordinates ≃ₗ[ℚ] RationalCoordinates where
  __ := extensionMap g.toLinearMap
  invFun := extensionMap g.symm.toLinearMap
  left_inv := by
    have h : (extensionMap g.symm.toLinearMap).comp (extensionMap g.toLinearMap) = LinearMap.id := by
      apply rationalLeechBasis.ext
      intro i
      simp only [LinearMap.comp_apply,extensionMap_basis]
      rw [extensionMap_agrees]
      simp [rationalLeechBasis_apply]
    intro x
    exact congrArg (fun f : RationalCoordinates →ₗ[ℚ] RationalCoordinates => f x) h
  right_inv := by
    have h : (extensionMap g.toLinearMap).comp (extensionMap g.symm.toLinearMap) = LinearMap.id := by
      apply rationalLeechBasis.ext
      intro i
      simp only [LinearMap.comp_apply,extensionMap_basis]
      rw [extensionMap_agrees]
      simp [rationalLeechBasis_apply]
    intro x
    exact congrArg (fun f : RationalCoordinates →ₗ[ℚ] RationalCoordinates => f x) h

theorem rationalExtension_agrees (g : leech ≃ₗ[ℤ] leech) (x : leech) :
    rationalExtension g (rationalEmbedding x.val) = rationalEmbedding (g x).val :=
  extensionMap_agrees g.toLinearMap x

theorem rationalExtension_unique (g : leech ≃ₗ[ℤ] leech)
    (f : RationalCoordinates →ₗ[ℚ] RationalCoordinates)
    (hf : ∀ x : leech, f (rationalEmbedding x.val) = rationalEmbedding (g x).val) :
    f = (rationalExtension g).toLinearMap := by
  apply rationalLeechBasis.ext
  intro i
  rw [rationalLeechBasis_apply,hf]
  exact (rationalExtension_agrees g (leechBasis i)).symm

end Atlas.Lattices
