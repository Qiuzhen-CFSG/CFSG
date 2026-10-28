/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechDeterminant.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechIndex
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
The determinant of every Leech Gram matrix is one.
The coordinate-basis determinant computes the lattice index, then scaling the form gives the Gram determinant.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def leechBasis : Module.Basis Omega ℤ leech :=
  (Module.finBasisOfFinrankEq ℤ leech leech_rank).reindex
    (Fintype.equivOfCardEq (by simp [Omega,HexIndex]))

def coordinateBasisMatrix (b : Module.Basis Omega ℤ leech) : Matrix Omega Omega ℤ :=
  fun i j => (b j).val i

def leechGram (b : Module.Basis Omega ℤ leech) : Matrix Omega Omega ℚ :=
  fun i j => rationalForm (rationalEmbedding (b i).val) (rationalEmbedding (b j).val)

theorem coordinateBasis_det (b : Module.Basis Omega ℤ leech) :
    (coordinateBasisMatrix b).det.natAbs = 2^36 := by
  have h := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ Omega) leech.toAddSubgroup b
  rw [leech_index] at h
  rw [Module.Basis.det_apply] at h
  have hm : (Pi.basisFun ℤ Omega).toMatrix (fun i => (b i).val) = coordinateBasisMatrix b := by
    ext i j
    simp [Module.Basis.toMatrix_apply,coordinateBasisMatrix]
  rw [hm] at h
  exact h.symm

theorem leechGram_matrix (b : Module.Basis Omega ℤ leech) :
    leechGram b = (1/8 : ℚ) •
      ((coordinateBasisMatrix b).map (Int.castRingHom ℚ)).transpose *
        ((coordinateBasisMatrix b).map (Int.castRingHom ℚ)) := by
  ext i j
  simp [leechGram,rationalForm_integer,integerDot,Matrix.mul_apply,
    coordinateBasisMatrix,Matrix.map_apply,Matrix.transpose_apply,Finset.sum_mul,div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem leech_gram_determinant (b : Module.Basis Omega ℤ leech) : (leechGram b).det = 1 := by
  rw [leechGram_matrix,Matrix.det_mul,Matrix.det_smul,Matrix.det_transpose]
  have hd : (((coordinateBasisMatrix b).map (Int.castRingHom ℚ)).det) =
      ((coordinateBasisMatrix b).det : ℚ) :=
    ((Int.castRingHom ℚ).map_det (coordinateBasisMatrix b)).symm
  rw [hd]
  have hs := Int.natAbs_sq (coordinateBasisMatrix b).det
  rw [coordinateBasis_det] at hs
  have hs' : (((coordinateBasisMatrix b).det : ℚ))^2 = (2^36 : ℚ)^2 := by
    exact_mod_cast hs.symm
  have hn : Fintype.card Omega = 24 := by simp [Omega,HexIndex]
  rw [hn]
  nlinarith [hs']

end Atlas.Lattices
