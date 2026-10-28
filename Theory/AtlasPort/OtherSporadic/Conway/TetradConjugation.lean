/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/TetradConjugation.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.BinaryLift
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Mul
/-!
Explicit sextet and tetrad isometries of the integral Leech lattice.
Coordinate identities and the retained lattice generators certify the isometry operations.

Source: Gerald Höhn, `Atlas/Conway/TetradConjugation.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes

def tetradReflectionMatrix : Matrix Tetrad Tetrad ℚ :=
  !![1/2,-1/2,-1/2,-1/2; -1/2,1/2,-1/2,-1/2;
    -1/2,-1/2,1/2,-1/2; -1/2,-1/2,-1/2,1/2]

theorem four_dimensional_conjugation_identity :
    tetradReflectionMatrix * Matrix.diagonal ![-1,-1,1,1] * tetradReflectionMatrix =
      !![0,1,0,0; 1,0,0,0; 0,0,0,-1; 0,0,-1,0] := by decide +kernel

def tetradSwitch (u : K) : Equiv.Perm Tetrad :=
  if u = 0 then 1 else if u = a then Equiv.swap 0 1 * Equiv.swap 2 3
    else if u = b then Equiv.swap 0 2 * Equiv.swap 1 3
    else Equiv.swap 0 3 * Equiv.swap 1 2

def conjugatedSign (u : K) (k : Tetrad) : ℚ :=
  if u = 0 then 1 else if j u k = 0 then -1 else 1

def tetradDiagonal (u : K) : Matrix Tetrad Tetrad ℚ :=
  Matrix.diagonal (fun k => if j u k = 0 then 1 else -1)

def tetradSwitchMatrix (u : K) : Matrix Tetrad Tetrad ℚ :=
  fun k l => if l = tetradSwitch u k then conjugatedSign u k else 0

theorem tetradSwitch_involutive : ∀ u : K, Function.Involutive (tetradSwitch u) := by
  change ∀ (u : K) (k : Tetrad), tetradSwitch u (tetradSwitch u k) = k
  decide +kernel

theorem tetrad_conjugation_matrix : ∀ u : K,
    tetradReflectionMatrix * tetradDiagonal u * tetradReflectionMatrix = tetradSwitchMatrix u := by
  decide +kernel

theorem tetrad_conjugation_apply (u : K) (x : Tetrad → ℚ) :
    tetradReflectionMatrix.mulVec ((tetradDiagonal u).mulVec (tetradReflectionMatrix.mulVec x)) =
      fun k => conjugatedSign u k * x (tetradSwitch u k) := by
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,tetrad_conjugation_matrix]
  funext k
  simp [Matrix.mulVec,dotProduct,tetradSwitchMatrix,ite_mul]

theorem tetradReflectionMatrix_apply (x : Tetrad → ℚ) (k : Tetrad) :
    tetradReflectionMatrix.mulVec x k = x k - (∑ l, x l)/2 := by
  fin_cases k <;> simp [tetradReflectionMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem tetradReflectionMatrix_relabel (e : Equiv.Perm Tetrad) :
    tetradReflectionMatrix.submatrix e e = tetradReflectionMatrix := by
  have hf : ∀ i j : Tetrad, tetradReflectionMatrix i j = if i = j then (1/2 : ℚ) else -1/2 := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tetradReflectionMatrix]
  ext i j
  simp only [Matrix.submatrix_apply,hf,Equiv.apply_eq_iff_eq]

theorem four_dimensional_conjugation_relabel (e : Equiv.Perm Tetrad) :
    tetradReflectionMatrix * (Matrix.diagonal ![-1,-1,1,1]).submatrix e e * tetradReflectionMatrix =
      (!![0,1,0,0; 1,0,0,0; 0,0,0,-1; 0,0,-1,0] : Matrix Tetrad Tetrad ℚ).submatrix e e := by
  calc
    _ = (tetradReflectionMatrix.submatrix e e * (Matrix.diagonal ![-1,-1,1,1]).submatrix e e) *
        tetradReflectionMatrix.submatrix e e := by rw [tetradReflectionMatrix_relabel]
    _ = (tetradReflectionMatrix * Matrix.diagonal ![-1,-1,1,1] * tetradReflectionMatrix).submatrix e e := by
      rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
    _ = _ := congrArg (fun M : Matrix Tetrad Tetrad ℚ => M.submatrix e e) four_dimensional_conjugation_identity

end Atlas.Conway
