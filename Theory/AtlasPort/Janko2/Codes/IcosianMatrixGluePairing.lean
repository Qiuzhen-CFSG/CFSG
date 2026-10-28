/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/IcosianMatrixGluePairing.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.IcosianMatrixGlue
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# IcosianMatrixGluePairing

The summed adjugate pairing of two matrix glue words vanishes. Expanding
the two columns into information coordinates reduces the identity to
commutative-ring arithmetic.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/IcosianMatrixGluePairing.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports, public module boundaries, and
proof syntax updated for the local APIs and linters.
-/

@[expose] public section


namespace Atlas.Codes
open scoped BigOperators Matrix

/-- The complete right-matrix glue is isotropic for the adjugate pairing. -/
theorem icosianMatrixGlue_adjugate_pairing {F : Type*} [Field F]
    (x y : IcosianMatrixGlueWord F)
    (hx : x ∈ icosianMatrixGlue F) (hy : y ∈ icosianMatrixGlue F) :
    (∑ i,Matrix.adjugate (x i)*y i)=0 := by
  have xb (i : Fin 3) (j : Fin 2) : x i 1 j=x 0 1 j := by
    have h := (icosianMatrixGlue_constraints x).mp hx j
    fin_cases i
    · rfl
    · exact h.1.symm
    · exact (h.1.trans h.2.1).symm
  have yb (i : Fin 3) (j : Fin 2) : y i 1 j=y 0 1 j := by
    have h := (icosianMatrixGlue_constraints y).mp hy j
    fin_cases i
    · rfl
    · exact h.1.symm
    · exact (h.1.trans h.2.1).symm
  have xt (j : Fin 2) : x 2 0 j= -(x 0 0 j+x 1 0 j) := by
    linear_combination ((icosianMatrixGlue_constraints x).mp hx j).2.2
  have yt (j : Fin 2) : y 2 0 j= -(y 0 0 j+y 1 0 j) := by
    linear_combination ((icosianMatrixGlue_constraints y).mp hy j).2.2
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two,Matrix.vecMul,dotProduct,Fin.sum_univ_succ,xb,yb,xt,yt] <;> ring

end Atlas.Codes
