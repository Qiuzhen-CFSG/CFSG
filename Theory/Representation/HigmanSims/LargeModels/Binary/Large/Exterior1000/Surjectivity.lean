module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Data
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Matrix.Basic
/-!
# Surjectivity from the source pivot minor

A checked right inverse of a selected square column minor gives a preimage
under the full row matrix: multiply by the inverse, then put the resulting
coordinates in the selected ambient columns. This supplies the exact
surjectivity premise of invariant-row descent for the degree-1000 HS action.
The numerical inverse identity remains explicit until its certificate is built.

Source: the pivot columns and inverse in `Binary/source/section1000.json`,
with ATLAS attribution retained in `Binary/source/README.md`.
-/

@[expose] public section
open scoped BigOperators
namespace Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000

/-- A right inverse of a column minor supplies a right inverse on vectors, even
without a separate injectivity proof for the selected column map. -/
theorem surjective_of_minor_inverse {m n : ℕ}
    (V : Matrix (Fin n) (Fin m) (ZMod 2)) (p : Fin n → Fin m)
    (R : Matrix (Fin n) (Fin n) (ZMod 2)) (h : V.submatrix id p * R = 1) :
    Function.Surjective V.mulVecLin := by
  have lift (z : Fin n → ZMod 2) :
      V.mulVec (∑ j : Fin n, z j • Pi.single (p j) 1) = (V.submatrix id p).mulVec z := by
    rw [Matrix.mulVec_sum]
    funext i
    simp [Matrix.mulVec_smul, Matrix.mulVec_single, Matrix.mulVec,
      dotProduct, Matrix.submatrix, mul_comm]
  intro y
  refine ⟨∑ j : Fin n, (R.mulVec y) j • Pi.single (p j) 1, ?_⟩
  change V.mulVec _ = y
  rw [lift, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

/-- Apply the selected-column construction to the literal degree-1000 rows. -/
theorem surjective_of_pivot_certificate (h : pivotMinor * pivotInverse = 1) :
    Function.Surjective U.mulVecLin :=
  surjective_of_minor_inverse U pivotColumn pivotInverse h

end Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000
