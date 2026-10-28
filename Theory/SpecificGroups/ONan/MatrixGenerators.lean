module

public import Theory.SpecificGroups.ONan.MatrixData
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Invertible ATLAS generators for the O'Nan construction

The displayed inverse matrices are checked entry by entry by kernel reduction.
This produces genuine elements of GL(45,7) from the published ATLAS data,
without a hypothesis about invertibility or the existence of a sporadic group.
See `MatrixData.lean` and `refs/original/onan/README.md` for attribution.
-/

namespace ONan

set_option maxRecDepth 4096
set_option maxHeartbeats 0

public theorem matrixA_mul_self : matrixA * matrixA = 1 := by
  apply Matrix.ext
  simp only [Matrix.one_apply]
  decide +kernel

public theorem matrixB_mul_inv : matrixB * matrixBInv = 1 := by
  apply Matrix.ext
  simp only [Matrix.one_apply]
  decide +kernel

/-- The first standard generator of the linear triple-cover construction. -/
@[expose] public def linearA : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7) where
  val := matrixA
  inv := matrixA
  val_inv := matrixA_mul_self
  inv_val := matrixA_mul_self

/-- The second standard generator of the linear triple-cover construction. -/
@[expose] public def linearB : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7) where
  val := matrixB
  inv := matrixBInv
  val_inv := matrixB_mul_inv
  inv_val := mul_eq_one_comm.mp matrixB_mul_inv

/-- A coordinate that prevents the two products from being scalar multiples. -/
public theorem matrixAB_zero : (matrixA * matrixB) 0 0 = 0 := by decide +kernel

public theorem matrixBA_four : (matrixB * matrixA) 0 0 = 4 := by decide +kernel

end ONan
