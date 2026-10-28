module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.RepresentativeOrders.Base

/-!
# The fifth power of the O'Nan representative

Explicit products from the preserved ATLAS matrices (`refs/original/onan/`)
certify the words in `ONG1-cycW1` by kernel reduction. Repeated squaring
assembles the scalar power without evaluating a large nested matrix expression.
-/

namespace ONan.Simplicity.RepresentativeOrderData

set_option maxRecDepth 4096
set_option maxHeartbeats 0

public theorem w20_sq : w20 * w20 = w20sq := by
  apply Matrix.ext
  unfold w20 w20sq
  decide +kernel

public theorem w20sq_sq : w20sq * w20sq = five := by
  apply Matrix.ext
  unfold w20sq five
  decide +kernel

/-- The linear lift of the representative labelled 5A. -/
public theorem matrix_five :
    ((matrixA * matrixB) * ((matrixA * matrixB) * matrixB)) ^ 4 = five := by
  rw [c_eq, d_eq, w20_eq]
  calc
    w20 ^ 4 = w20 ^ 2 * w20 ^ 2 := pow_add w20 2 2
    _ = five := by rw [pow_two, w20_sq, w20sq_sq]

public theorem five_sq : five * five = five2 := by
  apply Matrix.ext
  unfold five five2
  decide +kernel

public theorem five2_sq : five2 * five2 = five4 := by
  apply Matrix.ext
  unfold five2 five4
  decide +kernel

public theorem five4_mul : five4 * five = Matrix.scalar (Fin 45) (2 : ZMod 7) := by
  apply Matrix.ext
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
  unfold five4 five
  decide +kernel

/-- The fifth power of the linear lift is 2I. -/
public theorem five_pow : five ^ 5 = Matrix.scalar (Fin 45) (2 : ZMod 7) := by
  calc
    five ^ 5 = (five ^ 2 * five ^ 2) * five := by rw [← pow_add, ← pow_succ]
    _ = _ := by rw [pow_two, five_sq, five2_sq, five4_mul]

end ONan.Simplicity.RepresentativeOrderData
