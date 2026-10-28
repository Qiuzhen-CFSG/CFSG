module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.RepresentativeOrders.Base

/-!
# The thirty-first power of the O'Nan representative

Explicit products from the preserved ATLAS matrices (`refs/original/onan/`)
certify the words in `ONG1-cycW1` by kernel reduction. Repeated squaring
assembles the scalar power without evaluating a large nested matrix expression.
-/

namespace ONan.Simplicity.RepresentativeOrderData

set_option maxRecDepth 4096
set_option maxHeartbeats 0

public theorem aux_eq : SimplicityData.ab * w20 = aux := by
  apply Matrix.ext
  unfold SimplicityData.ab w20 aux
  decide +kernel

public theorem thirtyone_eq : aux * PrimeNormalData.d = thirtyone := by
  apply Matrix.ext
  unfold aux PrimeNormalData.d thirtyone
  decide +kernel

/-- The linear lift of the representative labelled 31AB. -/
public theorem matrix_thirtyone :
    ((matrixA * matrixB) * ((matrixA * matrixB) * ((matrixA * matrixB) * matrixB))) *
      ((matrixA * matrixB) * matrixB) = thirtyone := by
  rw [c_eq, d_eq, w20_eq, aux_eq, thirtyone_eq]

public theorem t2_eq : thirtyone * thirtyone = t2 := by
  apply Matrix.ext
  unfold thirtyone t2
  decide +kernel

public theorem t4_eq : t2 * t2 = t4 := by
  apply Matrix.ext
  unfold t2 t4
  decide +kernel

public theorem t8_eq : t4 * t4 = t8 := by
  apply Matrix.ext
  unfold t4 t8
  decide +kernel

public theorem t16_eq : t8 * t8 = t16 := by
  apply Matrix.ext
  unfold t8 t16
  decide +kernel

public theorem t24_eq : t16 * t8 = t24 := by
  apply Matrix.ext
  unfold t16 t8 t24
  decide +kernel

public theorem t28_eq : t24 * t4 = t28 := by
  apply Matrix.ext
  unfold t24 t4 t28
  decide +kernel

public theorem t30_eq : t28 * t2 = t30 := by
  apply Matrix.ext
  unfold t28 t2 t30
  decide +kernel

public theorem t30_mul : t30 * thirtyone = Matrix.scalar (Fin 45) (1 : ZMod 7) := by
  apply Matrix.ext
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
  unfold t30 thirtyone
  decide +kernel

/-- The thirty-first power is the identity on the linear cover. -/
public theorem thirtyone_pow : thirtyone ^ 31 = 1 := by
  have h2 : thirtyone ^ 2 = t2 := (pow_two thirtyone).trans t2_eq
  have h4 : thirtyone ^ 4 = t4 := by
    calc
      thirtyone ^ 4 = thirtyone ^ 2 * thirtyone ^ 2 := pow_add thirtyone 2 2
      _ = t4 := by rw [h2, t4_eq]
  have h8 : thirtyone ^ 8 = t8 := by
    calc
      thirtyone ^ 8 = thirtyone ^ 4 * thirtyone ^ 4 := pow_add thirtyone 4 4
      _ = t8 := by rw [h4, t8_eq]
  have h16 : thirtyone ^ 16 = t16 := by
    calc
      thirtyone ^ 16 = thirtyone ^ 8 * thirtyone ^ 8 := pow_add thirtyone 8 8
      _ = t16 := by rw [h8, t16_eq]
  calc
    thirtyone ^ 31 = (((thirtyone ^ 16 * thirtyone ^ 8) * thirtyone ^ 4) *
      thirtyone ^ 2) * thirtyone := by simp only [← pow_add, ← pow_succ]
    _ = Matrix.scalar (Fin 45) (1 : ZMod 7) := by
      rw [h16, h8, h4, h2, t24_eq, t28_eq, t30_eq, t30_mul]
    _ = 1 := by simp

end ONan.Simplicity.RepresentativeOrderData
