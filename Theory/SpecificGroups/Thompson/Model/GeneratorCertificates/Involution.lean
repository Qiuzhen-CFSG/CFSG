module

public import Theory.SpecificGroups.Thompson.Model.Basic
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix

/-!
# The ATLAS Thompson involution

The packed row product is reduced by the Lean kernel on each of the 248 rows.
Its soundness gives the square relation for `ThG1-f2r248B0.m1`; source data and
attribution are recorded in `Model/source/README.md`.
-/

namespace Thompson

set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
private theorem involution_certificate : ∀ i : Fin 248,
    BinaryMatrix.rowProduct atlasARows[i.val]! atlasARows 248 = 2 ^ i.val := by
  decide +kernel

/-- The published ATLAS matrix `a` is an involution. -/
public theorem atlasA_sq : atlasA ^ 2 = 1 := by
  rw [pow_two]
  exact BinaryMatrix.decode_mul_one 248 atlasARows atlasARows involution_certificate

end Thompson
