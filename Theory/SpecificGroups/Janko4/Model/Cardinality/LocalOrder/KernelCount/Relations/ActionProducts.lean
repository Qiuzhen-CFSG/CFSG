module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.Witnesses

/-!
# ActionProducts for the local kernel

These witnesses implement the ATLAS `J4G1-max1W1` words documented in
`Cardinality.Subgroup` and the conjugates in `KernelCount.BinarySpan`.
Packed products are checked by Lean's kernel; `decode_packedMul` transfers
these certificates to binary matrices. No external computation is trusted.
-/

public section
namespace Janko4.Cardinality.KernelCount.Relations
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem product_x0left : packedMul e0Rows xRows = x0leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x0right : packedMul xRows e1Rows = x0leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x1left : packedMul e1Rows xRows = x1leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x1right : packedMul xRows e0Rows = x1leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x2left : packedMul e2Rows xRows = x2leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x2right : packedMul xRows e3Rows = x2leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x3left : packedMul e3Rows xRows = x3leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x3right : packedMul xRows e2Rows = x3leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x4left : packedMul e4Rows xRows = x4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x4right : packedMul xRows e4Rows = x4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x5left : packedMul e5Rows xRows = x5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x5right : packedMul xRows e6Rows = x5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x6left : packedMul e6Rows xRows = x6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x6right : packedMul xRows e5Rows = x6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x7left : packedMul e7Rows xRows = x7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x7right : packedMul xRows m224_5Rows = x7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x8left : packedMul e8Rows xRows = x8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x8right : packedMul xRows e9Rows = x8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x9left : packedMul e9Rows xRows = x9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x9right : packedMul xRows e8Rows = x9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x10left : packedMul e10Rows xRows = x10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x10right : packedMul xRows m1952_5Rows = x10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y0left : packedMul e0Rows yRows = y0leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y0right : packedMul yRows e2Rows = y0leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y1left : packedMul e1Rows yRows = y1leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y1right : packedMul yRows e0Rows = y1leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y2left : packedMul e2Rows yRows = y2leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y2right : packedMul yRows e1Rows = y2leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y3left : packedMul e3Rows yRows = y3leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y3right : packedMul yRows e4Rows = y3leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y4left : packedMul e4Rows yRows = y4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y4right : packedMul yRows e5Rows = y4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y5left : packedMul e5Rows yRows = y5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y5right : packedMul yRows e3Rows = y5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y6left : packedMul e6Rows yRows = y6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y6right : packedMul yRows e7Rows = y6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y7left : packedMul e7Rows yRows = y7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y7right : packedMul yRows e8Rows = y7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y8left : packedMul e8Rows yRows = y8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y8right : packedMul yRows e6Rows = y8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y9left : packedMul e9Rows yRows = y9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y9right : packedMul yRows e10Rows = y9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y10left : packedMul e10Rows yRows = y10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y10right : packedMul yRows m1991_0Rows = y10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Cardinality.KernelCount.Relations
