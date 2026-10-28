module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.Witnesses

/-!
# WordProducts for the local kernel

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

theorem product_b3 : packedMul b2Rows bRows = b3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_ab : packedMul aRows bRows = abRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_abb : packedMul abRows bRows = abbRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w5 : packedMul abRows abbRows = w5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w6 : packedMul abRows w5Rows = w6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w2 : packedMul w6Rows w6Rows = w2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w4 : packedMul w2Rows w2Rows = w4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w8 : packedMul w4Rows w4Rows = w8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_abbb : packedMul abbRows bRows = abbbRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_iabbb : packedMul bRows aRows = iabbbRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_iab : packedMul b3Rows aRows = iabRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_ab_inverse : packedMul abRows iabRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_abbb_inverse : packedMul abbbRows iabbbRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_xl : packedMul iabRows aRows = xlRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x : packedMul xlRows abRows = xRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_yl : packedMul iabbbRows w8Rows = ylRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y : packedMul ylRows abbbRows = yRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_xy : packedMul xRows yRows = xyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_xy2 : packedMul xyRows xyRows = xy2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_xy4 : packedMul xy2Rows xy2Rows = xy4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_xy8 : packedMul xy4Rows xy4Rows = xy8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_xy12 : packedMul xy8Rows xy4Rows = xy12Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_seed : packedMul xy12Rows xy2Rows = e0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Cardinality.KernelCount.Relations
