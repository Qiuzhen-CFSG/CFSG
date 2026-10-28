module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Rows
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.FastArithmetic

/-!
# Shared-subword certificates for the local presentation

The words and masks are from `UpperBound.Data` and its adjacent
`source/relator_masks.json`. The generator matrices implement the ATLAS
`J4G1-max1W1` program. Repeated subwords are factored into binary products;
all proposed products are checked by kernel reduction of packed arithmetic.
The external generator supplies witnesses only, never trusted evaluations.
-/

public section
namespace Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
open KernelCount KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem product_200 : packedMul r195Rows r196Rows = r197Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_201 : packedMul r104Rows r11Rows = r198Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_202 : packedMul r104Rows r120Rows = r199Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_203 : packedMul r198Rows r199Rows = r200Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_204 : packedMul r197Rows r200Rows = r201Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_205 : packedMul r1Rows r64Rows = r202Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_206 : packedMul r9Rows r6Rows = r203Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_207 : packedMul r202Rows r203Rows = r204Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_208 : packedMul r121Rows r16Rows = r205Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_209 : packedMul r61Rows r3Rows = r206Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_210 : packedMul r45Rows r206Rows = r207Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_211 : packedMul r205Rows r207Rows = r208Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_212 : packedMul r204Rows r208Rows = r209Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_213 : packedMul r1Rows r122Rows = r210Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_214 : packedMul r122Rows r5Rows = r211Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_215 : packedMul r25Rows r211Rows = r212Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_216 : packedMul r210Rows r212Rows = r213Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_217 : packedMul r139Rows r16Rows = r214Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_218 : packedMul r29Rows r19Rows = r215Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_219 : packedMul r25Rows r215Rows = r216Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_220 : packedMul r214Rows r216Rows = r217Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_221 : packedMul r140Rows r25Rows = r218Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_222 : packedMul r16Rows r218Rows = r219Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_223 : packedMul r31Rows r120Rows = r220Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_224 : packedMul r141Rows r220Rows = r221Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
