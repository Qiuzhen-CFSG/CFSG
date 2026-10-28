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

theorem product_325 : packedMul yRows r320Rows = r321Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_326 : packedMul r3Rows r129Rows = r322Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_327 : packedMul r2Rows r13Rows = r323Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_328 : packedMul r322Rows r323Rows = r324Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_329 : packedMul r321Rows r324Rows = r325Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_330 : packedMul r5Rows r130Rows = r326Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_331 : packedMul r35Rows r326Rows = r327Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_332 : packedMul r158Rows r2Rows = r328Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_333 : packedMul r62Rows r120Rows = r329Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_334 : packedMul r328Rows r329Rows = r330Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_335 : packedMul r327Rows r330Rows = r331Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_336 : packedMul r325Rows r331Rows = r332Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_337 : packedMul r0Rows r75Rows = r333Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_338 : packedMul r24Rows r97Rows = r334Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_339 : packedMul r159Rows r334Rows = r335Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_340 : packedMul r333Rows r335Rows = r336Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_341 : packedMul r160Rows r131Rows = r337Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_342 : packedMul r34Rows r107Rows = r338Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_343 : packedMul r95Rows r338Rows = r339Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_344 : packedMul r337Rows r339Rows = r340Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_345 : packedMul r336Rows r340Rows = r341Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_346 : packedMul r45Rows r9Rows = r342Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_347 : packedMul r0Rows r342Rows = r343Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_348 : packedMul r108Rows r143Rows = r344Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_349 : packedMul r121Rows r344Rows = r345Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
