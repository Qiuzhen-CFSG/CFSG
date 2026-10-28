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

theorem product_275 : packedMul r270Rows r271Rows = r272Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_276 : packedMul r269Rows r272Rows = r273Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_277 : packedMul r266Rows r273Rows = r274Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_278 : packedMul r1Rows r149Rows = r275Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_279 : packedMul r68Rows r5Rows = r276Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_280 : packedMul r149Rows r276Rows = r277Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_281 : packedMul r275Rows r277Rows = packedOne :=
  packed_of_list _ _ _ (by
    simp only [packedOne, Vector.toList_ofFn]
    decide +kernel)

theorem product_282 : packedMul r0Rows r82Rows = r278Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_283 : packedMul r151Rows r152Rows = r279Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_284 : packedMul r150Rows r279Rows = r280Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_285 : packedMul r278Rows r280Rows = r281Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_286 : packedMul r17Rows r65Rows = r282Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_287 : packedMul r19Rows r153Rows = r283Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_288 : packedMul r151Rows r283Rows = r284Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_289 : packedMul r282Rows r284Rows = r285Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_290 : packedMul r281Rows r285Rows = r286Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_291 : packedMul r0Rows r5Rows = r287Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_292 : packedMul r78Rows r25Rows = r288Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_293 : packedMul r92Rows r288Rows = r289Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_294 : packedMul r287Rows r289Rows = r290Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_295 : packedMul r14Rows r93Rows = r291Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_296 : packedMul r9Rows r2Rows = r292Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_297 : packedMul r66Rows r292Rows = r293Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_298 : packedMul r291Rows r293Rows = r294Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_299 : packedMul r290Rows r294Rows = r295Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
