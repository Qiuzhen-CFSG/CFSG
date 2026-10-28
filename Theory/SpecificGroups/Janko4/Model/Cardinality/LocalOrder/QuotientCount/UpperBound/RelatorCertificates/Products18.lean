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

theorem product_450 : packedMul r139Rows r155Rows = r446Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_451 : packedMul r446Rows r237Rows = r447Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_452 : packedMul r80Rows r66Rows = r448Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_453 : packedMul r7Rows r56Rows = r449Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_454 : packedMul r136Rows r449Rows = r450Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_455 : packedMul r448Rows r450Rows = r451Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_456 : packedMul r447Rows r451Rows = r452Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_457 : packedMul r166Rows r31Rows = r453Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_458 : packedMul r166Rows r137Rows = r454Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_459 : packedMul r14Rows r454Rows = r455Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_460 : packedMul r453Rows r455Rows = r456Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_461 : packedMul r10Rows r86Rows = r457Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_462 : packedMul r457Rows r427Rows = r458Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_463 : packedMul r456Rows r458Rows = r459Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_464 : packedMul r452Rows r459Rows = r460Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_465 : packedMul r39Rows r5Rows = r461Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_466 : packedMul r50Rows r461Rows = r462Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_467 : packedMul r195Rows r462Rows = r463Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_468 : packedMul r77Rows r161Rows = r464Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_469 : packedMul r160Rows r328Rows = r465Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_470 : packedMul r464Rows r465Rows = r466Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_471 : packedMul r463Rows r466Rows = r467Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_472 : packedMul r41Rows r59Rows = r468Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_473 : packedMul r20Rows r65Rows = r469Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_474 : packedMul r167Rows r469Rows = r470Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
