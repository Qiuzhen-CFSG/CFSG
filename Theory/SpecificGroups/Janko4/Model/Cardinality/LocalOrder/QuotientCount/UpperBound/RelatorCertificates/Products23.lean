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

theorem product_575 : packedMul r65Rows r7Rows = r571Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_576 : packedMul r570Rows r571Rows = r572Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_577 : packedMul r98Rows r125Rows = r573Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_578 : packedMul r7Rows r153Rows = r574Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_579 : packedMul r150Rows r574Rows = r575Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_580 : packedMul r573Rows r575Rows = r576Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_581 : packedMul r572Rows r576Rows = r577Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_582 : packedMul r569Rows r577Rows = r578Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_583 : packedMul r95Rows r164Rows = r579Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_584 : packedMul r71Rows r579Rows = r580Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_585 : packedMul r94Rows r95Rows = r581Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_586 : packedMul r164Rows r3Rows = r582Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_587 : packedMul r581Rows r582Rows = r583Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_588 : packedMul r580Rows r583Rows = r584Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_589 : packedMul r138Rows r112Rows = r585Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_590 : packedMul r9Rows r71Rows = r586Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_591 : packedMul r2Rows r586Rows = r587Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_592 : packedMul r585Rows r587Rows = r588Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_593 : packedMul r95Rows r59Rows = r589Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_594 : packedMul r75Rows r24Rows = r590Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_595 : packedMul r8Rows r590Rows = r591Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_596 : packedMul r589Rows r591Rows = r592Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_597 : packedMul r588Rows r592Rows = r593Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_598 : packedMul r97Rows r9Rows = r594Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_599 : packedMul r140Rows r99Rows = r595Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
