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

theorem product_700 : packedMul r59Rows r695Rows = r696Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_701 : packedMul r694Rows r696Rows = r697Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_702 : packedMul r62Rows r68Rows = r698Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_703 : packedMul r106Rows r141Rows = r699Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_704 : packedMul r94Rows r699Rows = r700Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_705 : packedMul r698Rows r700Rows = r701Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_706 : packedMul r697Rows r701Rows = r702Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_707 : packedMul r24Rows r18Rows = r703Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_708 : packedMul r7Rows r154Rows = r704Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_709 : packedMul r70Rows r704Rows = r705Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_710 : packedMul r703Rows r705Rows = r706Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_711 : packedMul r8Rows r44Rows = r707Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_712 : packedMul r101Rows r707Rows = r708Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_713 : packedMul r99Rows xRows = r709Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_714 : packedMul r83Rows r709Rows = r710Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_715 : packedMul r708Rows r710Rows = r711Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_716 : packedMul r706Rows r711Rows = r712Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_717 : packedMul r702Rows r712Rows = r713Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_718 : packedMul r40Rows r91Rows = r714Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_719 : packedMul r138Rows r714Rows = r715Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_720 : packedMul r9Rows r95Rows = r716Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_721 : packedMul r44Rows r716Rows = r717Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_722 : packedMul r715Rows r717Rows = r718Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_723 : packedMul r125Rows r183Rows = r719Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_724 : packedMul r133Rows r719Rows = r720Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
