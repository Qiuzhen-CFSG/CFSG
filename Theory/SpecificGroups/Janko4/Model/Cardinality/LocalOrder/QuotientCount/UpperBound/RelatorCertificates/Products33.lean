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

theorem product_825 : packedMul e1Rows r793Rows = r794Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_826 : packedMul e0Rows r794Rows = r477Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_827 : packedMul e4Rows r768Rows = r795Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_828 : packedMul e2Rows r795Rows = r796Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_829 : packedMul e0Rows r796Rows = r493Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_830 : packedMul e5Rows r757Rows = r512Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_831 : packedMul e5Rows e8Rows = r797Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_832 : packedMul e4Rows r797Rows = r798Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_833 : packedMul e3Rows r798Rows = r799Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_834 : packedMul e2Rows r799Rows = r800Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_835 : packedMul e1Rows r800Rows = r801Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_836 : packedMul e0Rows r801Rows = r527Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_837 : packedMul e3Rows e4Rows = r529Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_838 : packedMul e4Rows r763Rows = r802Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_839 : packedMul e2Rows r802Rows = r548Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_840 : packedMul e4Rows r738Rows = r803Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_841 : packedMul e3Rows r803Rows = r804Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_842 : packedMul e2Rows r804Rows = r805Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_843 : packedMul e1Rows r805Rows = r578Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_844 : packedMul e5Rows e7Rows = r806Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_845 : packedMul e4Rows r806Rows = r807Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_846 : packedMul e2Rows r807Rows = r584Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_847 : packedMul e1Rows r790Rows = r604Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_848 : packedMul e7Rows r763Rows = r808Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_849 : packedMul e6Rows r808Rows = r809Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
