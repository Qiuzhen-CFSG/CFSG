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

theorem product_775 : packedMul e4Rows r759Rows = r760Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_776 : packedMul e3Rows r760Rows = r761Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_777 : packedMul e1Rows r761Rows = r762Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_778 : packedMul e0Rows r762Rows = r286Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_779 : packedMul e9Rows e10Rows = r763Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_780 : packedMul e8Rows r763Rows = r764Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_781 : packedMul e7Rows r764Rows = r765Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_782 : packedMul e5Rows r765Rows = r766Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_783 : packedMul e4Rows r766Rows = r767Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_784 : packedMul e0Rows r767Rows = r304Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_785 : packedMul e5Rows r749Rows = r319Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_786 : packedMul e6Rows r765Rows = r768Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_787 : packedMul e2Rows r768Rows = r769Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_788 : packedMul e1Rows r769Rows = r770Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_789 : packedMul e0Rows r770Rows = r332Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_790 : packedMul e5Rows r745Rows = r771Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_791 : packedMul e4Rows r771Rows = r772Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_792 : packedMul e3Rows r772Rows = r773Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_793 : packedMul e0Rows r773Rows = r341Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_794 : packedMul e6Rows e9Rows = r353Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_795 : packedMul e6Rows r763Rows = r563Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_796 : packedMul e4Rows r563Rows = r774Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_797 : packedMul e3Rows r774Rows = r775Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_798 : packedMul e0Rows r775Rows = r363Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_799 : packedMul e4Rows r764Rows = r776Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
