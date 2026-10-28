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

theorem product_750 : packedMul e2Rows r743Rows = r744Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_751 : packedMul e1Rows r744Rows = r209Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_752 : packedMul e7Rows r735Rows = r745Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_753 : packedMul e6Rows r745Rows = r746Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_754 : packedMul e3Rows r746Rows = r747Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_755 : packedMul e2Rows r747Rows = r748Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_756 : packedMul e0Rows r748Rows = r213Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_757 : packedMul e7Rows e10Rows = r749Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_758 : packedMul e3Rows r749Rows = r750Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_759 : packedMul e2Rows r750Rows = r751Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_760 : packedMul e1Rows r751Rows = r223Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_761 : packedMul e4Rows r737Rows = r225Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_762 : packedMul e2Rows r738Rows = r752Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_763 : packedMul e0Rows r752Rows = r233Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_764 : packedMul e4Rows r735Rows = r753Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_765 : packedMul e2Rows r753Rows = r754Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_766 : packedMul e0Rows r754Rows = r241Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_767 : packedMul e5Rows r736Rows = r755Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_768 : packedMul e3Rows r755Rows = r756Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_769 : packedMul e2Rows r756Rows = r251Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_770 : packedMul e1Rows r749Rows = r260Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_771 : packedMul e6Rows e10Rows = r757Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_772 : packedMul e4Rows r757Rows = r758Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_773 : packedMul e0Rows r758Rows = r274Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_774 : packedMul e7Rows e8Rows = r759Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
