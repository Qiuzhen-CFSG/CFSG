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

theorem product_800 : packedMul e0Rows r776Rows = r380Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_801 : packedMul e4Rows e8Rows = r391Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_802 : packedMul e5Rows e9Rows = r777Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_803 : packedMul e4Rows r777Rows = r778Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_804 : packedMul e3Rows r778Rows = r779Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_805 : packedMul e2Rows r779Rows = r780Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_806 : packedMul e0Rows r780Rows = r396Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_807 : packedMul e6Rows r737Rows = r781Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_808 : packedMul e5Rows r781Rows = r782Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_809 : packedMul e4Rows r782Rows = r783Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_810 : packedMul e3Rows r783Rows = r784Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_811 : packedMul e1Rows r784Rows = r785Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_812 : packedMul e0Rows r785Rows = r408Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_813 : packedMul e5Rows r563Rows = r786Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_814 : packedMul e3Rows r786Rows = r787Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_815 : packedMul e2Rows r787Rows = r788Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_816 : packedMul e1Rows r788Rows = r789Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_817 : packedMul e0Rows r789Rows = r419Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_818 : packedMul e6Rows r759Rows = r790Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_819 : packedMul e3Rows r790Rows = r429Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_820 : packedMul e5Rows r737Rows = r791Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_821 : packedMul e3Rows r791Rows = r792Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_822 : packedMul e0Rows r792Rows = r445Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_823 : packedMul e2Rows r742Rows = r460Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_824 : packedMul e2Rows r775Rows = r793Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
