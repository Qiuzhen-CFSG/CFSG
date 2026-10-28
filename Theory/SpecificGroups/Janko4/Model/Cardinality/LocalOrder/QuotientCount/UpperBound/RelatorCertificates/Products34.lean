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

theorem product_850 : packedMul e5Rows r809Rows = r810Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_851 : packedMul e4Rows r810Rows = r811Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_852 : packedMul e1Rows r811Rows = r623Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_853 : packedMul e5Rows r735Rows = r812Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_854 : packedMul e4Rows r812Rows = r813Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_855 : packedMul e3Rows r813Rows = r814Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_856 : packedMul e2Rows r814Rows = r643Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_857 : packedMul e7Rows e9Rows = r815Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_858 : packedMul e6Rows r815Rows = r816Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_859 : packedMul e3Rows r816Rows = r817Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_860 : packedMul e2Rows r817Rows = r657Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_861 : packedMul e2Rows r782Rows = r672Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_862 : packedMul e2Rows r759Rows = r818Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_863 : packedMul e1Rows r818Rows = r693Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_864 : packedMul e1Rows r787Rows = r713Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_865 : packedMul e6Rows r764Rows = r819Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_866 : packedMul e5Rows r819Rows = r820Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_867 : packedMul e2Rows r820Rows = r821Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_868 : packedMul e1Rows r821Rows = r734Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
