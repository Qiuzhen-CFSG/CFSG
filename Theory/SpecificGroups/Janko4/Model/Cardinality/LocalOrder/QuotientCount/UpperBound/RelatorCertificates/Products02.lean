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

theorem product_50 : packedMul r9Rows r41Rows = r48Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_51 : packedMul r48Rows r13Rows = r49Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_52 : packedMul r12Rows r1Rows = r50Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_53 : packedMul r19Rows r2Rows = r51Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_54 : packedMul r51Rows r26Rows = r52Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_55 : packedMul r52Rows r21Rows = r53Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_56 : packedMul r53Rows r16Rows = r54Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_57 : packedMul r54Rows r7Rows = r55Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_58 : packedMul r2Rows r14Rows = r56Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_59 : packedMul r32Rows r6Rows = r57Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_60 : packedMul r46Rows r35Rows = r58Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_61 : packedMul r34Rows r49Rows = r59Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_62 : packedMul r56Rows r38Rows = r60Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_63 : packedMul r44Rows r14Rows = r61Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_64 : packedMul r28Rows r1Rows = r62Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_65 : packedMul r29Rows r29Rows = r63Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_66 : packedMul r10Rows r40Rows = r64Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_67 : packedMul r55Rows r24Rows = r65Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_68 : packedMul r16Rows r63Rows = r66Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_69 : packedMul r9Rows r24Rows = r67Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_70 : packedMul r5Rows r47Rows = r68Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_71 : packedMul r10Rows r23Rows = r69Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_72 : packedMul r34Rows r8Rows = r70Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_73 : packedMul r10Rows r43Rows = r71Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_74 : packedMul r26Rows r38Rows = r72Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
