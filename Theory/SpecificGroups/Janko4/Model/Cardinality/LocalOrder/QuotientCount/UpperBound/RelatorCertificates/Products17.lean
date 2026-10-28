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

theorem product_425 : packedMul r110Rows r147Rows = r421Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_426 : packedMul r116Rows r421Rows = r422Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_427 : packedMul r420Rows r422Rows = r423Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_428 : packedMul r116Rows r110Rows = r424Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_429 : packedMul r105Rows r424Rows = r425Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_430 : packedMul r22Rows xRows = r426Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_431 : packedMul r55Rows r426Rows = r427Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_432 : packedMul r425Rows r427Rows = r428Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_433 : packedMul r423Rows r428Rows = r429Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_434 : packedMul r15Rows r69Rows = r430Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_435 : packedMul r49Rows r19Rows = r431Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_436 : packedMul r430Rows r431Rows = r432Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_437 : packedMul r15Rows r62Rows = r433Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_438 : packedMul r8Rows r156Rows = r434Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_439 : packedMul r433Rows r434Rows = r435Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_440 : packedMul r432Rows r435Rows = r436Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_441 : packedMul r24Rows r165Rows = r437Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_442 : packedMul r95Rows r35Rows = r438Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_443 : packedMul r437Rows r438Rows = r439Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_444 : packedMul r134Rows r65Rows = r440Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_445 : packedMul r135Rows r2Rows = r441Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_446 : packedMul r16Rows r441Rows = r442Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_447 : packedMul r440Rows r442Rows = r443Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_448 : packedMul r439Rows r443Rows = r444Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_449 : packedMul r436Rows r444Rows = r445Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
