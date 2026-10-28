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

theorem product_225 : packedMul r219Rows r221Rows = r222Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_226 : packedMul r217Rows r222Rows = r223Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_227 : packedMul r142Rows r142Rows = r224Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_228 : packedMul r142Rows r224Rows = r225Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_229 : packedMul r0Rows r6Rows = r226Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_230 : packedMul r143Rows r90Rows = r227Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_231 : packedMul r226Rows r227Rows = r228Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_232 : packedMul r24Rows r140Rows = r229Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_233 : packedMul r83Rows xRows = r230Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_234 : packedMul r41Rows r230Rows = r231Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_235 : packedMul r229Rows r231Rows = r232Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_236 : packedMul r228Rows r232Rows = r233Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_237 : packedMul r144Rows r59Rows = r234Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_238 : packedMul r91Rows r15Rows = r235Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_239 : packedMul r234Rows r235Rows = r236Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_240 : packedMul r17Rows r97Rows = r237Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_241 : packedMul r15Rows r107Rows = r238Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_242 : packedMul r91Rows r238Rows = r239Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_243 : packedMul r237Rows r239Rows = r240Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_244 : packedMul r236Rows r240Rows = r241Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_245 : packedMul r0Rows r145Rows = r242Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_246 : packedMul r71Rows r28Rows = r243Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_247 : packedMul r108Rows r243Rows = r244Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_248 : packedMul r242Rows r244Rows = r245Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_249 : packedMul r121Rows r108Rows = r246Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
