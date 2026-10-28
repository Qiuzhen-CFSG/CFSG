module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.NormalClosure.ProgramData
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.FastArithmetic

/-!
# Kernel-checked products for the literal max4 program

Adapted, without changing the original, from the saved quotient certificates
in workspace `449b987386c84be8b20675cc86eef10f`. See `source/README.md`.
The sequential checker agrees with ordinary matrix multiplication by the proved
`packed_of_list` and `decode_packedMul` lemmas. The basis inverse identities
are reused from `CharacteristicTwo.Basis` and are not recomputed here.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.NormalClosure.ProgramData.Products
open Janko4.GeneratorCertificates
open Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates

-- The import baseline is 3.2 GiB; serial checks bound the additional live reduction data.
set_option Elab.async false

set_option maxRecDepth 10000 in
theorem product_stage01 : packedMul aRows bRows = product_stage01Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage02Power2 : packedMul product_stage01Rows product_stage01Rows = stage02Power2Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage02Power3 : packedMul stage02Power2Rows product_stage01Rows = stage02Power3Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage03 : packedMul stage02Power3Rows bRows = product_stage03Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage04 : packedMul bRows aRows = product_stage04Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage05 : packedMul product_stage03Rows bRows = product_stage05Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage06Power2 : packedMul product_stage05Rows product_stage05Rows = stage06Power2Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage06Power3 : packedMul stage06Power2Rows product_stage05Rows = stage06Power3Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage07Power2 : packedMul product_stage04Rows product_stage04Rows = stage07Power2Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage07Power4 : packedMul stage07Power2Rows stage07Power2Rows = stage07Power4Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage07Power5 : packedMul stage07Power4Rows product_stage04Rows = stage07Power5Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage07Power10 : packedMul stage07Power5Rows stage07Power5Rows = stage07Power10Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage07Power11 : packedMul stage07Power10Rows product_stage04Rows = stage07Power11Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage07Power22 : packedMul stage07Power11Rows stage07Power11Rows = stage07Power22Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage08Power6 : packedMul stage02Power3Rows stage02Power3Rows = stage08Power6Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage08Power12 : packedMul stage08Power6Rows stage08Power6Rows = stage08Power12Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage08Power13 : packedMul stage08Power12Rows product_stage01Rows = stage08Power13Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage09 : packedMul stage07Power22Rows stage08Power13Rows = product_stage09Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage10 : packedMul product_stage04Rows product_stage04Rows = product_stage10Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage11 : packedMul stage11Rows product_stage09Rows = packedOne :=
  packed_of_list _ _ _ (by
    simp only [packedOne, Vector.toList_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage12 : packedMul stage11Rows stage06Power3Rows = product_stage12Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage13 : packedMul stage06Power3Rows stage06Power3Rows = product_stage13Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage14 : packedMul product_stage12Rows product_stage09Rows = product_stage14Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage15 : packedMul stage15Rows product_stage10Rows = packedOne :=
  packed_of_list _ _ _ (by
    simp only [packedOne, Vector.toList_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage16 : packedMul stage15Rows product_stage13Rows = product_stage16Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage17 : packedMul product_stage16Rows product_stage10Rows = product_stage17Rows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem first_left : packedMul Coordinates.basisRows product_stage17Rows = first_leftRows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem first_conjugate : packedMul first_leftRows Coordinates.basisInverseRows = Coordinates.firstRows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem second_left : packedMul Coordinates.basisRows product_stage14Rows = second_leftRows :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem second_conjugate : packedMul second_leftRows Coordinates.basisInverseRows = Coordinates.secondRows :=
  packed_of_list _ _ _ (by decide +kernel)

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.NormalClosure.ProgramData.Products
