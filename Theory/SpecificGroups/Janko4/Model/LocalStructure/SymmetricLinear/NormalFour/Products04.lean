module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Data

/-!
# Checked products for the max4 obstruction

Source: ATLAS `J4G1-f2r112B0` and `J4G1-max4W1`, as attributed in
`Model/Data.lean` and `SymmetricLinear/Model.lean`. Reproduce using
`NormalFour/source/generate.py`. All numerical equalities are kernel checked.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
open GeneratorCertificates Simplicity.Elevens.BridgeCertificate Matrix

set_option maxRecDepth 10000 in
theorem product048 : m041 * m029 = m047 :=
  product_lists l041 l029 l047 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product049 : m041 * m030 = m048 :=
  product_lists l041 l030 l048 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product050 : m034 * m029 = m032 :=
  product_lists l034 l029 l032 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product051 : m034 * m030 = m049 :=
  product_lists l034 l030 l049 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product052 : m042 * m029 = m050 :=
  product_lists l042 l029 l050 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product053 : m042 * m030 = m051 :=
  product_lists l042 l030 l051 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product054 : m043 * m029 = m052 :=
  product_lists l043 l029 l052 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product055 : m044 * m029 = m053 :=
  product_lists l044 l029 l053 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product056 : m044 * m030 = m054 :=
  product_lists l044 l030 l054 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product057 : m045 * m029 = m055 :=
  product_lists l045 l029 l055 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product058 : m045 * m030 = m056 :=
  product_lists l045 l030 l056 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product059 : m046 * m030 = m057 :=
  product_lists l046 l030 l057 rfl rfl rfl (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
