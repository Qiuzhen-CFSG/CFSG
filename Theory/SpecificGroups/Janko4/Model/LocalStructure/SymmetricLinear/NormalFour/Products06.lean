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
theorem product072 : m052 * m030 = m069 :=
  product_lists l052 l030 l069 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product073 : m053 * m029 = m070 :=
  product_lists l053 l029 l070 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product074 : m053 * m030 = m071 :=
  product_lists l053 l030 l071 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product075 : m054 * m029 = m072 :=
  product_lists l054 l029 l072 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product076 : m054 * m030 = m073 :=
  product_lists l054 l030 l073 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product077 : m055 * m029 = m074 :=
  product_lists l055 l029 l074 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product078 : m055 * m030 = m075 :=
  product_lists l055 l030 l075 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product079 : m056 * m029 = m076 :=
  product_lists l056 l029 l076 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product080 : m056 * m030 = m077 :=
  product_lists l056 l030 l077 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product081 : m057 * m029 = m078 :=
  product_lists l057 l029 l078 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product082 : m057 * m030 = m079 :=
  product_lists l057 l030 l079 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product083 : m058 * m029 = m080 :=
  product_lists l058 l029 l080 rfl rfl rfl (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
