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
theorem product132 : m083 * m030 = m129 :=
  product_lists l083 l030 l129 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product133 : m084 * m030 = m130 :=
  product_lists l084 l030 l130 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product134 : m085 * m029 = m131 :=
  product_lists l085 l029 l131 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product135 : m085 * m030 = m132 :=
  product_lists l085 l030 l132 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product136 : m086 * m029 = m133 :=
  product_lists l086 l029 l133 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product137 : m086 * m030 = m134 :=
  product_lists l086 l030 l134 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product138 : m087 * m029 = m135 :=
  product_lists l087 l029 l135 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product139 : m087 * m030 = m136 :=
  product_lists l087 l030 l136 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product140 : m088 * m029 = m137 :=
  product_lists l088 l029 l137 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product141 : m088 * m030 = m138 :=
  product_lists l088 l030 l138 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product142 : m089 * m029 = m139 :=
  product_lists l089 l029 l139 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product143 : m090 * m029 = m140 :=
  product_lists l090 l029 l140 rfl rfl rfl (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
