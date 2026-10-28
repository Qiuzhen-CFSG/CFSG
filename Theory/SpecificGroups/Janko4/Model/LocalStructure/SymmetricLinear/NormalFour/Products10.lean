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
theorem product120 : m077 * m030 = m117 :=
  product_lists l077 l030 l117 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product121 : m078 * m029 = m118 :=
  product_lists l078 l029 l118 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product122 : m078 * m030 = m119 :=
  product_lists l078 l030 l119 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product123 : m079 * m029 = m120 :=
  product_lists l079 l029 l120 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product124 : m079 * m030 = m121 :=
  product_lists l079 l030 l121 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product125 : m080 * m029 = m122 :=
  product_lists l080 l029 l122 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product126 : m080 * m030 = m123 :=
  product_lists l080 l030 l123 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product127 : m081 * m029 = m124 :=
  product_lists l081 l029 l124 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product128 : m081 * m030 = m125 :=
  product_lists l081 l030 l125 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product129 : m082 * m029 = m126 :=
  product_lists l082 l029 l126 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product130 : m082 * m030 = m127 :=
  product_lists l082 l030 l127 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product131 : m083 * m029 = m128 :=
  product_lists l083 l029 l128 rfl rfl rfl (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
