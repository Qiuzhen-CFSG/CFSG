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
theorem product084 : m058 * m030 = m081 :=
  product_lists l058 l030 l081 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product085 : m059 * m030 = m082 :=
  product_lists l059 l030 l082 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product086 : m060 * m029 = m083 :=
  product_lists l060 l029 l083 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product087 : m060 * m030 = m084 :=
  product_lists l060 l030 l084 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product088 : m061 * m029 = m085 :=
  product_lists l061 l029 l085 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product089 : m061 * m030 = m086 :=
  product_lists l061 l030 l086 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product090 : m035 * m029 = m087 :=
  product_lists l035 l029 l087 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product091 : m035 * m030 = m088 :=
  product_lists l035 l030 l088 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product092 : m062 * m029 = m089 :=
  product_lists l062 l029 l089 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product093 : m062 * m030 = m090 :=
  product_lists l062 l030 l090 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product094 : m063 * m029 = m091 :=
  product_lists l063 l029 l091 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product095 : m064 * m029 = m092 :=
  product_lists l064 l029 l092 rfl rfl rfl (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
