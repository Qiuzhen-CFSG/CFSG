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
theorem product060 : m047 * m029 = m058 :=
  product_lists l047 l029 l058 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product061 : m047 * m030 = m059 :=
  product_lists l047 l030 l059 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product062 : m048 * m029 = m060 :=
  product_lists l048 l029 l060 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product063 : m048 * m030 = m061 :=
  product_lists l048 l030 l061 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product064 : m032 * m029 = m035 :=
  product_lists l032 l029 l035 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product065 : m032 * m030 = m062 :=
  product_lists l032 l030 l062 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product066 : m049 * m029 = m063 :=
  product_lists l049 l029 l063 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product067 : m049 * m030 = m064 :=
  product_lists l049 l030 l064 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product068 : m050 * m029 = m065 :=
  product_lists l050 l029 l065 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product069 : m051 * m029 = m066 :=
  product_lists l051 l029 l066 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product070 : m051 * m030 = m067 :=
  product_lists l051 l030 l067 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product071 : m052 * m029 = m068 :=
  product_lists l052 l029 l068 rfl rfl rfl (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
