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
theorem product144 : m090 * m030 = m141 :=
  product_lists l090 l030 l141 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product145 : m091 * m030 = m142 :=
  product_lists l091 l030 l142 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product146 : m092 * m030 = m143 :=
  product_lists l092 l030 l143 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product147 : m131 * m030 = m144 :=
  product_lists l131 l030 l144 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product148 : m146 * m145 = m000 :=
  product_lists l146 l145 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product149 : m147 * m148 = m149 :=
  product_lists l147 l148 l149 rfl rfl rfl (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
