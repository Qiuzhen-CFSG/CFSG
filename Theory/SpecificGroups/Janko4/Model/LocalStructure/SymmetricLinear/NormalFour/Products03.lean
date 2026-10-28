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
theorem product036 : m037 * m038 = m000 :=
  product_lists l037 l038 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product037 : m000 * m029 = m029 :=
  by rw [identity_matrix, one_mul]

set_option maxRecDepth 10000 in
theorem product038 : m000 * m030 = m030 :=
  by rw [identity_matrix, one_mul]

set_option maxRecDepth 10000 in
theorem product039 : m029 * m030 = m039 :=
  product_lists l029 l030 l039 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product040 : m030 * m029 = m040 :=
  product_lists l030 l029 l040 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product041 : m030 * m030 = m041 :=
  product_lists l030 l030 l041 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product042 : m031 * m029 = m034 :=
  product_lists l031 l029 l034 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product043 : m031 * m030 = m042 :=
  product_lists l031 l030 l042 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product044 : m039 * m029 = m043 :=
  product_lists l039 l029 l043 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product045 : m039 * m030 = m044 :=
  product_lists l039 l030 l044 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product046 : m040 * m029 = m045 :=
  product_lists l040 l029 l045 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product047 : m040 * m030 = m046 :=
  product_lists l040 l030 l046 rfl rfl rfl (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
