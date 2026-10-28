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
theorem product108 : m070 * m030 = m105 :=
  product_lists l070 l030 l105 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product109 : m071 * m030 = m106 :=
  product_lists l071 l030 l106 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product110 : m072 * m029 = m107 :=
  product_lists l072 l029 l107 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product111 : m072 * m030 = m108 :=
  product_lists l072 l030 l108 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product112 : m073 * m029 = m109 :=
  product_lists l073 l029 l109 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product113 : m073 * m030 = m110 :=
  product_lists l073 l030 l110 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product114 : m074 * m029 = m111 :=
  product_lists l074 l029 l111 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product115 : m074 * m030 = m112 :=
  product_lists l074 l030 l112 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product116 : m075 * m029 = m113 :=
  product_lists l075 l029 l113 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product117 : m075 * m030 = m114 :=
  product_lists l075 l030 l114 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product118 : m076 * m029 = m115 :=
  product_lists l076 l029 l115 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product119 : m077 * m029 = m116 :=
  product_lists l077 l029 l116 rfl rfl rfl (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
