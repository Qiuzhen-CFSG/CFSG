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
theorem product096 : m064 * m030 = m093 :=
  product_lists l064 l030 l093 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product097 : m065 * m029 = m094 :=
  product_lists l065 l029 l094 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product098 : m065 * m030 = m095 :=
  product_lists l065 l030 l095 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product099 : m066 * m029 = m096 :=
  product_lists l066 l029 l096 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product100 : m066 * m030 = m097 :=
  product_lists l066 l030 l097 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product101 : m067 * m029 = m098 :=
  product_lists l067 l029 l098 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product102 : m067 * m030 = m099 :=
  product_lists l067 l030 l099 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product103 : m068 * m029 = m100 :=
  product_lists l068 l029 l100 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product104 : m068 * m030 = m101 :=
  product_lists l068 l030 l101 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product105 : m069 * m029 = m102 :=
  product_lists l069 l029 l102 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product106 : m069 * m030 = m103 :=
  product_lists l069 l030 l103 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product107 : m070 * m029 = m104 :=
  product_lists l070 l029 l104 rfl rfl rfl (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
