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
theorem product012 : m013 * m014 = m015 :=
  product_lists l013 l014 l015 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product013 : m015 * m015 = m016 :=
  product_lists l015 l015 l016 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product014 : m005 * m005 = m017 :=
  product_lists l005 l005 l017 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product015 : m004 * m004 = m018 :=
  product_lists l004 l004 l018 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product016 : m005 * m018 = m019 :=
  product_lists l005 l018 l019 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product017 : m017 * m019 = m020 :=
  product_lists l017 l019 l020 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product018 : m016 * m020 = m021 :=
  product_lists l016 l020 l021 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product019 : m021 * m022 = m000 :=
  product_lists l021 l022 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product020 : m022 * m010 = m023 :=
  product_lists l022 l010 l023 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product021 : m010 * m010 = m024 :=
  product_lists l010 l010 l024 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product022 : m023 * m021 = m025 :=
  product_lists l023 l021 l025 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product023 : m011 * m026 = m000 :=
  product_lists l011 l026 l000 rfl rfl rfl (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
