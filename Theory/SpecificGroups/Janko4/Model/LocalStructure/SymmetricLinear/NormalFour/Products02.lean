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
theorem product024 : m026 * m024 = m027 :=
  product_lists l026 l024 l027 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product025 : m027 * m011 = m028 :=
  product_lists l027 l011 l028 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product026 : m028 * m025 = m029 :=
  product_lists l028 l025 l029 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product027 : m025 * m028 = m030 :=
  product_lists l025 l028 l030 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product028 : m029 * m029 = m031 :=
  product_lists l029 l029 l031 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product029 : m031 * m031 = m032 :=
  product_lists l031 l031 l032 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product030 : m032 * m032 = m033 :=
  product_lists l032 l032 l033 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product031 : m029 * m031 = m034 :=
  product_lists l029 l031 l034 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product032 : m031 * m034 = m035 :=
  product_lists l031 l034 l035 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product033 : m032 * m035 = m036 :=
  product_lists l032 l035 l036 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product034 : m033 * m036 = m037 :=
  product_lists l033 l036 l037 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product035 : m036 * m036 = m038 :=
  product_lists l036 l036 l038 rfl rfl rfl (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
