module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Data

/-!
# Checked products for the J₄ local commutant

List row multiplication is transferred to ordinary matrix multiplication.

Source matrices: `Janko4/Model/Data.lean` (ATLAS J4G1-f2r112B0).
Reproduction: `LocalCommutant/source/generate.py`; candidate data are untrusted.
Every numerical identity below is checked by the Lean kernel.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
open GeneratorCertificates Janko4.Simplicity.Elevens.BridgeCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
theorem product156 : m075 * m017 = m127 :=
  product_lists l075 l017 l127 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product157 : m075 * m051 = m128 :=
  product_lists l075 l051 l128 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product158 : m075 * m062 = m129 :=
  product_lists l075 l062 l129 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product159 : m077 * m009 = m130 :=
  product_lists l077 l009 l130 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product160 : m077 * m025 = m131 :=
  product_lists l077 l025 l131 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product161 : m077 * m034 = m132 :=
  product_lists l077 l034 l132 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product162 : m077 * m017 = m010 :=
  product_lists l077 l017 l010 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product163 : m077 * m051 = m133 :=
  product_lists l077 l051 l133 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product164 : m077 * m062 = m134 :=
  product_lists l077 l062 l134 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product165 : m077 * m075 = m135 :=
  product_lists l077 l075 l135 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product166 : m078 * m009 = m136 :=
  product_lists l078 l009 l136 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product167 : m078 * m016 = m137 :=
  product_lists l078 l016 l137 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
