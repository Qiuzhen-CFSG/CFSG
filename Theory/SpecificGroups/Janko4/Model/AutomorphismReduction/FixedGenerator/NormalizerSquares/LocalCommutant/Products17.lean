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
theorem product204 : m083 * m051 = m174 :=
  product_lists l083 l051 l174 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product205 : m083 * m062 = m175 :=
  product_lists l083 l062 l175 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product206 : m084 * m034 = m176 :=
  product_lists l084 l034 l176 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product207 : m084 * m017 = m177 :=
  product_lists l084 l017 l177 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product208 : m084 * m016 = m178 :=
  product_lists l084 l016 l178 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product209 : m179 * m180 = m000 :=
  product_lists l179 l180 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product210 : m180 * m179 = m000 :=
  product_lists l180 l179 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product211 : m181 * m182 = m183 :=
  product_lists l181 l182 l183 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
