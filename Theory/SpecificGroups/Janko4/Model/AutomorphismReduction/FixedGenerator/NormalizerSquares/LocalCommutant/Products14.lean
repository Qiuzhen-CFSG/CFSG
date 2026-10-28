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
theorem product168 : m078 * m034 = m138 :=
  product_lists l078 l034 l138 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product169 : m078 * m017 = m139 :=
  product_lists l078 l017 l139 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product170 : m078 * m051 = m140 :=
  product_lists l078 l051 l140 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product171 : m078 * m062 = m141 :=
  product_lists l078 l062 l141 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product172 : m078 * m075 = m142 :=
  product_lists l078 l075 l142 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product173 : m079 * m009 = m143 :=
  product_lists l079 l009 l143 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product174 : m079 * m016 = m144 :=
  product_lists l079 l016 l144 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product175 : m079 * m025 = m145 :=
  product_lists l079 l025 l145 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product176 : m079 * m017 = m146 :=
  product_lists l079 l017 l146 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product177 : m079 * m051 = m147 :=
  product_lists l079 l051 l147 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product178 : m079 * m062 = m148 :=
  product_lists l079 l062 l148 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product179 : m079 * m075 = m149 :=
  product_lists l079 l075 l149 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
