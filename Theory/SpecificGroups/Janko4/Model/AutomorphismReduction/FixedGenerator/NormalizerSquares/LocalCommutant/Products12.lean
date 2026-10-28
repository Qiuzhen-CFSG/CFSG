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
theorem product144 : m062 * m009 = m115 :=
  product_lists l062 l009 l115 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product145 : m062 * m016 = m116 :=
  product_lists l062 l016 l116 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product146 : m062 * m025 = m117 :=
  product_lists l062 l025 l117 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product147 : m062 * m034 = m118 :=
  product_lists l062 l034 l118 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product148 : m062 * m017 = m119 :=
  product_lists l062 l017 l119 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product149 : m062 * m051 = m120 :=
  product_lists l062 l051 l120 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product150 : m062 * m062 = m121 :=
  product_lists l062 l062 l121 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product151 : m062 * m075 = m122 :=
  product_lists l062 l075 l122 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product152 : m075 * m009 = m123 :=
  product_lists l075 l009 l123 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product153 : m075 * m016 = m124 :=
  product_lists l075 l016 l124 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product154 : m075 * m025 = m125 :=
  product_lists l075 l025 l125 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product155 : m075 * m034 = m126 :=
  product_lists l075 l034 l126 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
