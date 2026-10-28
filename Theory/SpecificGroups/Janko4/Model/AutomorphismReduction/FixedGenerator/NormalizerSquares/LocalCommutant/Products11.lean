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
theorem product132 : m034 * m075 = m103 :=
  product_lists l034 l075 l103 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product133 : m017 * m009 = m104 :=
  product_lists l017 l009 l104 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product134 : m017 * m025 = m105 :=
  product_lists l017 l025 l105 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product135 : m017 * m034 = m106 :=
  product_lists l017 l034 l106 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product136 : m017 * m051 = m107 :=
  product_lists l017 l051 l107 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product137 : m017 * m062 = m108 :=
  product_lists l017 l062 l108 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product138 : m017 * m075 = m109 :=
  product_lists l017 l075 l109 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product139 : m051 * m009 = m110 :=
  product_lists l051 l009 l110 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product140 : m051 * m025 = m111 :=
  product_lists l051 l025 l111 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product141 : m051 * m034 = m112 :=
  product_lists l051 l034 l112 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product142 : m051 * m062 = m113 :=
  product_lists l051 l062 l113 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product143 : m051 * m075 = m114 :=
  product_lists l051 l075 l114 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
