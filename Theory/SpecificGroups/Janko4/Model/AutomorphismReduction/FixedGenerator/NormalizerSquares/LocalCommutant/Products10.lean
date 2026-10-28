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
theorem product120 : m025 * m016 = m091 :=
  product_lists l025 l016 l091 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product121 : m025 * m034 = m092 :=
  product_lists l025 l034 l092 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product122 : m025 * m017 = m093 :=
  product_lists l025 l017 l093 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product123 : m025 * m051 = m094 :=
  product_lists l025 l051 l094 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product124 : m025 * m062 = m095 :=
  product_lists l025 l062 l095 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product125 : m025 * m075 = m096 :=
  product_lists l025 l075 l096 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product126 : m034 * m009 = m097 :=
  product_lists l034 l009 l097 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product127 : m034 * m016 = m098 :=
  product_lists l034 l016 l098 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product128 : m034 * m025 = m099 :=
  product_lists l034 l025 l099 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product129 : m034 * m017 = m100 :=
  product_lists l034 l017 l100 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product130 : m034 * m051 = m101 :=
  product_lists l034 l051 l101 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product131 : m034 * m062 = m102 :=
  product_lists l034 l062 l102 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
