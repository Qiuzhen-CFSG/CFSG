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
theorem product108 : m009 * m017 = m080 :=
  product_lists l009 l017 l080 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product109 : m009 * m051 = m081 :=
  product_lists l009 l051 l081 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product110 : m009 * m062 = m082 :=
  product_lists l009 l062 l082 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product111 : m009 * m075 = m083 :=
  product_lists l009 l075 l083 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product112 : m016 * m009 = m084 :=
  product_lists l016 l009 l084 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product113 : m016 * m025 = m085 :=
  product_lists l016 l025 l085 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product114 : m016 * m034 = m086 :=
  product_lists l016 l034 l086 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product115 : m016 * m017 = m001 :=
  product_lists l016 l017 l001 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product116 : m016 * m051 = m087 :=
  product_lists l016 l051 l087 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product117 : m016 * m062 = m088 :=
  product_lists l016 l062 l088 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product118 : m016 * m075 = m089 :=
  product_lists l016 l075 l089 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product119 : m025 * m009 = m090 :=
  product_lists l025 l009 l090 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
