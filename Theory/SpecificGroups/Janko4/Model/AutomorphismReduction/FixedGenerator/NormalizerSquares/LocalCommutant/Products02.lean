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
theorem product024 : m001 * m020 = m021 :=
  product_lists l001 l020 l021 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product025 : m021 * m001 = m022 :=
  product_lists l021 l001 l022 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product026 : m022 * m019 = m023 :=
  product_lists l022 l019 l023 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product027 : m023 * m023 = m024 :=
  product_lists l023 l023 l024 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product028 : m024 * m024 = m025 :=
  product_lists l024 l024 l025 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product029 : m025 * m025 = m000 :=
  product_lists l025 l025 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product030 : m025 * m001 = m026 :=
  product_lists l025 l001 l026 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product031 : m001 * m025 = m026 :=
  product_lists l001 l025 l026 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product032 : m019 * m002 = m027 :=
  product_lists l019 l002 l027 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product033 : m027 * m028 = m000 :=
  product_lists l027 l028 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product034 : m001 * m028 = m029 :=
  product_lists l001 l028 l029 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product035 : m029 * m001 = m030 :=
  product_lists l029 l001 l030 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
