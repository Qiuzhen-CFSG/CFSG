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
theorem product084 : m065 * m001 = m066 :=
  product_lists l065 l001 l066 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product085 : m066 * m002 = m067 :=
  product_lists l066 l002 l067 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product086 : m067 * m002 = m068 :=
  product_lists l067 l002 l068 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product087 : m068 * m069 = m000 :=
  product_lists l068 l069 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product088 : m001 * m069 = m070 :=
  product_lists l001 l069 l070 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product089 : m070 * m001 = m071 :=
  product_lists l070 l001 l071 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product090 : m071 * m068 = m072 :=
  product_lists l071 l068 l072 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product091 : m072 * m072 = m073 :=
  product_lists l072 l072 l073 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product092 : m072 * m073 = m074 :=
  product_lists l072 l073 l074 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product093 : m074 * m074 = m075 :=
  product_lists l074 l074 l075 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product094 : m075 * m075 = m000 :=
  product_lists l075 l075 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product095 : m075 * m001 = m076 :=
  product_lists l075 l001 l076 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
