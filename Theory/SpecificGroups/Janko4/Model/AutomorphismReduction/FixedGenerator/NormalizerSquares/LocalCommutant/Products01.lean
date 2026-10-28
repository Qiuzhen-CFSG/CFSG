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
theorem product012 : m011 * m011 = m000 :=
  product_lists l011 l011 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product013 : m001 * m011 = m012 :=
  product_lists l001 l011 l012 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product014 : m012 * m001 = m013 :=
  product_lists l012 l001 l013 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product015 : m013 * m011 = m014 :=
  product_lists l013 l011 l014 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product016 : m014 * m014 = m015 :=
  product_lists l014 l014 l015 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product017 : m014 * m015 = m016 :=
  product_lists l014 l015 l016 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product018 : m016 * m016 = m000 :=
  product_lists l016 l016 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product019 : m016 * m001 = m017 :=
  product_lists l016 l001 l017 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product020 : m001 * m016 = m017 :=
  product_lists l001 l016 l017 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product021 : m002 * m001 = m018 :=
  product_lists l002 l001 l018 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product022 : m018 * m002 = m019 :=
  product_lists l018 l002 l019 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product023 : m019 * m020 = m000 :=
  product_lists l019 l020 l000 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
