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
theorem product060 : m045 * m042 = m046 :=
  product_lists l045 l042 l046 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product061 : m046 * m046 = m047 :=
  product_lists l046 l046 l047 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product062 : m046 * m047 = m048 :=
  product_lists l046 l047 l048 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product063 : m047 * m048 = m049 :=
  product_lists l047 l048 l049 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product064 : m048 * m048 = m050 :=
  product_lists l048 l048 l050 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product065 : m049 * m050 = m000 :=
  product_lists l049 l050 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product066 : m042 * m049 = m051 :=
  product_lists l042 l049 l051 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product067 : m051 * m001 = m052 :=
  product_lists l051 l001 l052 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product068 : m001 * m051 = m052 :=
  product_lists l001 l051 l052 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product069 : m042 * m002 = m053 :=
  product_lists l042 l002 l053 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product070 : m053 * m054 = m000 :=
  product_lists l053 l054 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product071 : m001 * m054 = m055 :=
  product_lists l001 l054 l055 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
