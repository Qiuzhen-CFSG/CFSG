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
theorem product072 : m055 * m001 = m056 :=
  product_lists l055 l001 l056 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product073 : m056 * m053 = m057 :=
  product_lists l056 l053 l057 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product074 : m057 * m057 = m058 :=
  product_lists l057 l057 l058 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product075 : m057 * m058 = m059 :=
  product_lists l057 l058 l059 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product076 : m058 * m059 = m060 :=
  product_lists l058 l059 l060 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product077 : m059 * m059 = m061 :=
  product_lists l059 l059 l061 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product078 : m060 * m061 = m000 :=
  product_lists l060 l061 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product079 : m053 * m060 = m062 :=
  product_lists l053 l060 l062 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product080 : m062 * m001 = m063 :=
  product_lists l062 l001 l063 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product081 : m001 * m062 = m063 :=
  product_lists l001 l062 l063 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product082 : m019 * m001 = m064 :=
  product_lists l019 l001 l064 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product083 : m064 * m002 = m065 :=
  product_lists l064 l002 l065 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
