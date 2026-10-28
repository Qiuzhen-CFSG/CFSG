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
theorem product048 : m014 * m001 = m039 :=
  product_lists l014 l001 l039 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product049 : m039 * m038 = m015 :=
  product_lists l039 l038 l015 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product050 : m015 * m015 = m040 :=
  product_lists l015 l015 l040 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product051 : m015 * m040 = m000 :=
  product_lists l015 l040 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product052 : m038 * m015 = m017 :=
  product_lists l038 l015 l017 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product053 : m017 * m001 = m016 :=
  product_lists l017 l001 l016 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product054 : m001 * m017 = m016 :=
  product_lists l001 l017 l016 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product055 : m027 * m001 = m041 :=
  product_lists l027 l001 l041 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product056 : m041 * m002 = m042 :=
  product_lists l041 l002 l042 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product057 : m042 * m043 = m000 :=
  product_lists l042 l043 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product058 : m001 * m043 = m044 :=
  product_lists l001 l043 l044 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product059 : m044 * m001 = m045 :=
  product_lists l044 l001 l045 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
