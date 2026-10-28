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
theorem product096 : m001 * m075 = m076 :=
  product_lists l001 l075 l076 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product097 : m000 * m009 = m009 :=
  by rw [identity_matrix, one_mul]

set_option maxRecDepth 10000 in
theorem product098 : m000 * m016 = m016 :=
  by rw [identity_matrix, one_mul]

set_option maxRecDepth 10000 in
theorem product099 : m000 * m025 = m025 :=
  by rw [identity_matrix, one_mul]

set_option maxRecDepth 10000 in
theorem product100 : m000 * m034 = m034 :=
  by rw [identity_matrix, one_mul]

set_option maxRecDepth 10000 in
theorem product101 : m000 * m017 = m017 :=
  by rw [identity_matrix, one_mul]

set_option maxRecDepth 10000 in
theorem product102 : m000 * m051 = m051 :=
  by rw [identity_matrix, one_mul]

set_option maxRecDepth 10000 in
theorem product103 : m000 * m062 = m062 :=
  by rw [identity_matrix, one_mul]

set_option maxRecDepth 10000 in
theorem product104 : m000 * m075 = m075 :=
  by rw [identity_matrix, one_mul]

set_option maxRecDepth 10000 in
theorem product105 : m009 * m016 = m077 :=
  product_lists l009 l016 l077 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product106 : m009 * m025 = m078 :=
  product_lists l009 l025 l078 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product107 : m009 * m034 = m079 :=
  product_lists l009 l034 l079 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
