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
theorem product000 : m000 * m002 = m002 :=
  by rw [identity_matrix, one_mul]

set_option maxRecDepth 10000 in
theorem product001 : m002 * m003 = m000 :=
  product_lists l002 l003 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product002 : m001 * m003 = m004 :=
  product_lists l001 l003 l004 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product003 : m004 * m001 = m005 :=
  product_lists l004 l001 l005 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product004 : m005 * m002 = m006 :=
  product_lists l005 l002 l006 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product005 : m006 * m006 = m007 :=
  product_lists l006 l006 l007 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product006 : m006 * m007 = m008 :=
  product_lists l006 l007 l008 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product007 : m007 * m008 = m009 :=
  product_lists l007 l008 l009 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product008 : m009 * m009 = m000 :=
  product_lists l009 l009 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product009 : m009 * m001 = m010 :=
  product_lists l009 l001 l010 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product010 : m001 * m009 = m010 :=
  product_lists l001 l009 l010 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product011 : m002 * m002 = m011 :=
  product_lists l002 l002 l011 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
