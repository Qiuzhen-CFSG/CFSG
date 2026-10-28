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
theorem product036 : m030 * m027 = m031 :=
  product_lists l030 l027 l031 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product037 : m031 * m031 = m032 :=
  product_lists l031 l031 l032 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product038 : m031 * m032 = m033 :=
  product_lists l031 l032 l033 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product039 : m033 * m033 = m034 :=
  product_lists l033 l033 l034 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product040 : m034 * m034 = m000 :=
  product_lists l034 l034 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product041 : m034 * m001 = m035 :=
  product_lists l034 l001 l035 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product042 : m001 * m034 = m035 :=
  product_lists l001 l034 l035 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product043 : m011 * m001 = m036 :=
  product_lists l011 l001 l036 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product044 : m036 * m002 = m037 :=
  product_lists l036 l002 l037 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product045 : m037 * m002 = m038 :=
  product_lists l037 l002 l038 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product046 : m038 * m038 = m000 :=
  product_lists l038 l038 l000 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product047 : m001 * m038 = m014 :=
  product_lists l001 l038 l014 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
