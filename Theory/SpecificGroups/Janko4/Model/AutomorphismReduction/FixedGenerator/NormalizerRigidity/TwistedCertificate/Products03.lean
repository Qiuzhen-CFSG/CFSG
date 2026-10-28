module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate.Data

/-!
# Checked products for the local twist polynomial

Source: the actual ATLAS matrices in `Janko4/Model/Data.lean` and the
certified local words in `NormalizerSquares/LocalAction/TwoCoreCentralizer`.
Reproduce with `TwistedCertificate/source/generate_certificate.py`.
All numerical identities are kernel-checked.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
open Janko4.GeneratorCertificates Janko4.Simplicity.Elevens.BridgeCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
theorem product036 : m029 * m001 = m039 :=
  product_lists l029 l001 l039 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product037 : m029 * m002 = m040 :=
  product_lists l029 l002 l040 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product038 : m030 * m002 = m041 :=
  product_lists l030 l002 l041 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product039 : m031 * m002 = m042 :=
  product_lists l031 l002 l042 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product040 : m032 * m001 = m043 :=
  product_lists l032 l001 l043 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product041 : m033 * m001 = m044 :=
  product_lists l033 l001 l044 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product042 : m034 * m001 = m045 :=
  product_lists l034 l001 l045 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product043 : m034 * m002 = m046 :=
  product_lists l034 l002 l046 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product044 : m035 * m001 = m047 :=
  product_lists l035 l001 l047 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product045 : m035 * m002 = m048 :=
  product_lists l035 l002 l048 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product046 : m036 * m002 = m049 :=
  product_lists l036 l002 l049 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product047 : m037 * m002 = m050 :=
  product_lists l037 l002 l050 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
