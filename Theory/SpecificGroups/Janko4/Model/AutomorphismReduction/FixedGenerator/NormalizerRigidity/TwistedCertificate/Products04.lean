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
theorem product048 : m038 * m001 = m051 :=
  product_lists l038 l001 l051 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product049 : m039 * m002 = m052 :=
  product_lists l039 l002 l052 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product050 : m040 * m001 = m053 :=
  product_lists l040 l001 l053 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product051 : m041 * m001 = m054 :=
  product_lists l041 l001 l054 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product052 : m041 * m002 = m055 :=
  product_lists l041 l002 l055 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product053 : m042 * m002 = m056 :=
  product_lists l042 l002 l056 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product054 : m043 * m002 = m057 :=
  product_lists l043 l002 l057 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product055 : m046 * m001 = m058 :=
  product_lists l046 l001 l058 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product056 : m048 * m001 = m059 :=
  product_lists l048 l001 l059 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product057 : m049 * m001 = m060 :=
  product_lists l049 l001 l060 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product058 : m049 * m002 = m061 :=
  product_lists l049 l002 l061 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product059 : m050 * m002 = m062 :=
  product_lists l050 l002 l062 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
