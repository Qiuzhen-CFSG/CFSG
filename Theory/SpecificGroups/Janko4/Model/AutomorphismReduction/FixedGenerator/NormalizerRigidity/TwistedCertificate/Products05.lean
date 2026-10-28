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
theorem product060 : m051 * m002 = m063 :=
  product_lists l051 l002 l063 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product061 : m052 * m002 = m064 :=
  product_lists l052 l002 l064 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product062 : m053 * m002 = m065 :=
  product_lists l053 l002 l065 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product063 : m054 * m002 = m066 :=
  product_lists l054 l002 l066 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product064 : m055 * m001 = m067 :=
  product_lists l055 l001 l067 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product065 : m056 * m001 = m068 :=
  product_lists l056 l001 l068 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product066 : m057 * m002 = m069 :=
  product_lists l057 l002 l069 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product067 : m058 * m002 = m070 :=
  product_lists l058 l002 l070 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product068 : m059 * m002 = m071 :=
  product_lists l059 l002 l071 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product069 : m060 * m002 = m072 :=
  product_lists l060 l002 l072 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product070 : m062 * m001 = m073 :=
  product_lists l062 l001 l073 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product071 : m063 * m002 = m074 :=
  product_lists l063 l002 l074 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
