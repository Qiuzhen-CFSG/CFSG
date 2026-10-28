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
theorem product072 : m064 * m001 = m075 :=
  product_lists l064 l001 l075 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product073 : m065 * m002 = m076 :=
  product_lists l065 l002 l076 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product074 : m068 * m002 = m077 :=
  product_lists l068 l002 l077 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product075 : m070 * m001 = m078 :=
  product_lists l070 l001 l078 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product076 : m074 * m001 = m079 :=
  product_lists l074 l001 l079 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product077 : m076 * m001 = m080 :=
  product_lists l076 l001 l080 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product078 : m083 * m085 = m086 :=
  product_lists l083 l085 l086 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product079 : m088 * m082 = m087 :=
  product_lists l088 l082 l087 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
