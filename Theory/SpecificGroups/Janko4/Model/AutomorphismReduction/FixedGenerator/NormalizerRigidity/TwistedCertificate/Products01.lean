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
theorem product012 : m010 * m001 = m015 :=
  product_lists l010 l001 l015 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product013 : m010 * m002 = m016 :=
  product_lists l010 l002 l016 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product014 : m011 * m002 = m017 :=
  product_lists l011 l002 l017 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product015 : m012 * m002 = m018 :=
  product_lists l012 l002 l018 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product016 : m013 * m001 = m019 :=
  product_lists l013 l001 l019 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product017 : m014 * m001 = m020 :=
  product_lists l014 l001 l020 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product018 : m014 * m002 = m021 :=
  product_lists l014 l002 l021 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product019 : m015 * m002 = m022 :=
  product_lists l015 l002 l022 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product020 : m016 * m001 = m023 :=
  product_lists l016 l001 l023 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product021 : m017 * m001 = m024 :=
  product_lists l017 l001 l024 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product022 : m017 * m002 = m025 :=
  product_lists l017 l002 l025 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product023 : m018 * m001 = m026 :=
  product_lists l018 l001 l026 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
