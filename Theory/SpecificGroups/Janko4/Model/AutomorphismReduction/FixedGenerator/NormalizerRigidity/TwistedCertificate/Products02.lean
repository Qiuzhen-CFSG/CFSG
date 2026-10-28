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
theorem product024 : m018 * m002 = m027 :=
  product_lists l018 l002 l027 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product025 : m019 * m002 = m028 :=
  product_lists l019 l002 l028 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product026 : m020 * m002 = m029 :=
  product_lists l020 l002 l029 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product027 : m021 * m001 = m030 :=
  product_lists l021 l001 l030 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product028 : m022 * m001 = m031 :=
  product_lists l022 l001 l031 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product029 : m022 * m002 = m032 :=
  product_lists l022 l002 l032 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product030 : m023 * m002 = m033 :=
  product_lists l023 l002 l033 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product031 : m024 * m002 = m034 :=
  product_lists l024 l002 l034 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product032 : m026 * m002 = m035 :=
  product_lists l026 l002 l035 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product033 : m027 * m001 = m036 :=
  product_lists l027 l001 l036 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product034 : m028 * m001 = m037 :=
  product_lists l028 l001 l037 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product035 : m028 * m002 = m038 :=
  product_lists l028 l002 l038 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
