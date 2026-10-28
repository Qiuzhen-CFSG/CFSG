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
theorem product000 : m001 * m002 = m003 :=
  product_lists l001 l002 l003 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product001 : m002 * m001 = m004 :=
  product_lists l002 l001 l004 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product002 : m002 * m002 = m005 :=
  product_lists l002 l002 l005 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product003 : m003 * m001 = m006 :=
  product_lists l003 l001 l006 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product004 : m003 * m002 = m007 :=
  product_lists l003 l002 l007 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product005 : m004 * m002 = m008 :=
  product_lists l004 l002 l008 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product006 : m005 * m001 = m009 :=
  product_lists l005 l001 l009 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product007 : m006 * m002 = m010 :=
  product_lists l006 l002 l010 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product008 : m007 * m001 = m011 :=
  product_lists l007 l001 l011 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product009 : m008 * m001 = m012 :=
  product_lists l008 l001 l012 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product010 : m008 * m002 = m013 :=
  product_lists l008 l002 l013 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product011 : m009 * m002 = m014 :=
  product_lists l009 l002 l014 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
