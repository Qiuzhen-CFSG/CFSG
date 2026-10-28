module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorAgreement.ActionCertificates.CyclesA
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorAgreement.ActionCertificates.CyclesB
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorAgreement.ActionCertificates.FixedA
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorAgreement.ActionCertificates.FixedB

/-!
# Complete local signed actions of the packed Fi24' generators

All 593 A blocks and 400 B blocks are checked in both directions against
the exact packed maps. A balanced exhaustive check proves A fixation
outside its mask; B's mask has no complement. These are unconditional
numerical certificates, independent of source decoding and disjointness.

The inverse-left convention checks aMap/bMap against inverse cycles and
aInvMap/bInvMap against forward cycles. The assembly consumer is the
signed_maps_correct theorem in Checker, specialized in GeneratorAgreement.

Source: retained ATLAS F24G1-p306936B0.g1/.g2, with attribution in
AtlasCarriers/source/. Reproduce with ActionCertificates/source/generate.py.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.GeneratorAgreement

open ActionChecks

theorem actionsA_certificate : ActionCertificate aMap aInvMap cyclesA maskA where
  inverseCycles := blockTests_sound aMap false partsA allA_inverse
  forwardCycles := blockTests_sound aInvMap true partsA allA_forward
  fixed := fixedA

theorem actionsB_certificate : ActionCertificate bMap bInvMap cyclesB maskB where
  inverseCycles := blockTests_sound bMap false partsB allB_inverse
  forwardCycles := blockTests_sound bInvMap true partsB allB_forward
  fixed := fixedB

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.GeneratorAgreement
