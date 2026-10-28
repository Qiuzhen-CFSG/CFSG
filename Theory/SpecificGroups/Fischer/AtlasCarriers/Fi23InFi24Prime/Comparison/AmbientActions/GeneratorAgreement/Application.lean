module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorAgreement
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions

/-!
# Applying local generator certificates to the literal Fi23 lift words

The generator agreement discharges the signed-evaluation premise in both
existing candidate/label-map applications. The numerical word-action checks
remain independent premises. This extension keeps the core agreement module
below AmbientActions in the import graph, allowing its unconditional
certificate to be imported directly by that consumer. The final two applications
use the complete generator certificates and require only the numerical candidate
checks, whose discharge belongs to the ambient lift-action assembly.

Source: retained ATLAS F24G1-p306936B0.g1/.g2 and GLS3 Table 5.3v, with the
exact candidates in WordSetup and the inverse-left convention in CycleEncoding.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.GeneratorAgreement

/-- Application to the first literal carrier word and the shared label map. -/
theorem candidateA_apply_labelMap_of_local_certificates
    (hsa : SourceCertificate cycleBlocksA cyclesA maskA)
    (hsb : SourceCertificate cycleBlocksB cyclesB maskB)
    (haa : ActionCertificate aMap aInvMap cyclesA maskA)
    (hab : ActionCertificate bMap bInvMap cyclesB maskB)
    (hcheck : ∀ i, candidateAMap (labelMap i) = labelMap (sourceA i)) :
    ∀ i, candidateA.val (labelMap i) = labelMap (sourceA i) :=
  candidateA_apply_labelMap_of_certificates
    (letterMap_correct_of_cycle_certificates hsa hsb haa hab) hcheck

/-- Application to the second literal word, including its exact conjugation. -/
theorem candidateB_apply_labelMap_of_local_certificates
    (hsa : SourceCertificate cycleBlocksA cyclesA maskA)
    (hsb : SourceCertificate cycleBlocksB cyclesB maskB)
    (haa : ActionCertificate aMap aInvMap cyclesA maskA)
    (hab : ActionCertificate bMap bInvMap cyclesB maskB)
    (hcheck : ∀ i, candidateBMap (labelMap i) = labelMap (sourceB i)) :
    ∀ i, candidateB.val (labelMap i) = labelMap (sourceB i) :=
  candidateB_apply_labelMap_of_certificates
    (letterMap_correct_of_cycle_certificates hsa hsb haa hab) hcheck

/-- The unconditional generator comparison discharges the first candidate's
signed-evaluation premise on the literal label map. -/
theorem candidateA_apply_labelMap_of_action_check
    (hcheck : ∀ i, candidateAMap (labelMap i) = labelMap (sourceA i)) :
    ∀ i, candidateA.val (labelMap i) = labelMap (sourceA i) :=
  candidateA_apply_labelMap_of_certificates letterMap_correct hcheck

/-- The same signed-evaluation comparison applies to the exact second candidate,
including its conjugation and sixth power. -/
theorem candidateB_apply_labelMap_of_action_check
    (hcheck : ∀ i, candidateBMap (labelMap i) = labelMap (sourceB i)) :
    ∀ i, candidateB.val (labelMap i) = labelMap (sourceB i) :=
  candidateB_apply_labelMap_of_certificates letterMap_correct hcheck

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.GeneratorAgreement
