module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreCandidates
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.Containment
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreMaximality
public import Theory.PGroupCore

/-!
# Two-cores of three actual Held centralizers

For rows 1, 3 and 5, the literal core candidate, regarded as a subgroup of the
full ambient centralizer, is its two-core. The checked finite certificates in
`CoreMaximality` prove that this candidate is a normal two-subgroup containing
every normal two-subgroup. Its normality and two-group property give one
inclusion into the two-core; maximality applied to the two-core gives the other.

This discharges the two-core premise of
`e64_centralizer_certificates_of_core_and_span`. The independent intrinsic span
identity and the source condition E assembly remain with that consumer.

Source context: GLS3 Table 5.3p; Aschbacher–Smith, condition E, printed pp.3–4
and 481–482; the literal ATLAS Held words documented in `source/README.md`.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
open Subgroup

/-- The literal candidates are the two-cores of the full ambient centralizers.
All finite certificate inputs are discharged; only the row selection is needed. -/
public theorem coreCandidate_subgroupOf_centralizer_eq_pCore (j : Fin 22)
    (hj : j = 1 ∨ j = 3 ∨ j = 5) :
    (coreCandidate j).subgroupOf (centralizer (ambient j : Set He)) =
      pCore 2 (centralizer (ambient j : Set He)) := by
  obtain ⟨hQ, hN, hmax⟩ := centralizer_coreCandidate_certificates j hj
  exact le_antisymm (le_sSup ⟨hN, hQ⟩) (hmax _ inferInstance pCore_isPGroup)

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
