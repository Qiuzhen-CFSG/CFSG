module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Characteristic
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.Containment
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.Intrinsic
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.TwoCoreIdentities
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.SpanIdentities

/-!
# Characteristic E64 subgroups of three Held centralizers

For rows 1, 3, and 5, the prescribed containing rows 21, 20, and 20 lie in,
and are characteristic in, the actual ambient centralizers. The concrete core
candidates are their proved two-cores. Inside each core, the elements with
centralizer index at most two generate exactly the prescribed containing row.
Automorphisms preserve this intrinsic span, and characteristicity is transitive.

The original conditional assembly is preserved. The unconditional certificate
family discharges both finite identities and supplies precisely the centralizer
premise of `e64_containments_of_reconstruction`. Its direct normalizer application
proves the three corresponding containments. Containment in each centralizer is
proved separately, so `subgroupOf` does not silently replace E64 by an intersection.

Source context: GLS3 Table 5.3p; Aschbacher–Smith, condition E, printed pp.3–4
and 481–482; the unchanged ATLAS Held words. No classification or Held order is
assumed. The remaining six normalizer rows and the source condition E assembly
belong to the parent argument.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open Subgroup E64Containment.CentralizerCertificates

/-- The exact family consumed by the E64-containment assembly, conditional on
the actual two-core identifications and the intrinsic finite span calculations. -/
public theorem e64_centralizer_certificates_of_core_and_span
    (hcore : ∀ j : Fin 22, j = 1 ∨ j = 3 ∨ j = 5 →
      (coreCandidate j).subgroupOf (centralizer (ambient j : Set He)) =
        pCore 2 (centralizer (ambient j : Set He)))
    (hspan : ∀ j : Fin 22, j = 1 ∨ j = 3 ∨ j = 5 →
      indexTwoSpan (coreCandidate j) =
        (ambient (container j)).subgroupOf (coreCandidate j)) :
    ∀ j : Fin 22, j = 1 ∨ j = 3 ∨ j = 5 →
      ambient (container j) ≤ centralizer (ambient j : Set He) ∧
        ((ambient (container j)).subgroupOf
          (centralizer (ambient j : Set He))).Characteristic := by
  intro j hj
  refine ⟨ambient_container_le_centralizer j hj, ?_⟩
  exact characteristic_of_core_and_span _ _ _
    (ambient_container_le_coreCandidate j) (coreCandidate_le_centralizer j hj)
    (hcore j hj) (hspan j hj)

/-- The prescribed E64 rows are contained and characteristic in the full ambient
centralizers of rows 1, 3, and 5. Both concrete identity families are discharged. -/
public theorem e64_centralizer_certificates :
    ∀ j : Fin 22, j = 1 ∨ j = 3 ∨ j = 5 →
      ambient (container j) ≤ centralizer (ambient j : Set He) ∧
        ((ambient (container j)).subgroupOf
          (centralizer (ambient j : Set He))).Characteristic :=
  e64_centralizer_certificates_of_core_and_span
    coreCandidate_subgroupOf_centralizer_eq_pCore indexTwoSpan_coreCandidate

/-- The three normalizer containments supplied by the characteristic-centralizer
branch of `e64_containments_of_reconstruction`, with all its premises discharged. -/
public theorem e64_normalizer_containments_from_centralizers
    (j : Fin 22) (hj : j = 1 ∨ j = 3 ∨ j = 5) :
    normalizer (ambient j : Set He) ≤ normalizer (ambient (container j) : Set He) :=
  E64Containment.normalizer_le_of_characteristic_centralizer _ _
    (e64_centralizer_certificates j hj).1 (e64_centralizer_certificates j hj).2

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue
