module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreCandidates
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.Containment
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.SpanIdentities.RowOne.Checks
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.SpanIdentities.RowThree.Checks
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.SpanIdentities.RowFive.Checks

/-!
# Concrete subgroups for the three Held centralizer calculations

Intersect the fixed two-group representative with each actual centralizer.
The published core candidates lie in these intersections, so their two-group
property transports to the literal centralizers. The already checked exhaustive
word enumerations give core-candidate orders 256, 256 and 128.

These conclusions do not assert normality or maximality in the full centralizer.
They supply the finite sizes and containments for `CoreMaximality`; centralizer
upper bounds and order-three word witnesses remain separate obligations.

Source: the original ATLAS words and the enumeration certificates in
`SpanIdentities/*/Checks.lean`; GLS3 Table 5.3p and quasithin condition E.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
open Subgroup LocalPairs.SylowGeometry.Calculations SpanCertificates

@[expose] public def centralizerTwoCandidate (j : Fin 22) : Subgroup He :=
  representative ⊓ centralizer (ambient j : Set He)

public theorem coreCandidate_le_centralizerTwoCandidate (j : Fin 22)
    (hj : j = 1 ∨ j = 3 ∨ j = 5) : coreCandidate j ≤ centralizerTwoCandidate j :=
  le_inf (coreCandidate_le_representative j) (coreCandidate_le_centralizer j hj)

public theorem centralizerTwoCandidate_le_centralizer (j : Fin 22) :
    centralizerTwoCandidate j ≤ centralizer (ambient j : Set He) := inf_le_right

public theorem coreCandidate_isPGroup (hp : IsPGroup 2 representative) (j : Fin 22) :
    IsPGroup 2 (coreCandidate j) := hp.to_le (coreCandidate_le_representative j)

public theorem centralizerTwoCandidate_isPGroup (hp : IsPGroup 2 representative) (j : Fin 22) :
    IsPGroup 2 (centralizerTwoCandidate j) := hp.to_le inf_le_left

public theorem centralizer_coreCandidate_isPGroup (hp : IsPGroup 2 representative) (j : Fin 22) :
    IsPGroup 2 ((coreCandidate j).subgroupOf (centralizer (ambient j : Set He))) :=
  (coreCandidate_isPGroup hp j).comap_subtype

public theorem coreCandidate_one_card : Nat.card (coreCandidate 1) = 256 := by
  rw [coreCandidate_eq_word_closure]
  exact RowOne.enumeration.card

public theorem coreCandidate_three_card : Nat.card (coreCandidate 3) = 256 := by
  rw [coreCandidate_eq_word_closure]
  exact RowThree.enumeration.card

public theorem coreCandidate_five_card : Nat.card (coreCandidate 5) = 128 := by
  rw [coreCandidate_eq_word_closure]
  exact RowFive.enumeration.card

public theorem coreCandidate_card (j : Fin 22) (hj : j = 1 ∨ j = 3) :
    Nat.card (coreCandidate j) = 256 := by
  rcases hj with rfl | rfl
  · exact coreCandidate_one_card
  · exact coreCandidate_three_card
end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
