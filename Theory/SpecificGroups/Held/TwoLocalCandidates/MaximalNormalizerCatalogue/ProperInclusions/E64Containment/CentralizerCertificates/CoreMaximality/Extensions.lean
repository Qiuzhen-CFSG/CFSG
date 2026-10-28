module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreMaximality.Setup
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreMaximality.Extensions.RowOne
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreMaximality.Extensions.RowThree

/-!
# The two concrete Held order-three extensions

For rows 1 and 3, the literal intersection of the fixed representative with the
ambient centralizer has order 512. An explicit word in the conjugated max5
generators has order three, centralizes the row, normalizes its core candidate,
and does not normalize that intersection. The row modules check the words on
the faithful four-point base and exclude a displaced element using the exhaustive
1024-word representative cover. Two strict subgroup indices then give the order.

These are unconditional finite calculations in the original Held carrier.
They discharge the intersection-order and extension premises of
`centralizer_coreCandidate_certificates_of_bounds_and_extensions`; its full-centralizer bounds remain
separate inputs to the assembly owner.

Source: original ATLAS HeG1-p2058B0/max5 words; GLS3 Table 5.3p and quasithin
condition E. `Extensions/source/` reproduces the discovery data, while all finite
assertions used here are checked by the Lean kernel.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
open Subgroup

/-- Orders of the literal representative intersections for the two extension rows. -/
public theorem centralizerTwoCandidate_card (j : Fin 22) (hj : j = 1 ∨ j = 3) :
    Nat.card (centralizerTwoCandidate j) = 512 := by
  rcases hj with rfl | rfl
  · exact ExtensionCertificates.RowOne.card
  · exact ExtensionCertificates.RowThree.card

/-- Concrete order-three witnesses, with both normalizer conditions in Held. -/
public theorem exists_order_three_extension (j : Fin 22) (hj : j = 1 ∨ j = 3) :
    ∃ t : He, t ∈ centralizer (ambient j : Set He) ∧ orderOf t = 3 ∧
      t ∈ normalizer (coreCandidate j : Set He) ∧
      t ∉ normalizer (centralizerTwoCandidate j : Set He) := by
  rcases hj with rfl | rfl
  · exact ExtensionCertificates.RowOne.extension
  · exact ExtensionCertificates.RowThree.extension

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
