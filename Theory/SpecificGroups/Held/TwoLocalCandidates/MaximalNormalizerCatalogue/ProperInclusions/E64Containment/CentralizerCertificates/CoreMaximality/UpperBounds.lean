module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreMaximality.UpperBounds.RowOne
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreMaximality.UpperBounds.RowThree
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreMaximality.UpperBounds.RowFive
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup

/-!
# Upper bounds for three actual Held centralizers

All three full centralizers lie in the published row-zero conjugate of max5.
Its proved order is 21504. The kernel-checked row certificates separate 14,
14 and 168 centralizer cosets by their conjugation images of actual listed
generators. Counting these cosets gives the bounds 1536, 1536 and 128.

The row wrappers retain the original representative two-group hypothesis;
the combined theorem discharges it using the existing checked generator series.
The proof uses no Held order, classification, Sylow, candidate normality,
two-core or centralizer-completeness premise. The independent order-three
extension certificates are not needed. The assembly consumer is
`CoreMaximality.centralizer_coreCandidate_certificates_of_bounds_and_extensions`.

Source: GLS3 Table 5.3p; the original ATLAS HeG1-p2058B0 and HeG1-max5W1
words; the literal catalogue rows. See `UpperBounds/source/README.md`.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
open Subgroup LocalPairs.SylowGeometry.Calculations

/-- The full row-one centralizer has order at most 1536. -/
public theorem ambient_one_centralizer_card_le (hp : IsPGroup 2 representative) :
    Nat.card (centralizer (ambient 1 : Set He)) ≤ 1536 :=
  UpperBounds.RowOne.centralizer_card_le hp

/-- The full row-three centralizer has order at most 1536. -/
public theorem ambient_three_centralizer_card_le (hp : IsPGroup 2 representative) :
    Nat.card (centralizer (ambient 3 : Set He)) ≤ 1536 :=
  UpperBounds.RowThree.centralizer_card_le hp

/-- The full row-five centralizer has order at most 128. -/
public theorem ambient_five_centralizer_card_le (hp : IsPGroup 2 representative) :
    Nat.card (centralizer (ambient 5 : Set He)) ≤ 128 :=
  UpperBounds.RowFive.centralizer_card_le hp

/-- The two order-1536 bounds in the exact form used by core maximality. -/
public theorem ambient_centralizer_card_le (hp : IsPGroup 2 representative)
    (j : Fin 22) (hj : j = 1 ∨ j = 3) :
    Nat.card (centralizer (ambient j : Set He)) ≤ 1536 := by
  rcases hj with rfl | rfl
  · exact ambient_one_centralizer_card_le hp
  · exact ambient_three_centralizer_card_le hp

/-- Both finite bound premises of core maximality, with no remaining hypotheses. -/
public theorem ambient_centralizer_card_bounds :
    (∀ j : Fin 22, j = 1 ∨ j = 3 →
      Nat.card (centralizer (ambient j : Set He)) ≤ 1536) ∧
    Nat.card (centralizer (ambient 5 : Set He)) ≤ 128 :=
  ⟨ambient_centralizer_card_le representative_isPGroup,
    ambient_five_centralizer_card_le representative_isPGroup⟩

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
