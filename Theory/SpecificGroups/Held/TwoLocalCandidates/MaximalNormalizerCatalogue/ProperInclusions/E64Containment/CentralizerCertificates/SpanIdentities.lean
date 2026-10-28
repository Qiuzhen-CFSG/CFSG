module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.SpanIdentities.RowOne
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.SpanIdentities.RowThree
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.SpanIdentities.RowFive

/-!
# The three intrinsic E64 spans in the literal Held candidates

For rows 1, 3, and 5, the elements whose singleton centralizers have index at
most two generate precisely the prescribed containing row. Each proof uses an
injective exhaustive enumeration certified by generator transitions in Held's
literal degree-2058 action. Centralizer counts cover every candidate element;
word witnesses establish both span containments.

Source context: GLS3 Table 5.3p and Aschbacher–Smith condition E, printed
pp.3–4 and 481–482. This unconditional identity supplies the span premise in
`characteristic_of_core_and_span`. The separate ambient two-core identification
is not asserted here.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates

/-- The all-elements centralizer-index criterion recovers the prescribed row
inside each of the three unchanged literal core candidates. -/
public theorem indexTwoSpan_coreCandidate (j : Fin 22) (hj : j = 1 ∨ j = 3 ∨ j = 5) :
    indexTwoSpan (coreCandidate j) = (ambient (container j)).subgroupOf (coreCandidate j) := by
  rcases hj with rfl | rfl | rfl
  · exact SpanCertificates.RowOne.identity
  · exact SpanCertificates.RowThree.identity
  · exact SpanCertificates.RowFive.identity

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
