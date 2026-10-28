module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.Conjugation
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.ActionImage.Candidates

/-!
# Assembly of the large J₄ conjugation-image bound

The small-Frattini-quotient branch follows from the order of GL(d,2) for
d ≤ 5. For the remaining branch, a concrete candidate census and bounds
on those candidates' actual Frattini actions suffice. Passage to the
Frattini action preserves divisibility by 27 because its kernel is a
two-group.

The theorem below is conditional on both outstanding certificates; it is
not the unconditional J₄ calculation. Final assembly must construct both
premises before exporting `fixedTwoLargeConjugationThreePartBound`.
Source context: Aschbacher–Smith 1.3.4, printed p.511/PDF p.528, using
Aschbacher (1986).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- The two independent concrete certificates complete the original action-image contract. -/
theorem fixedTwoLargeConjugationThreePartBound_of_frattiniCandidates
    (hcover : FixedTwoLargeFrattiniCandidateCoverage)
    (hcandidates : FixedTwoCandidateFrattiniThreePartBound) :
    FixedTwoLargeConjugationThreePartBound := by
  intro _ _ _ S hS K hKT hKN hindex hrad
  rcases hcover K hKT hKN hindex with hsmall | ⟨i, rfl⟩
  · exact fixedTwoConjugation_not_dvd_twentySeven_of_smallFrattini hKT hsmall
  · exact (fixedTwoConjugation_not_dvd_twentySeven_iff_frattini hKT).mpr
      (hcandidates S hS i hKN hindex hrad)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
