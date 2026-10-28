module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.ActionImage.Candidates
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.ActionImage.CandidateCoverage.Census
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.ActionImage.CandidateCoverage.Collection

/-!
# Reduction of J₄ candidate coverage to finite certificates

The full 788-row family starts at the specified two-subgroup. Normal index-two
steps cover every normal subgroup of index at most 32. Partitioning the reached
rows then leaves either one of the 193 existing candidates or a row whose
Frattini quotient still requires an order bound of 32.

The assembly here remains conditional. Concrete collection relations, the
normal-step census and the 595 small-row bounds are separate proof obligations;
no GAP census or rank report is used as a theorem. The unconditional coverage
contract must only be exported once these obligations have been discharged.

Source context: Aschbacher–Smith 1.3.4, printed p.511/PDF p.528, citing Asc86b.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
open ActionImageCandidates.Coverage

/-- Normal-step and small-Frattini certificates suffice for the exact contract. -/
theorem fixedTwoLargeFrattiniCandidateCoverage_of_normalSteps_of_smallRows
    (hstep : NormalSteps) (hsmall : SmallRows) :
    FixedTwoLargeFrattiniCandidateCoverage := by
  intro K hKT hKN hindex
  obtain ⟨r, hr⟩ := ambient_coverage_of_steps hstep K hKT hKN hindex
  have hs := rowClass_spec r
  cases hc : rowClass r with
  | inl j =>
    have hj : smallRow j = r := by simpa only [hc, Sum.elim_inl] using hs
    left
    rw [← hr, ← hj]
    exact hsmall j
  | inr i =>
    have hi : candidateRow i = r := by simpa only [hc, Sum.elim_inr] using hs
    right
    exact ⟨i, (candidate_node i).symm.trans ((congrArg ambientNode hi).trans hr)⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
