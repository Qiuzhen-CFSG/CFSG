module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.ActionImage.Candidates
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.ActionImage.CandidateBounds.Contracts

/-!
# Assembly from concrete candidate profiles and the four exceptional bounds

For the 189 ordinary rows, a genuine Frattini-quotient comparison embeds
the actual ambient action image in the finite color stabilizer. The four
remaining rows use their original hypotheses directly.

This is conditional assembly, not the completed candidate calculation:
all three premises below remain independent proof obligations.
Source context: Aschbacher–Smith 1.3.4, printed p.511/PDF p.528.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- All three certificates are required to complete the original candidate action bound. -/
theorem fixedTwoCandidateFrattiniThreePartBound_of_profiles
    (hmodels : ActionImageCandidates.ProfileBounds.Realizations)
    (hfinite : ActionImageCandidates.ProfileBounds.StabilizerBounds)
    (hexceptional : ActionImageCandidates.ProfileBounds.ExceptionalBounds) :
    FixedTwoCandidateFrattiniThreePartBound := by
  intro _ _ _ S hS i hnormal hindex hradical
  by_cases hi : i ∈ ActionImageCandidates.ProfileBounds.exceptional
  · exact hexceptional S hS i hi hnormal hindex hradical
  · obtain ⟨model⟩ := hmodels i hi
    intro hd
    exact hfinite i hi (hd.trans
      (ActionImageCandidates.frattiniAction_card_dvd_colorStabilizer i
        model.coordinates (ActionImageCandidates.ProfileBounds.color i) model.invariant))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

