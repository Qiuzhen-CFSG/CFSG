module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.CorollarySeeds
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.TheoremTwo.ExactTwo
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.TheoremTwo.NoExactTwo

/-!
# The distinguished odd-prime action theorem

If an odd-prime subgroup fixes exactly two points, failure of double
transitivity produces a saturated distinguished seed by Corollary 5.7.
The exact-two argument excludes that seed. In the complementary case,
maximal subgroups have transitive normalizers and distinguished fixed
involutions at every fixed point. Proposition 5.2 is the sole earlier
Section 5 input to these two arguments; it is discharged by SectionFive.

Source: GLS, Volume 4, Chapter 2, Theorem 2 and Lemma 5.8, pp.41–42.
-/

namespace BenderSuzuki.ZD

variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Both clauses of Theorem 2 from Section 3 and Proposition 5.2. -/
public theorem actionTheoremTwo_of_sectionFive_maximalFixes
    (h : MinimalCounterexample Z M) (_r : SimpleReduction Z M)
    (h3 : ActionSectionThree Z M) (hf : ActionPrimeShareMaximalFixes Z M) :
    ActionTheoremTwo Z M := by
  intro p hp hpodd
  refine ⟨?_, sectionFive_normalizer_of_no_exact_two h.disconnected h3 hf hp hpodd⟩
  intro hexact
  by_contra hnot
  obtain ⟨z, hzZ, hzM⟩ := h.disconnected.nonempty
  obtain ⟨Q, hQp, hQM, hzQ, _hQthree, hshare⟩ :=
    actionSaturationSeeds_of_maximalFixes h.disconnected h3 hf z hzZ hzM p hp hpodd hnot
  exact sectionFive_no_exact_two_of_seed h.disconnected h3 hp hpodd hzZ hzM
    hQp hQM hzQ hshare hexact

end BenderSuzuki.ZD
