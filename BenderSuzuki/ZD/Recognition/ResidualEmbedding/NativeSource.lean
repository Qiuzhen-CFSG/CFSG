module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.NativeSource
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NativeSource.Completion

/-!
# The complete residual strong-embedding argument

The original minimal simple setup supplies the action and generation
theorems. The proved pair-rank bound feeds the completed local Section 16–17
argument, which makes the two-residual of M proper. Fusion and simplicity
give the opposite equality. The final theorem therefore discharges every
earlier action, generation, rank and local-analysis premise. The original
conditional pair-rank interface is retained for its existing consumers.

Source: GLS IV, Chapter 2, Proposition 16.5 and the end of Section 17.
-/

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII PFchapter1section1

/-- The final residual argument with its sole remaining earlier-source
input, the pair-rank bound of Proposition 16.5. -/
public theorem stronglyEmbedded_of_pair_rank_one
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hrank : ∀ t ∈ Z, t ∉ M → ¬ TwoRankAtLeastTwo (residualPairStabilizer M t)) :
    IsStronglyEmbedded M := by
  by_contra hn
  have ha := residualAction_of_minimalCounterexample h r
  have hg := residualGeneration_of_action h r ha hn
  exact twoResidual_ne_top_of_pair_rank_one h r ha hn hg hrank
    (r.twoResidual_eq_top h.disconnected)

/-- The original minimal counterexample and simple reduction imply strong
embedding. Every intermediate residual source premise is discharged. -/
public theorem stronglyEmbedded_of_minimalCounterexample
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) :
    IsStronglyEmbedded M := by
  by_contra hn
  have ha := residualAction_of_minimalCounterexample h r
  have hg := residualGeneration_of_action h r ha hn
  exact twoResidual_ne_top_of_residualGeneration h r ha hn hg
    (r.twoResidual_eq_top h.disconnected)

end BenderSuzuki.ZD
