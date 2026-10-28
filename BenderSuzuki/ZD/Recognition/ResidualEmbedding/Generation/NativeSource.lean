module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource

/-!
# Residual generation from the original minimal simple setup

Every proper residual subgroup is identified with an actual PSL₂(2ⁿ)
model, n≥2. The completed source linear exclusion makes this impossible.
Thus the distinguished involutions and actual residual commutator generate
the whole ambient group. This supplies the generation input of the final
ZD strong-embedding argument, with no recognition or exclusion premise.

Source: GLS IV, Chapter 2, Theorem 12.1 and Proposition 15.1.
-/

namespace BenderSuzuki.ZD
universe u

/-- The original action and minimal simple setup imply residual generation. -/
public theorem residualGeneration_of_action
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hn : ¬ IsStronglyEmbedded M) :
    ResidualGeneration Z M := by
  apply residualGeneration_of_linear_analysis h.disconnected ha hn
  · intro z hz hzM t ht htM hL heven
    exact proper_residualGenerated_linear h r ha hz hzM ht htM hL heven
  · intro z hz hzM t ht htM hL heven n hn e
    exact proper_residualGenerated_linear_false h r ha hz hzM ht htM hL heven n hn e

/-- The action input itself is supplied by the original minimal counterexample. -/
public theorem residualGeneration_of_minimalCounterexample
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hn : ¬ IsStronglyEmbedded M) : ResidualGeneration Z M :=
  residualGeneration_of_action h r (residualAction_of_minimalCounterexample h r) hn

end BenderSuzuki.ZD
