module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModule
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.MarkedSource

/-!
# The marked A₅ consumer of the conditional rank-one source assembly

The model obtained from the whole reduced commutator layer supplies the
literal `A5Setup.MarkedSource` consumer. Its quotient map, chosen subgroup,
normalizer action and invariant flag are the original ones. T-invariance of
V and the flag remain the separate structural owner's inputs, while the
two missing rank-one exits remain with the rank-one source assembly owner.

Source: Aschbacher--Smith, 12.2.2(3d) and 13.3.2(3), pp.795 and 885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} (D : ChosenModule T L V)
include D

/-- Construct the actual Chapter 13 context from the earlier rank-one exits,
rather than assuming a model on the selected subgroup. -/
theorem marked_context_of_rankOne_source_exits_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h1331 : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hgeneric : RankOneModule.GenericConfigurationExit T L)
    (hsmall : RankOneModule.SmallExit T L)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (h12 : V₁ ≤ V₂) (h2V : V₂ ≤ V) (h1 : Nat.card V₁ = 2) (h2 : Nat.card V₂ = 4)
    (hT1 : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hT2 : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (h3V : V₃ ≤ V) (h3 : Nat.card V₃ = 8)
    (hT3 : (T : Subgroup G) ≤ normalizer (V₃ : Set G)) :
    Nonempty (Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃) := by
  exact Chapter13.Section03.A5Setup.context_of_natural_module h1331 D
    (D.rankOne_module_of_source_exits_of_many h hmany hn hpsl hgeneric hsmall).2
    hTV h12 h2V h1 h2 hT1 hT2 h3V h3 hT3

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
