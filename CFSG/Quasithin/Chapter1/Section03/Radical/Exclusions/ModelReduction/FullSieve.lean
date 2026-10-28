module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.SieveContract
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.RankOne
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.LinearThreeExclusion
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.LinearThreeModels

/-!
# The full pushing-up model sieve in the radical reduction

The complete C.2.7 source implication supplies its centralizer bound and
all eight model alternatives. The bound makes the star image nontrivial
and the comparison from K/O₂(K) a central cover. The odd-characteristic
linear-three alternative of 1.3.4 is then excluded, leaving the genuine
swapped factors and rank-one models.

In the swapped case K/O₂(K) is simple, so the actual comparison with K*
is an isomorphism. The fixed-model exclusions leave two block types or a
full SL₃(2ⁿ) star image. Transporting that full group through the comparison
and comparing its order with the rank-one models forces n = 1 and the
L₂(7) quotient. Thus every clause of `RankOneSieveConclusion` is supplied.

Only the complete universal C.2.7 implication remains an explicit source
parameter. Its proof and the subsequent elimination of the two small
overlaps belong to their respective assembly owners.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
C.2.7, printed pp.145–147; proof of 1.3.8, p.514.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open FullSieve
open Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Intersect the full C.2.7 list with the two surviving 1.3.4 alternatives.
The universal source implication retains every module and stabilizer clause;
its model projection is derived here, never assumed as a replacement.
The L₂(7) branch uses the actual core-to-star isomorphism. -/
theorem PushingUpComponent.rankOneSieve {κ : GroupClass.{u}} {p : ℕ}
    {T X P M H₀ K : Subgroup G}
    (h : PushingUpComponent κ p T X P M H₀ K) (hp : 3 < p)
    (source : SourceInterface.Source κ G) : RankOneSieveConclusion p T P H₀ K := by
  obtain ⟨hb, hc⟩ := SourceInterface.specialize source h
  rcases h.alternatives.2 with ⟨hs, hm⟩ | ⟨_, hm⟩
  · refine ⟨hs, hm, ?_⟩
    rcases hc.rankOne h.radical_normalizes h.quasisimple hb hm with
      hbinary | hfive | hlinear
    · exact Or.inl hbinary
    · exact Or.inr (Or.inl hfive)
    · obtain ⟨n, hn, F, _, _, hF, ⟨e⟩⟩ := hlinear
      let coreEquiv := coreStarEquivOfSwapped h.radical_normalizes h.quasisimple hb hm
      exact Or.inr (Or.inr
        (slThree_swapped_parameter hn hF (coreEquiv.trans e) (swappedModel_three hm)).2)
  · exact (not_linearThreeModel h hp hb hc hm).elim

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
