module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockAlternatingFive
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceNonblock

/-!
# The nonblock exclusion at the original Baumann input

Baumann escape gives the actual A₅ block and identifies its natural layer
with the full omega-center module. Select the auxiliary chosen module from
the original Input and apply the layer-closure block theorem to the literal
SourceConfiguration. No MS witness, Frattini premise, parabolic marking or
later Hypothesis1223 exclusion remains in this nonblock consumer.

The original Baumann bound and Cartan assembly remain with
qt-d-1222-rankone-baumann-control-source. The general nonblock endgame
remains with qt-d-1222-rankone-uniqueness-nonblock.
Source: Aschbacher--Smith 5.1.7(1), pp.633--634, using C.1.13(c)
and the original 4.3.8--10 configuration, pp.616--617.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

/-- The actual original-input constrained nonblock branch is impossible. -/
theorem Input.original_nonblock_false
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ ChapterC.IsBlock c.K) : False := by
  obtain ⟨V,⟨D⟩⟩ := h.original_section1221.exists_chosen_of_normalizes h.sylow_normalizes
  obtain ⟨_,hA,hU,_⟩ := h.alternating_block_of_baumann_escape hout
  exact hb (c.block_of_alternatingFive D hf hA
    (hU.trans (h.original_fullModule_eq_moved hout).symm))
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
