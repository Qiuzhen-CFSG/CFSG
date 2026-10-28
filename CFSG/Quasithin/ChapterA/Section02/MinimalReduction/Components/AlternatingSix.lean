module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Components.Source
public import Theory.Alternating.TripleSixLocalRank

/-!
# Excluding a triple-A₆ factor from the centered source pair

The actual triple-A₆ normalizer has cubic rank at least two. The original
quasithin component-product argument bounds it by one when a second centered
component is present. This discharges the A₆ leaf of the source local-rank
model sieve, without an exponent or normalizer premise.

Source: Aschbacher–Smith A.2.12(I)–(II), printed pp.36–37.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
open Chapter1.Section02.LocalModels
universe u
variable {G S : Type u} [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem OddCenterCovers.alternating_six_local_threeRank_ge_two
    {L : Type*} [Group L] [Finite L] (h : IsAlternatingCover L 6) :
    2 ≤ twoLocalPrimeRank 3 L := by
  let := h.1
  obtain ⟨z⟩ := h.2.1
  obtain ⟨e⟩ := h.2.2
  have hc : Nat.card (center L) = 3 := by simpa using Nat.card_congr z.toEquiv
  exact GLS3.Chapter5.OddCentralCovers.triple_six_twoLocalThreeRank_ge_two e hc

theorem CounterexampleToTheoremA.not_alternating_six_centered_pair
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hsemi : IsSemisimple G) (hn : ¬ IsQuasisimple G)
    {C D : Subgroup G} (hC : IsComponent G C) (hD : IsComponent G D) (hne : C ≠ D)
    (hzC : center C ≠ ⊥) (hzD : center D ≠ ⊥) (hm : IsAlternatingCover C 6) : False := by
  have hsmall := h.source_component_local_threeRank_le_one ih hsemi hn hC hD hne hzC hzD
  have hbig := OddCenterCovers.alternating_six_local_threeRank_ge_two hm
  omega

end CFSG.Quasithin.ChapterA.Section02
