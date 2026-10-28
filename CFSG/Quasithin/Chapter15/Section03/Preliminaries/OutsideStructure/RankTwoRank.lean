module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.SourceSQTK
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.SourceQuotients
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Three-rank of the original cubic quotient

The outside SQTK bound gives rank at most two. The literal cubic
quotient has exponent three and order at least nine. Rank at most one
would make its Sylow three-group cyclic, contradicting that order.
Source: Aschbacher--Smith 15.3.11(5) and 15.3.36.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem rankTwoCase_three_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (h : OutsideStructure.RankTwoCase d I) : primeRank 3 d.Yplus = 2 := by
  have hupper : primeRank 3 d.Yplus ≤ 2 :=
    (primeRank_mono 3 (le_sup_left.trans hI.1.2)).trans
      ((OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide))
  apply le_antisymm hupper
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 d.Yplus) pCore_isPGroup]
  by_contra hr
  let Q := d.Yplus ⧸ pCore 2 d.Yplus
  obtain ⟨hp, he, _⟩ := ComponentIntersection.cubic_quotient_facts d.Yplus h.1
  have hcard : 9 ≤ Nat.card Q := by
    rcases h.1 with hE | ⟨_, hc, _⟩
    · obtain ⟨e⟩ := hE
      dsimp [Q]
      rw [Nat.card_congr e.toEquiv]
      change 9 ≤ Nat.card (Fin 2 → ZMod 3)
      simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      decide
    · exact hc.symm ▸ (by decide : 9 ≤ 27)
  let P : Sylow 3 Q := Sylow.nonempty.some
  have hrQ : ¬ 2 ≤ primeRank 3 Q := hr
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega)
  have hP : (P : Subgroup Q) = ⊤ :=
    top_unique ((hp.to_subgroup ⊤).le_sylow_of_normal P)
  let : IsCyclic Q := isCyclic_of_surjective (P : Subgroup Q).subtype (by
    intro x
    exact ⟨⟨x, by rw [hP]; exact mem_top x⟩, rfl⟩)
  have hc3 : Nat.card Q ≤ 3 := Nat.le_of_dvd (by decide)
    (by simpa only [IsCyclic.exponent_eq_card] using he)
  omega

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure
