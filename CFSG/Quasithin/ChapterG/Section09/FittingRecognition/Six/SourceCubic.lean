module
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six.RankTwoCubic
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six.AbelianCoreCubic
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six.NonabelianCoreCubic
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six.ElementaryCoreCubic
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six.ElementaryCoreCentralizer

/-!
# A normal cubic in the original degree-six Fitting branch

The faithful action bounds the three-core order by 81 and its rank by
three. At rank two, a characteristic critical subgroup gives the desired
cubic. Above rank two, a nonabelian core has central omega subgroup of order
three or nine, and a non-elementary abelian core has cubic Frattini subgroup.
The remaining elementary core has order 27 and is self-centralizing on the
six-space; A.1.31(3), on the original SQTK cover, finishes that case.

This is the precise G.9.4 consequence consumed by original 14.3.15. It
retains the given representation and does not require a full normalizer model.

Source: Aschbacher--Smith G.9.4(5), printed p.355, and 14.3.15, p.994.
-/

public section
open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The cubic degree-six source branch contains a normal subgroup of order three. -/
theorem normal_cubic_of_source_degree_six
    {K : GroupClass} {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    (h : FittingHypothesis K ρ A 2)
    (hc : IsPGroup 3 (⁅fittingSubgroup G,A⁆ : Subgroup G))
    (hd : finrank (ZMod 2) V = 6) :
    ∃ C : Subgroup G, C.Normal ∧ Nat.card C = 3 := by
  by_cases hr : primeRank 3 (pCore 3 G) ≤ 2
  · exact normal_cubic_of_source_three_rank_le_two h hc hd hr
  have hrgt : 2 < primeRank 3 (pCore 3 G) := Nat.lt_of_not_ge hr
  by_cases hab : IsMulCommutative (pCore 3 G)
  · by_cases hea : IsElementaryAbelian 3 (pCore 3 G)
    · let : IsElementaryAbelian 3 (pCore 3 G) := hea
      let : IsElementaryAbelian 3 (⊤ : Subgroup (pCore 3 G)) :=
        IsElementaryAbelian.of_injective (⊤ : Subgroup (pCore 3 G)).subtype
          (⊤ : Subgroup (pCore 3 G)).subtype_injective
      have hB : Nat.card (pCore 3 G) = 27 := by
        obtain ⟨E,hE,hEc⟩ := source_six_rank_three_has_elementary_twentyseven h hd hrgt
        have hl : 27 ≤ Nat.card (pCore 3 G) := hEc ▸ E.card_le_card_group
        have hu := (primeRank_le_iff_elementary_card_le (pCore 3 G)).mp
          (source_six_threeCore_rank_le_three h hd) ⊤ inferInstance
        have hu' : Nat.card (pCore 3 G) ≤ 27 := by simpa using hu
        omega
      exact normal_cubic_of_elementary_core_centralizer h hd hB
        (elementary_threeCore_centralizer_le h hd hB)
    · obtain ⟨C,hCn,hCc,_⟩ :=
        source_six_abelian_nonelementary_core_normal_cubic h hd hrgt hab hea
      exact ⟨C,hCn,hCc⟩
  · exact normal_cubic_of_source_nonabelian_threeCore h hd hab

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six
