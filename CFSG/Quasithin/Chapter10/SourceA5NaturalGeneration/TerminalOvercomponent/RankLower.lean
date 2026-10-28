module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CommonSylowCoreSeparation
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LargeTwoCoreQuotientRank
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverOrders
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2OddFixed
public import Theory.GroupTheory.PrimeRankFixedJoin
/-!
# Cubic rank of the actual common natural-block component

Two short groups with different moved layers share a Sylow. Their containing
component's two-core meets the natural group trivially by the common-Sylow
intersection theorem. The literal quotient map therefore preserves its
rank-four elementary module and factor five. The known-simple component
catalogue and Bender non-enlargement force cubic rank at least two whenever
the natural group is a proper local C-component.

Source: Aschbacher--Smith 10.2.3(4), p.747. The original setup discharges the
separate-layer premise in RankLowerOriginal using moved-normalizer control.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open ChapterC ChapterA.Section03
variable {G : Type*} [Group G] [Finite G]

theorem source_natural_pair_component_three_rank
    (L K C R : Subgroup G) (hC : (⊤ : Subgroup C).IsCComponent)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C)
    (hLC : L < C) (hKC : K ≤ C) (S : Sylow 2 C)
    (hloc : L.subgroupOf C ∈ localCComponents S)
    (hL : IsL2EvenBlock L 2) (hK : IsShort K)
    (hcL : pCore 2 L = blockU L) (hcK : pCore 2 K = blockU K)
    (hzL : center L = ⊥) (hzK : center K = ⊥)
    (hRL : Chapter1.IsSylowIn 2 R L) (hRK : Chapter1.IsSylowIn 2 R K)
    (hne : (blockU L).map L.subtype ≠ (blockU K).map K.subtype) :
    2 ≤ primeRank 3 C := by
  let Q := (pCore 2 C).map C.subtype
  have hCQ : C ≤ normalizer (Q : Set G) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hinf : Q ⊓ L = ⊥ := short_pair_twoGroup_intersection_eq_bot L K R Q hL.2.1 hK
    (pCore_isPGroup.map C.subtype) (hLC.le.trans hCQ) (hKC.trans hCQ)
    hzL hzK hcL hcK hRL hRK hne
  let f : L →* C ⧸ pCore 2 C :=
    (QuotientGroup.mk' (pCore 2 C)).comp (inclusion hLC.le)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hq : inclusion hLC.le x ∈ pCore 2 C :=
      (QuotientGroup.eq_one_iff _).mp (show f x = 1 from hx)
    have he : (x : G) ∈ Q ⊓ L := ⟨mem_map_of_mem C.subtype hq,x.property⟩
    have hx1 : (x : G) = 1 := by simpa only [hinf,mem_bot] using he
    exact mem_bot.mpr (Subtype.ext hx1)
  have hU : Nat.card (blockU L) = 16 := by
    rw [card_eq_card_quotient_mul_card_subgroup (blockFixed L),hL.module_card]
    have hb : blockFixed L = ⊥ := by
      ext u
      change (u : L) ∈ center L ↔ u = 1
      rw [hzL,mem_bot]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [hb,card_bot]
    norm_num
  have h2 : 4 ≤ primeRank 2 L := by
    let := hL.2.1.elementary
    exact IsElementaryAbelian.primeRank_ge_of_card (blockU L) (by norm_num [hU])
  have h5 : 5 ∣ Nat.card L := by
    obtain ⟨e⟩ := hL.four_quotient_alternatingFive
    have hh : Nat.card (L ⧸ pCore 2 L) = 60 := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num
    exact (show 5 ∣ 60 by decide).trans (hh ▸ card_quotient_dvd_card (pCore 2 L))
  exact SourceEmbeddings.local_component_three_rank_of_large_twoCore_quotient hsq hC
    S (L.subgroupOf C) hloc (fun he => hLC.ne (le_antisymm hLC.le (subgroupOf_eq_top.mp he)))
    (h2.trans (Theory.GroupTheory.primeRank_le_of_injective 2 f hf))
    (h5.trans (card_dvd_of_injective f hf))
end CFSG.Quasithin.Chapter10
