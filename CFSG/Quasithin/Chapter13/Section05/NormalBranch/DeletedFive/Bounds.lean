module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup.Action

/-!
# The source Sylow bound in the deleted-five branch

The existing action of the normalizer of an alternating-five block on its
literal module maps into S₅. When that module is self-centralizing, the
kernel is exactly the module, so its full normalizer has order dividing
16 · 120. Every two-subgroup of this normalizer has order at most 128.
The original subgroup of index at most two in an ambient Sylow therefore
bounds that Sylow by 256.

Source: Aschbacher–Smith 13.5.15, printed p.921. The final statement keeps
the actual local subgroup P, ambient Sylow T and their relative index.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem normalizer_card_dvd (K : Subgroup X)
    (hK : ChapterC.IsAlternatingBlock K 5)
    (hc : Nat.card ((ChapterC.blockU K).map K.subtype) = 16)
    (hself : centralizer ((ChapterC.blockU K).map K.subtype : Set X) ≤
      (ChapterC.blockU K).map K.subtype)
    (hctrl : normalizer ((ChapterC.blockU K).map K.subtype : Set X) ≤
      normalizer (K : Set X)) :
    Nat.card (normalizer ((ChapterC.blockU K).map K.subtype : Set X)) ∣ 1920 := by
  let U := (ChapterC.blockU K).map K.subtype
  let N := normalizer (U : Set X)
  let := hK.2.1.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map K.subtype
  have hKN : K ≤ N := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (ChapterC.blockU K))
  obtain ⟨q,e,hker,-,-⟩ :=
    ChapterC.Section05.BlockAnalysis.AlternatingSetup.exists_action hK hKN hctrl
  have hcent : centralizer (U : Set X) = U := le_antisymm hself (le_centralizer U)
  have hkcard : Nat.card q.ker = 16 := by
    rw [hker]
    change Nat.card ((centralizer (U : Set X)).subgroupOf N) = 16
    rw [hcent,Nat.card_congr (subgroupOfEquivOfLe U.le_normalizer).toEquiv]
    exact hc
  have hcard := q.ker.card_mul_index
  rw [index_ker,hkcard] at hcard
  have hr : Nat.card q.range ∣ 120 := by
    have hh := q.range.card_subgroup_dvd_card
    have hfive : Fintype.card (ChapterC.Section05.ConjugateSource.FivePerm) = 120 := by
      rw [Fintype.card_perm]
      decide
    simpa only [Nat.card_eq_fintype_card (α := ChapterC.Section05.ConjugateSource.FivePerm),
      hfive] using hh
  rw [←hcard]
  exact Nat.mul_dvd_mul_left 16 hr

theorem normalizer_twoSubgroup_card_le (K P : Subgroup X)
    (hK : ChapterC.IsAlternatingBlock K 5)
    (hc : Nat.card ((ChapterC.blockU K).map K.subtype) = 16)
    (hself : centralizer ((ChapterC.blockU K).map K.subtype : Set X) ≤
      (ChapterC.blockU K).map K.subtype)
    (hctrl : normalizer ((ChapterC.blockU K).map K.subtype : Set X) ≤
      normalizer (K : Set X))
    (hP : IsPGroup 2 P)
    (hPN : P ≤ normalizer ((ChapterC.blockU K).map K.subtype : Set X)) :
    Nat.card P ≤ 128 := by
  have hd := (card_dvd_of_le hPN).trans (normalizer_card_dvd K hK hc hself hctrl)
  obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp hP
  have hcop : Nat.Coprime (Nat.card P) 15 := by
    rw [hn]
    exact (show Nat.Coprime 2 15 by decide).pow_left n
  exact Nat.le_of_dvd (by decide : 0 < 128) (hcop.dvd_of_dvd_mul_left hd)

theorem sylow_card_le (K P : Subgroup X)
    (hK : ChapterC.IsAlternatingBlock K 5)
    (hc : Nat.card ((ChapterC.blockU K).map K.subtype) = 16)
    (hself : centralizer ((ChapterC.blockU K).map K.subtype : Set X) ≤
      (ChapterC.blockU K).map K.subtype)
    (hctrl : normalizer ((ChapterC.blockU K).map K.subtype : Set X) ≤
      normalizer (K : Set X))
    (hPN : P ≤ normalizer ((ChapterC.blockU K).map K.subtype : Set X))
    (T : Sylow 2 X) (hPT : P ≤ T) (hi : P.relIndex T ≤ 2) : Nat.card T ≤ 256 := by
  have hp := normalizer_twoSubgroup_card_le K P hK hc hself hctrl (T.isPGroup'.to_le hPT) hPN
  have hh : Nat.card P * P.relIndex T = Nat.card T := by
    simpa only [relIndex_bot_left] using relIndex_mul_relIndex ⊥ P T bot_le hPT
  rw [←hh]
  exact (Nat.mul_le_mul hp hi).trans (by decide)

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
