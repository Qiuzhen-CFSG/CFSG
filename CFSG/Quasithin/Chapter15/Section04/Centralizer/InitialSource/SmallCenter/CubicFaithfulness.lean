module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.CubicNormalSpan
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.WreathRecognition.Centralizer

/-!
# Faithfulness on the original normal cubic orbit

Characteristic two detects nontrivial normal subgroups through the Sylow
omega center. When that center has order two, every nontrivial normal
subgroup contains it. A centerless such subgroup therefore has trivial
centralizer. Applying this to the actual A₄ or A₄ × A₄ orbit gives
faithful conjugation by the original M, without a kernel premise.

Source: Aschbacher--Smith 15.4.7, printed p.1158; the original normal
subgroup argument reuses the proved centralizer lemma from 15.3.9.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open FamilySource FamilySource.ModuleStructure ChapterC.GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original characteristic two and the order-two omega center give a trivial centralizer. -/
theorem member_normal_centerless_centralizer {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (N : Subgroup M) (hn : N.Normal) (hne : N ≠ ⊥) (hz : center N = ⊥) :
    centralizer (N : Set M) = ⊥ := by
  let Y := N.map M.subtype
  have hYM : Y ≤ M := map_subtype_le _
  have hnY : (Y.subgroupOf M).Normal := by
    simpa only [Y,subgroupOf,comap_map_eq_self_of_injective M.subtype_injective] using hn
  have hYne : Y ≠ ⊥ := fun he => hne ((map_eq_bot_iff_of_injective _ M.subtype_injective).mp he)
  have hchar : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2 := by
    have hh := map_mono (f := M.subtype)
      (h.ambient.evenCharacteristic T M h.maximal h.sylow_le)
    rwa [map_centralizer_subtype] at hh
  have hdis : Y ⊓ Section03.centralInvolutions T ≠ ⊥ := by
    intro he
    exact hYne (Section03.WreathRecognition.normal_eq_bot_of_inf_centralInvolutions_eq_bot
      M Y T h.sylow_le hYM hnY hchar he)
  have hΩ : Section03.centralInvolutions T ≤ Y := by
    have hc : Nat.card (Section03.centralInvolutions T) = 2 := hZ
    have he : Y ⊓ Section03.centralInvolutions T = Section03.centralInvolutions T :=
      eq_of_le_of_card_ge inf_le_right (by
        rw [hc]
        exact Nat.succ_le_of_lt
          ((Y ⊓ Section03.centralInvolutions T).one_lt_card_iff_ne_bot.mpr hdis))
    exact he.symm.le.trans inf_le_left
  have hzY : center Y = ⊥ := by
    apply card_eq_one.mp
    let a : N ≃* Y := N.equivMapOfInjective M.subtype M.subtype_injective
    rw [←Nat.card_congr (centerCongr a).toEquiv,hz,card_bot]
  have hc := Section03.WreathRecognition.centralizer_eq_bot_of_center_eq_bot
    M Y T h.sylow_le hYM hnY hchar hΩ hzY
  apply map_injective M.subtype_injective
  rwa [map_centralizer_subtype,Subgroup.map_bot]

/-- The same source cubic orbit has faithful ambient conjugation. -/
theorem member_cubic_span_faithful {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (R : Subgroup M) (hb : ChapterC.IsBlock R) (ha : ChapterC.IsAlternatingBlock R 3)
    (hm : R = ⁅R,elementaryAbelianMaxJ (T.subtype h.sylow_le : Subgroup M)⁆)
    (hgen : R ⊔ (T.subtype h.sylow_le : Subgroup M) = ⊤) :
    let N := conjugateSpanBy R (T.subtype h.sylow_le : Subgroup M)
    centralizer (N : Set M) = ⊥ := by
  obtain ⟨hn,_,_,hmodel⟩ := member_cubic_normal_span h R hb ha hm hgen
  have hne : conjugateSpanBy R (T.subtype h.sylow_le : Subgroup M) ≠ ⊥ := by
    intro he
    have hR := bot_unique ((le_conjugateSpanBy R _).trans_eq he)
    have hc : Nat.card R = 12 := by
      obtain ⟨a⟩ := ha.equiv_alternatingFour
      rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      rfl
    rw [hR,card_bot] at hc
    omega
  apply member_normal_centerless_centralizer h hZ _ hn hne
  apply card_eq_one.mp
  rcases hmodel with hmodel | hmodel
  · obtain ⟨a⟩ := hmodel
    rw [Nat.card_congr (centerCongr a).toEquiv,
      alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 4)),card_bot]
  · obtain ⟨a⟩ := hmodel
    rw [Nat.card_congr (centerCongr a).toEquiv,AlternatingFourPair.center_eq_bot,card_bot]
end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
