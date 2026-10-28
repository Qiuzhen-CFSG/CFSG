module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Definitions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoModel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ModelAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ShadowBounds
public import CFSG.Quasithin.MainConverse.SporadicLocal.HS.EvenLocalCover
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.LargeNormalizerThreePart
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# Excluding the Higman–Sims component in the rank-two sporadic sieve

Let K be the actual component image in I/C_I(L). The source equality I = LS
makes the quotient by K a two-group, including when the ambient action is an
outer extension. The full S₃ × S₃ Frattini shadow forces 36 to divide the
local subgroup order. Thus nine divides the order of its normal intersection
with K. Characteristic two passes to that intersection, whose nontrivial
two-core places it inside a maximal two-local of K containing a Sylow subgroup.

The fixed degree-100 ATLAS HS carrier has three such local candidates. Their
checked orders are all indivisible by nine. The ambient order-divisibility
premise of the existing cover is discharged by the carrier's checked order
bound. The component marking is the actual quotient equivalence from
`ModelAction`; no alternate HS construction or automorphism-order assumption
is used. All setup fields, relative normality and the full Frattini denominator
are retained in the exported exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.41–42,
printed p.1138, and 1.1.5(3f), printed pp.501–503; GLS3 Table 5.3m,
printed p.274. The imported ATLAS certificates retain their source attribution.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HigmanSims
open Sporadic.LeechRelated.HS
open Sporadic.LeechRelated.HS.EvenLocalCandidates

private theorem local_nine_not_dvd (P : Sylow 2 Carrier) (N : Subgroup Carrier)
    (hN : IsMaximalTwoLocal N) (hPN : (P : Subgroup Carrier) ≤ N) :
    ¬ 9 ∣ Nat.card N := by
  obtain ⟨T, _, _, _, _, hcover⟩ :=
    MainConverse.SporadicLocal.HSEvenLocalCover.exists_normal_local_cover_of_card_dvd
      card_carrier_dvd
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier P T
  have hm := (Theory.Quasithin.maximalTwoLocal_overgroup_conj_iff g P N).mpr ⟨hN, hPN⟩
  rw [hg] at hm
  obtain ⟨i, ⟨e⟩⟩ := hcover _ hm.1 hm.2
  have he := Nat.card_congr (((MulAut.conj g).subgroupMap N).trans e).toEquiv
  rw [he]
  by_cases hi : i = 0
  · subst i
    exact central_localGroup_nine_not_dvd
  · exact large_localGroup_nine_not_dvd i hi

private theorem characteristicTwo_nine_not_dvd (P : Sylow 2 Carrier) (N : Subgroup Carrier)
    (hc : centralizer (pCore 2 N : Set N) ≤ pCore 2 N)
    (hPN : (P : Subgroup Carrier) ≤ N) : ¬ 9 ∣ Nat.card N := by
  intro hd
  have hn : pCore 2 N ≠ ⊥ := by
    intro hb
    have hone (x : N) : x = 1 := by
      apply mem_bot.mp
      rw [← hb]
      apply hc
      rw [hb]
      intro y hy
      rw [mem_bot.mp hy]
      simp
    let : Subsingleton N := ⟨fun x y => (hone x).trans (hone y).symm⟩
    have hcard : Nat.card N = 1 := Nat.card_unique
    rw [hcard] at hd
    norm_num at hd
  obtain ⟨U, hU, hNU⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot N hn
  exact local_nine_not_dvd P U hU (hPN.trans hNU) (hd.trans (card_dvd_of_le hNU))

variable {H : Type*} [Group H] [Finite H]

/-- The source local configuration cannot occur in any two-group extension
of the actual HS carrier. The extra quotient hypothesis is discharged below. -/
theorem no_localConfiguration (K M Y S : Subgroup H) [K.Normal]
    (e : K ≃* Carrier) (hq : IsPGroup 2 (H ⧸ K))
    (d : LocalConfiguration K M Y S) : False := by
  obtain ⟨P, hP⟩ := d.sylow
  have hM9 : 9 ∣ Nat.card M := (by decide : 9 ∣ 36).trans
    (shadow_local_order_bounds P M Y S hP d.sylow_le
      (d.yplus_le.trans inf_le_left) d.shadow).1
  obtain ⟨n, hn⟩ := hq.exists_card_eq
  have hindex : (K.subgroupOf M).index ∣ 2 ^ n := by
    change K.relIndex M ∣ 2 ^ n
    rw [← hn, ← index_eq_card]
    exact relIndex_dvd_index_of_normal K M
  have hcop : Nat.Coprime 9 (K.subgroupOf M).index :=
    ((by decide : Nat.Coprime 9 2).pow_right n).of_dvd_right hindex
  have hK9 : 9 ∣ Nat.card (K.subgroupOf M) := by
    rw [← (K.subgroupOf M).card_mul_index] at hM9
    exact hcop.dvd_of_dvd_mul_right hM9
  let a : K.subgroupOf M ≃* M.subgroupOf K :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let N : Subgroup Carrier := (M.subgroupOf K).map e.toMonoidHom
  let b : K.subgroupOf M ≃* N := a.trans (e.subgroupMap (M.subgroupOf K))
  have hN9 : 9 ∣ Nat.card N := (Nat.card_congr b.toEquiv) ▸ hK9
  have hcM : centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
    rw [← d.characteristicTwo]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  have hcN : centralizer (pCore 2 N : Set N) ≤ pCore 2 N :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 b).mp
      (normal_core_selfCentralizing hcM (K.subgroupOf M))
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal K
  have hQN : ((Q.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 Carrier) :
      Subgroup Carrier) ≤ N := by
    change (Q : Subgroup K).map e.toMonoidHom ≤ (M.subgroupOf K).map e.toMonoidHom
    apply map_mono
    rw [hQ, hP]
    exact comap_mono d.sylow_le
  exact characteristicTwo_nine_not_dvd
    (Q.mapSurjective (f := e.toMonoidHom) e.surjective) N hcN hQN hN9

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HigmanSims

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve

variable {G : Type*} [Group G] [Finite G] {I L M Y S : Subgroup G}
variable [(L.subgroupOf I).Normal]

/-- The Higman–Sims alternative of source 1.1.5(3f) is impossible in
15.3.41. This includes every outer extension allowed by the standing setup. -/
theorem higmanSims_exclusion (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  have hjoin : L.subgroupOf I ⊔ S.subgroupOf I = ⊤ := by
    apply Subgroup.map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le d.component_le,
      map_subgroupOf_eq_of_le (d.join_eq ▸ le_sup_right)]
    simpa only [← MonoidHom.range_eq_map, range_subtype] using d.join_eq.symm
  have hplus : componentImage I L L ⊔ componentImage I L S = ⊤ := by
    change (L.subgroupOf I).map (centralizerQuotientMap (L.subgroupOf I)) ⊔
      (S.subgroupOf I).map (centralizerQuotientMap (L.subgroupOf I)) = ⊤
    rw [← Subgroup.map_sup, hjoin]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  obtain ⟨P, hP⟩ := d.quotient_local.sylow
  have hq := isPGroup_quotient_of_sup_eq_top (componentImage I L L)
    (componentImage I L S) (hP ▸ P.isPGroup') hplus
  exact HigmanSims.no_localConfiguration _ _ _ _ (componentModel d e) hq d.quotient_local

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve
