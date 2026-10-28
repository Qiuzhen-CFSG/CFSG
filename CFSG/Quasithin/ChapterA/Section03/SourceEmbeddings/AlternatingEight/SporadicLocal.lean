module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.SporadicOrders
public import CFSG.Quasithin.MainConverse.SporadicLocal.J2.LocalCover
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer
public import CFSG.Quasithin.MainConverse.SporadicLocal.HS.EvenLocalCover
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.LargeNormalizerThreePart
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart
public import Theory.SpecificGroups.Held.TwoLocalCandidates.ThreeCoreBounds
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.TwoLocalOrder

/-!
# Nontrivial two-cores in the sporadic A₈ containing rows

The image of O₂(B) is characteristic in B. Its normalizer therefore contains
both B and the original Sylow subgroup. The proved maximal two-local catalogues
for J₂, HS, He and Ru give order obstructions to an A₈ section in this normalizer.
No quasisimplicity of B or ordinary-subgroup maximality is assumed.

Source: Aschbacher–Smith A.3.12, pp.47–48, used in 15.3.32(3), p.1133;
GLS3 Tables 5.3g, 5.3m, 5.3p and 5.3r. The imported catalogues concern the
literal sporadic carriers and discharge their finite coverage certificates.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight

private theorem all_local_bounds {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H)
    (ht : ∀ N : Subgroup H, IsMaximalTwoLocal N → (T : Subgroup H) ≤ N →
      ¬ 20160 ∣ Nat.card N)
    (S : Sylow 2 H) (N : Subgroup H) (hN : IsMaximalTwoLocal N)
    (hSN : (S : Subgroup H) ≤ N) : ¬ 20160 ∣ Nat.card N := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H S T
  have hm := (Theory.Quasithin.maximalTwoLocal_overgroup_conj_iff g S N).mpr ⟨hN,hSN⟩
  rw [hg] at hm
  have hh := ht _ hm.1 hm.2
  rwa [card_map_of_injective (MulAut.conj g).injective] at hh

private theorem not_section_of_local_bounds {G H : Type*} [Group G] [Finite G]
    [Group H] [Finite H] (e : G ≃* H)
    (hb : ∀ (T : Sylow 2 H) (N : Subgroup H), IsMaximalTwoLocal N →
      (T : Subgroup H) ≤ N → ¬ 20160 ∣ Nat.card N)
    (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (hcore : pCore 2 B ≠ ⊥) : False := by
  let U := (pCore 2 B).map B.subtype
  have hU : U ≠ ⊥ := fun he => hcore
    ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have hloc : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U,hU,pCore_isPGroup.map B.subtype,rfl⟩
  have hnorm := normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  have hBN : B ≤ normalizer (U : Set G) := B.le_normalizer.trans hnorm
  have hSN : (S : Subgroup G) ≤ normalizer (U : Set G) := hn.trans hnorm
  obtain ⟨N,hNN,hN⟩ := Finite.exists_le_maximal hloc
  have hd : 20160 ∣ Nat.card N := (quotient_card_dvd h).trans
    (card_dvd_of_le (hBN.trans hNN))
  have hnm := hb (S.mapSurjective e.surjective) (N.map e.toMonoidHom)
    (Theory.Quasithin.isMaximalTwoLocal_map e hN)
    (show (S : Subgroup G).map e.toMonoidHom ≤ N.map e.toMonoidHom from
      map_mono (hSN.trans hNN))
  rw [card_map_of_injective e.injective] at hnm
  exact hnm hd

private theorem jankoTwo_local_bound
    (S : Sylow 2 Sporadic.LeechRelated.J2.Carrier)
    (N : Subgroup Sporadic.LeechRelated.J2.Carrier)
    (hN : IsMaximalTwoLocal N) (hSN : (S : Subgroup _) ≤ N) :
    ¬ 20160 ∣ Nat.card N := by
  apply all_local_bounds MainConverse.SporadicLocal.J2Even.sylowTwo _ S N hN hSN
  intro M hM hSM
  rcases MainConverse.SporadicLocal.J2Even.sylowLocalCover M hM hSM with he | he
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv,
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_l₁]
    decide
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv,
      Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.card_p₂]
    decide

private theorem higmanSims_local_bound
    (S : Sylow 2 Sporadic.LeechRelated.HS.Carrier)
    (N : Subgroup Sporadic.LeechRelated.HS.Carrier)
    (hN : IsMaximalTwoLocal N) (hSN : (S : Subgroup _) ≤ N) :
    ¬ 20160 ∣ Nat.card N := by
  open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates in
  obtain ⟨T,_,_,_,_,hcover⟩ :=
    MainConverse.SporadicLocal.HSEvenLocalCover.exists_normal_local_cover_of_card_dvd
      card_carrier_dvd
  apply all_local_bounds T _ S N hN hSN
  intro M hM hTM hd
  obtain ⟨i,⟨e⟩⟩ := hcover M hM hTM
  have h9 : 9 ∣ Nat.card (Sporadic.LeechRelated.HS.EvenLocalCandidates.localGroup i) :=
    (Nat.card_congr e.toEquiv) ▸ ((by decide : 9 ∣ 20160).trans hd)
  by_cases hi : i = 0
  · subst i
    exact Sporadic.LeechRelated.HS.EvenLocalCandidates.central_localGroup_nine_not_dvd h9
  · exact Sporadic.LeechRelated.HS.EvenLocalCandidates.large_localGroup_nine_not_dvd i hi h9

private theorem held_candidate_bound (i : Fin 3) :
    ¬ 20160 ∣ Nat.card (Held.TwoLocalCandidates.subgroup i) := by
  have hmax34 (j : Bool) :
      ¬ 7 ∣ Nat.card (Held.LocalPairs.PairCoverage.localOvergroup j) := by
    let f := Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.SixPoint.quotientAction j
    have hc := f.ker.card_mul_index
    rw [index_ker] at hc
    have hquot : Nat.card (Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.LocalQuotient j) ∣ 2160 := by
      rw [← hc]
      have hd : Nat.card f.range ∣ 720 := by
        simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
          using f.range.card_subgroup_dvd_card
      exact Nat.mul_dvd_mul
        (Held.TwoLocalCandidates.ThreeCoreBounds.quotientAction_kernel_card_dvd_three j) hd
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2)
      (G := Held.LocalPairs.PairCoverage.localOvergroup j)).exists_card_eq
    intro hd
    rw [← (pCore 2 (Held.LocalPairs.PairCoverage.localOvergroup j)).card_mul_index,hn] at hd
    have hh := (((by decide : Nat.Coprime 7 2).pow_right n).dvd_of_dvd_mul_left hd).trans hquot
    norm_num at hh
  fin_cases i
  · exact fun hd => hmax34 false ((by decide : 7 ∣ 20160).trans hd)
  · exact fun hd => hmax34 true ((by decide : 7 ∣ 20160).trans hd)
  · change ¬ 20160 ∣ Nat.card Held.TwoLocalCandidates.max5
    rw [Held.InvolutionFixedData.TwoB.max5_card]
    decide

private theorem held_local_bound (S : Sylow 2 Held.He) (N : Subgroup Held.He)
    (hN : IsMaximalTwoLocal N) (hSN : (S : Subgroup Held.He) ≤ N) :
    ¬ 20160 ∣ Nat.card N := by
  obtain ⟨T,hcatalogue⟩ := Held.TwoLocalCandidates.MaximalNormalizerCatalogue.exists_sylow_catalogue
  apply all_local_bounds T _ S N hN hSN
  intro M hM hTM
  obtain ⟨R,hR,hn,he,hRM⟩ := exists_normal_elementary_normalizer_of_sylow_le T hM hTM
  obtain ⟨i,g,hg⟩ := hcatalogue R hR hn he (hRM ▸ hM)
  rw [hRM,hg,card_map_of_injective (MulAut.conj g).injective]
  exact held_candidate_bound i

variable {G : Type*} [Group G] [Finite G]

/-- A Sylow-normalized A₈ section with nontrivial two-core cannot occur in J₂. -/
theorem not_janko_two_of_core_ne_bot (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) (hcore : pCore 2 B ≠ ⊥)
    (e : G ≃* Sporadic.LeechRelated.J2.Carrier) : False :=
  not_section_of_local_bounds e jankoTwo_local_bound S B hn h hcore

/-- A Sylow-normalized A₈ section with nontrivial two-core cannot occur in HS. -/
theorem not_higmanSims_of_core_ne_bot (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) (hcore : pCore 2 B ≠ ⊥)
    (e : G ≃* Sporadic.LeechRelated.HS.Carrier) : False :=
  not_section_of_local_bounds e higmanSims_local_bound S B hn h hcore

/-- A Sylow-normalized A₈ section with nontrivial two-core cannot occur in He. -/
theorem not_held_of_core_ne_bot (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) (hcore : pCore 2 B ≠ ⊥)
    (e : G ≃* Held.He) : False :=
  not_section_of_local_bounds e held_local_bound S B hn h hcore

/-- A Sylow-normalized A₈ section with nontrivial two-core cannot occur in Ru. -/
theorem not_rudvalis_of_core_ne_bot (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) (hcore : pCore 2 B ≠ ⊥)
    (e : G ≃* Rudvalis.Model) : False := by
  apply not_section_of_local_bounds e _ S B hn h hcore
  intro T N hN hTN hd
  exact Rudvalis.SylowOvergroups.not_nine_dvd_card_twoLocal T N hN.1 hTN
    ((by decide : 9 ∣ 20160).trans hd)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
