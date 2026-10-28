module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.FaithfulSylow
/-!
# The remaining large sporadic local-order exclusions

For Higman–Sims, Held and Rudvalis a nontrivial intrinsic two-core puts the smaller
subgroup into a full-Sylow two-local normalizer of incompatible order.
If that core is trivial, the full Sylow acts faithfully on the exceptional
carrier, whose automorphism group's two-part is at most 256. Each ambient
carrier has two-part at least 512. This excludes all three exceptional
sections with the original subgroup and Sylow marking.
Source: Aschbacher–Smith A.3.12, printed pp.47–48; 13.6.27, p.934.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
variable {G : Type*} [Group G] [Finite G]

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

/-- No original exceptional local section has Higman–Sims as containing carrier. -/
theorem not_higmanSims (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B)) (e : G ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  by_cases hc : pCore 2 B = ⊥
  · have hd : 512 ∣ Nat.card G := by
      rw [Nat.card_congr e.toEquiv]
      apply dvd_trans (b := Nat.card Sporadic.LeechRelated.HS.EvenLocalCandidates.subgroup)
      · rw [Sporadic.LeechRelated.HS.EvenLocalCandidates.subgroup_card]
        decide
      · exact card_subgroup_dvd_card _
    have hs := S.pow_dvd_card_of_pow_dvd_card (n := 9) hd
    have hb := sylow_card_dvd_of_core_eq_bot S B hB hn h hc
      (MainConverse.evenCharacteristic_of_model_equiv e
        MainConverse.SporadicLocal.hs_evenCharacteristic S)
    have hh : 512 ∣ 256 := hs.trans hb
    norm_num at hh
  · exact not_section_of_local_bounds e higmanSims_local_bound S B hn h hc


/-- No original exceptional local section has Held as containing carrier. -/
theorem not_held (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B)) (e : G ≃* Held.He) : False := by
  by_cases hc : pCore 2 B = ⊥
  · have hd : 512 ∣ Nat.card G := (Nat.card_congr e.toEquiv).symm ▸ held_twoPower
    have hs := S.pow_dvd_card_of_pow_dvd_card (n := 9) hd
    have hb := sylow_card_dvd_of_core_eq_bot S B hB hn h hc
      (MainConverse.SporadicLocal.he_evenCharacteristic_of_equiv e S)
    have hh : 512 ∣ 256 := hs.trans hb
    norm_num at hh
  · exact not_section_of_local_bounds e held_local_bound S B hn h hc

/-- No original exceptional local section has Rudvalis as containing carrier. -/
theorem not_rudvalis (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B)) (e : G ≃* Rudvalis.Model) : False := by
  by_cases hc : pCore 2 B = ⊥
  · have hd : 512 ∣ Nat.card G := by
      rw [Nat.card_congr e.toEquiv, Rudvalis.model_card]
      decide
    have hs := S.pow_dvd_card_of_pow_dvd_card (n := 9) hd
    have hb := sylow_card_dvd_of_core_eq_bot S B hB hn h hc
      (MainConverse.evenCharacteristic_of_model_equiv e
        MainConverse.SporadicLocal.ru_evenCharacteristic S)
    have hh : 512 ∣ 256 := hs.trans hb
    norm_num at hh
  · apply not_section_of_local_bounds e _ S B hn h hc
    intro T N hN hTN hd
    exact Rudvalis.SylowOvergroups.not_nine_dvd_card_twoLocal T N hN.1 hTN
      ((by decide : 9 ∣ 20160).trans hd)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
