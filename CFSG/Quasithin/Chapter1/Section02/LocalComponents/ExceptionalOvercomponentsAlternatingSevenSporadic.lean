module
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.OtherSporadic
public import Theory.Alternating.Aut
/-!
# A₇ local sections exclude HS, He and Ru

The actual section order 2520 puts a subgroup with nontrivial two-core in a
full-Sylow two-local of incompatible order. With trivial two-core, even
characteristic gives a faithful full-Sylow action on A₇. Since Aut(A₇)=S₇,
that Sylow has order dividing16, contradicting the native sporadic orders.
The final theorem transports these exclusions to the literal K/O₂(K) for
the original local X ≤ K, preserving the same Sylow normalization.

Source: Aschbacher–Smith A.3.12(18–20), pp.47–48, and 1.2.8, pp.506–507.
-/
public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenModels
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem section_card_dvd {B : Subgroup G}
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) : 2520 ∣ Nat.card B := by
  have hc : Nat.card (B ⧸ pCore 2 B) = 2520 := by
    rw [Nat.card_congr h.some.toEquiv, nat_card_alternatingGroup]
    norm_num
  exact hc ▸ card_quotient_dvd_card (pCore 2 B)

private theorem sylow_card_dvd_of_core_eq_bot (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (hc : pCore 2 B = ⊥) (hE : IsEvenCharacteristicAt S) : Nat.card S ∣ 16 := by
  let eB : B ≃* alternatingGroup (Fin 7) :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans h.some
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup B := eB.isSimpleGroup
  let := Exceptional.local_perfect hB
  have hz : center B = ⊥ :=
    (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
  let : IsQuasisimple B :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hf := sylow_centralizer_eq_bot_of_evenCharacteristic S hE hB hn
  let f := B.normalizerMonoidHom.comp (inclusion hn)
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hf]
    refine ⟨a.property, ?_⟩
    change inclusion hn a ∈ B.normalizerMonoidHom.ker at ha
    rw [normalizerMonoidHom_ker] at ha
    exact ha
  let c : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  have hAut : Nat.card (MulAut B) = 16 * 315 := by
    rw [Nat.card_congr (MulAut.congr eB).toEquiv, ← Nat.card_congr c.toEquiv,
      Nat.card_perm, Nat.card_fin]
    norm_num
  have hd : Nat.card S ∣ 16 * 315 := hAut ▸ card_dvd_of_injective f hinj
  have hcop : Nat.Coprime (Nat.card S) 315 := by
    obtain ⟨m,hm⟩ := S.isPGroup'.exists_card_eq
    rw [hm]
    exact (by decide : Nat.Coprime 2 315).pow_left m
  exact hcop.dvd_of_dvd_mul_right hd

private theorem all_local_bounds {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H)
    (ht : ∀ N : Subgroup H, IsMaximalTwoLocal N → (T : Subgroup H) ≤ N →
      ¬ 2520 ∣ Nat.card N)
    (S : Sylow 2 H) (N : Subgroup H) (hN : IsMaximalTwoLocal N)
    (hSN : (S : Subgroup H) ≤ N) : ¬ 2520 ∣ Nat.card N := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H S T
  have hm := (Theory.Quasithin.maximalTwoLocal_overgroup_conj_iff g S N).mpr ⟨hN,hSN⟩
  rw [hg] at hm
  have hh := ht _ hm.1 hm.2
  rwa [card_map_of_injective (MulAut.conj g).injective] at hh

private theorem not_section_of_local_bounds {H : Type*} [Group H] [Finite H]
    (e : G ≃* H)
    (hb : ∀ (T : Sylow 2 H) (N : Subgroup H), IsMaximalTwoLocal N →
      (T : Subgroup H) ≤ N → ¬ 2520 ∣ Nat.card N)
    (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
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
  have hd : 2520 ∣ Nat.card N := (section_card_dvd h).trans
    (card_dvd_of_le (hBN.trans hNN))
  have hnm := hb (S.mapSurjective e.surjective) (N.map e.toMonoidHom)
    (Theory.Quasithin.isMaximalTwoLocal_map e hN)
    (show (S : Subgroup G).map e.toMonoidHom ≤ N.map e.toMonoidHom from
      map_mono (hSN.trans hNN))
  rw [card_map_of_injective e.injective] at hnm
  exact hnm hd

private theorem higmanSims_local_bound
    (S : Sylow 2 Sporadic.LeechRelated.HS.Carrier)
    (N : Subgroup Sporadic.LeechRelated.HS.Carrier)
    (hN : IsMaximalTwoLocal N) (hSN : (S : Subgroup _) ≤ N) :
    ¬ 2520 ∣ Nat.card N := by
  open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates in
  obtain ⟨T,_,_,_,_,hcover⟩ :=
    MainConverse.SporadicLocal.HSEvenLocalCover.exists_normal_local_cover_of_card_dvd
      card_carrier_dvd
  apply all_local_bounds T _ S N hN hSN
  intro M hM hTM hd
  obtain ⟨i,⟨e⟩⟩ := hcover M hM hTM
  have h9 : 9 ∣ Nat.card (Sporadic.LeechRelated.HS.EvenLocalCandidates.localGroup i) :=
    (Nat.card_congr e.toEquiv) ▸ ((by decide : 9 ∣ 2520).trans hd)
  by_cases hi : i = 0
  · subst i
    exact Sporadic.LeechRelated.HS.EvenLocalCandidates.central_localGroup_nine_not_dvd h9
  · exact Sporadic.LeechRelated.HS.EvenLocalCandidates.large_localGroup_nine_not_dvd i hi h9

private theorem held_candidate_bound (i : Fin 3) :
    ¬ 2520 ∣ Nat.card (Held.TwoLocalCandidates.subgroup i) := by
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
  · exact fun hd => hmax34 false ((by decide : 7 ∣ 2520).trans hd)
  · exact fun hd => hmax34 true ((by decide : 7 ∣ 2520).trans hd)
  · change ¬ 2520 ∣ Nat.card Held.TwoLocalCandidates.max5
    rw [Held.InvolutionFixedData.TwoB.max5_card]
    decide

private theorem held_local_bound (S : Sylow 2 Held.He) (N : Subgroup Held.He)
    (hN : IsMaximalTwoLocal N) (hSN : (S : Subgroup Held.He) ≤ N) :
    ¬ 2520 ∣ Nat.card N := by
  obtain ⟨T,hcatalogue⟩ := Held.TwoLocalCandidates.MaximalNormalizerCatalogue.exists_sylow_catalogue
  apply all_local_bounds T _ S N hN hSN
  intro M hM hTM
  obtain ⟨R,hR,hn,he,hRM⟩ := exists_normal_elementary_normalizer_of_sylow_le T hM hTM
  obtain ⟨i,g,hg⟩ := hcatalogue R hR hn he (hRM ▸ hM)
  rw [hRM,hg,card_map_of_injective (MulAut.conj g).injective]
  exact held_candidate_bound i



/-- No original local A₇ section has Higman–Sims as containing carrier. -/
theorem not_higmanSims (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) (e : G ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
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
    have hh : 512 ∣ 16 := hs.trans hb
    norm_num at hh
  · exact not_section_of_local_bounds e higmanSims_local_bound S B hn h hc


/-- No original local A₇ section has Held as containing carrier. -/
theorem not_held (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) (e : G ≃* Held.He) : False := by
  by_cases hc : pCore 2 B = ⊥
  · have hd : 512 ∣ Nat.card G := (Nat.card_congr e.toEquiv).symm ▸ Exceptional.held_twoPower
    have hs := S.pow_dvd_card_of_pow_dvd_card (n := 9) hd
    have hb := sylow_card_dvd_of_core_eq_bot S B hB hn h hc
      (MainConverse.SporadicLocal.he_evenCharacteristic_of_equiv e S)
    have hh : 512 ∣ 16 := hs.trans hb
    norm_num at hh
  · exact not_section_of_local_bounds e held_local_bound S B hn h hc

/-- No original local A₇ section has Rudvalis as containing carrier. -/
theorem not_rudvalis (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) (e : G ≃* Rudvalis.Model) : False := by
  by_cases hc : pCore 2 B = ⊥
  · have hd : 512 ∣ Nat.card G := by
      rw [Nat.card_congr e.toEquiv, Rudvalis.model_card]
      decide
    have hs := S.pow_dvd_card_of_pow_dvd_card (n := 9) hd
    have hb := sylow_card_dvd_of_core_eq_bot S B hB hn h hc
      (MainConverse.evenCharacteristic_of_model_equiv e
        MainConverse.SporadicLocal.ru_evenCharacteristic S)
    have hh : 512 ∣ 16 := hs.trans hb
    norm_num at hh
  · apply not_section_of_local_bounds e _ S B hn h hc
    intro T N hN hTN hd
    exact Rudvalis.SylowOvergroups.not_nine_dvd_card_twoLocal T N hN.1 hTN
      ((by decide : 9 ∣ 2520).trans hd)



private theorem not_model_of_local_overcomponent
    {M : Type*} [Group M]
    (hexclude : ∀ {V : Type u} [Group V] [Finite V] (S : Sylow 2 V) (B : Subgroup V),
      B ∈ localCComponents S → (S : Subgroup V) ≤ normalizer (B : Set V) →
      Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)) → (V ≃* M) → False)
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hK : K ∈ L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7)))
    (e : (K ⧸ pCore 2 K) ≃* M) : False := by
  let H := K ⊔ (T : Subgroup G)
  have hXH : X ≤ H := hXK.trans le_sup_left
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hx : X.subgroupOf H ∈ L H (S : Subgroup H) :=
    (mem_LIn_iff_subgroupOf le_sup_right hXH).mp ⟨hXH,hX⟩
  have hn' : (S : Subgroup H) ≤ normalizer (X.subgroupOf H : Set H) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : G)
  let q := QuotientGroup.mk' (pCore 2 H)
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hb : (X.subgroupOf H).map q ∈ localCComponents Sbar :=
    mem_L_map_twoCore_mem_localCComponents hx
  have hnb : (Sbar : Subgroup (H ⧸ pCore 2 H)) ≤
      normalizer ((X.subgroupOf H).map q : Set _) :=
    (map_mono hn').trans (le_normalizer_map q)
  let eX := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hXH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hXH))
  have hk : IsPGroup 2 (q.subgroupMap (X.subgroupOf H)).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eB := MonoidHom.quotientPCoreEquivOfSurjective
    (q.subgroupMap (X.subgroupOf H)) (q.subgroupMap_surjective _) hk
  have hm : Nonempty ((((X.subgroupOf H).map q) ⧸ pCore 2 ((X.subgroupOf H).map q)) ≃*
      alternatingGroup (Fin 7)) := ⟨eB.symm.trans (eX.trans h.some)⟩
  let := pCore_isNilpotent (p := 2) (G := H)
  have hC := hK.1.map_quotient (pCore 2 H)
  have hBC : (X.subgroupOf H).map q ≤ (K.subgroupOf H).map q :=
    map_mono (comap_mono hXK)
  obtain ⟨P,_,hl,hs⟩ := exists_local_sylow_normalizing Sbar hb hC.subnormal hBC hnb
  let er := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBC)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hBC))
  let eK := QuotientGroup.congr _ _ (subgroupOfEquivOfLe (show K ≤ H from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)))
  exact hexclude P _ hl hs ⟨er.trans hm.some⟩
    ((cComponentTwoCoreQuotientEquiv hK.1).symm.trans (eK.trans e))

/-- The original local A₇ quotient excludes HS, He and Ru for the
literal maximal-overcomponent quotient, with all quotient maps discharged. -/
theorem local_overcomponent_not_otherSporadic
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hK : K ∈ L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7))) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.HS.Carrier) ∧
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Held.He) ∧
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Rudvalis.Model) := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨e⟩
    exact not_model_of_local_overcomponent not_higmanSims T hX hn hK hXK h e
  · rintro ⟨e⟩
    exact not_model_of_local_overcomponent not_held T hX hn hK hXK h e
  · rintro ⟨e⟩
    exact not_model_of_local_overcomponent not_rudvalis T hX hn hK hXK h e

end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenModels
