module

public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.LaterDefs
public import Stellmacher.SectionFiveToSeven.Result7_3
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction
public import Stellmacher.TwoResidualSylowSupplement
public import Theory.GroupTheory.CenterFreeOddImageCore
public import Stellmacher.ElementaryAbelianMaxOrder
public import Stellmacher.SectionEight.EightThreeCoreBound
public import Stellmacher.SectionEight.EightThreeThompsonNotCore
public import Stellmacher.SectionTwo.ThompsonResidualBaumann
public import Stellmacher.SectionThree.LocalCoreQuotientOddResidual

/-! Graph-preserving local kernels for the generated proof of Stellmacher (8.3). -/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- The initial two-core equals its vertex center module under the (8.3) commutator bound. -/
public theorem eight_three_core_eq_center_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcomm : ⁅QAt ctx.Γ ctx.criticalPath.a, EAt ctx.Γ ctx.criticalPath.a⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a) :
    QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a := by
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Pb := stabilizer Γ cp.firstStep
  let Z := z Γ cp.a
  let Q := pCore 2 P
  let E := twoResidualAmbient (⊤ : Subgroup P)
  have ha : cp.a ∈ neighborhood Γ cp.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  have hb : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have h73 := lemma_seven_three h Γ
  have hPcenter : Subgroup.center P = ⊥ := by
    let T : Sylow 2 (↥(Pb ⊓ P)) := default
    have hdata := edge_sectionThree_data h Γ ha T
    have halt := h73.centralizer_alternative cp.firstStep cp.a ha T
    have hZeq : z Γ cp.firstStep = omegaOneCenter Pb := by
      rcases halt with heq | heq
      · have hWPb : sylowTwoAmbient (Pb ⊓ P) T ≤ Pb :=
          (Subgroup.map_subtype_le _).trans inf_le_left
        have hWC : sylowTwoAmbient (Pb ⊓ P) T ≤ Subgroup.centralizer (z Γ cp.firstStep : Set H) :=
          hWPb.trans (Subgroup.le_centralizer_iff.mp
            (hcenter.trans (SevenSix.centerAmbient_le_centralizer Pb)))
        rw [inf_eq_left.mpr hWC] at heq
        have hcore : q Γ cp.firstStep = twoCoreAmbient Pb := Γ.twoCoreAt_def cp.firstStep
        exact (hdata.2.1.1.2.2.2 (heq.trans hcore)).elim
      · exact heq.1
    exact h73.center_neighbor_trivial cp.firstStep cp.a ha hZeq
  have hZomega : Z ≤ omegaOneCenter (q Γ cp.a) := h73.center_core cp.a cp.firstStep hb
  have hZQ : Z ≤ q Γ cp.a := hZomega.trans (Subgroup.map_subtype_le _)
  have hQmap : Q.map P.subtype = q Γ cp.a := by
    change twoCoreIn P = q Γ cp.a
    exact (Γ.twoCoreAt_def cp.a).symm
  have hQP : q Γ cp.a ≤ P := by rw [← hQmap]; exact Subgroup.map_subtype_le _
  have hZP : Z ≤ P := hZQ.trans hQP
  let V := Z.subgroupOf P
  have hVmap : V.map P.subtype = Z := Subgroup.map_subgroupOf_eq_of_le hZP
  have hEmap : E.map P.subtype = e Γ cp.a := by
    have hm := map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup P) P.subtype P
      (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])
    exact hm.trans (Γ.twoResidualAt_def cp.a).symm
  let _ : E.Normal := by
    dsimp only [E]
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
    exact BenderSuzuki.External.hktPResidual_normal
  have hSP := (SevenSix.edge_sylow_data h Γ cp).1
  obtain ⟨hSPle, T, hT⟩ := hSP
  have hcover : E ⊔ (T : Subgroup P) = ⊤ := twoResidualAmbient_top_sup_sylow T
  have hPset := (pFamily_iff_pSet _ _ _).mp (SevenSix.edge_local_data h Γ cp).1.1
  have hsolv := (SevenSix.edge_local_data h Γ cp).1.2
  obtain ⟨B, hB, hSB, huniq⟩ := hPset.2
  have hBnative : IsCoatom B ∧ S.subgroupOf P ≤ B ∧
      ∀ B' : Subgroup P, IsCoatom B' → S.subgroupOf P ≤ B' → B' = B := by
    refine ⟨hB, ?_, ?_⟩
    · intro s hs
      obtain ⟨b, hb, he⟩ := hSB hs
      exact P.subtype_injective he ▸ hb
    · intro B' hB' hS'
      apply huniq B' hB'
      intro s hs
      exact ⟨⟨s, hSPle hs⟩, hS' hs, rfl⟩
  obtain ⟨p, hp, hpodd, hres⟩ :=
    (SectionThree.lemma_three_three S (SevenSix.sectionThreeHypotheses h) P hPset B B.normalCore hBnative
      ⟨B.normalCore_le, inferInstance, fun N hN hNB => by
        let _ := hN
        exact Subgroup.normal_le_normalCore.mpr hNB⟩ hsolv).part_a
  let f := QuotientGroup.mk' Q
  have hodd : Odd (Nat.card (E.map f)) := by
    rw [map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup P) f ⊤
      (Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective Q))]
    let _ : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := hres.exists_card_eq
    rw [hn]
    exact hpodd.pow
  have hVcentral : V ≤ Subgroup.centralizer (Q : Set P) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    apply Subtype.ext
    have hvc := (SevenSix.omegaOneCenter_le_centerAmbient (q Γ cp.a)) (hZomega hv)
    have hrq : (r : H) ∈ q Γ cp.a := hQmap ▸ Subgroup.mem_map_of_mem P.subtype hr
    exact Subgroup.mem_centralizer_iff.mp
      ((SevenSix.centerAmbient_le_centralizer (q Γ cp.a)) hvc) r hrq
  have hcommN : ⁅Q, E⁆ ≤ V := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_commutator, hQmap, hEmap, hVmap]
    exact hcomm
  have hQV := Subgroup.le_of_centerfree_odd_image_commutator_le T E Q V hcover
    (pCore_isPGroup (p := 2) (G := P)) hodd hPcenter hVcentral hcommN
  apply le_antisymm ?_ hZQ
  rw [← hQmap, ← hVmap]
  exact Subgroup.map_mono hQV

end Stellmacher.SectionEight


namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext

public theorem eight_three_thompson_not_le_core_local
    {H : Type*} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcore : QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a)
    (hcontained : QAt ctx.Γ ctx.criticalPath.a ≤ QAt ctx.Γ ctx.criticalPath.firstStep) :
    ¬ elementaryAbelianMaxJ (QAt ctx.Γ ctx.criticalPath.firstStep) ≤
      QAt ctx.Γ ctx.criticalPath.a := by
  classical
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Pb := stabilizer Γ cp.firstStep
  let Q := q Γ cp.a
  let T := q Γ cp.firstStep
  let J := elementaryAbelianMaxJ T
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have helem : IsElementaryAbelian 2 Q := by
    change IsElementaryAbelian 2 (QAt Γ cp.a)
    rw [hcore]
    exact SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  have hQT : Q ≤ T := hcontained
  intro hJQ
  have hQJ : Q ≤ J := by
    obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty T
    have hAQ : A ≤ Q := (le_sSup hA).trans hJQ
    have heq : A = Q := Subgroup.eq_of_le_of_card_ge hAQ (hA.2.2 Q hQT helem)
    rw [← heq]
    exact le_sSup hA
  have hJ : J = Q := le_antisymm hJQ hQJ
  have hPbT : Pb ≤ Subgroup.normalizer (T : Set H) := by
    rw [show T = twoCoreIn Pb from Γ.twoCoreAt_def cp.firstStep]
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hPbQ : Pb ≤ Subgroup.normalizer (Q : Set H) := by
    rw [← hJ]
    intro g hg
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (elementaryAbelianMaxJ T).map (MulAut.conj g).toMonoidHom = elementaryAbelianMaxJ T
    rw [← elementaryAbelianMaxJ_map_equiv]
    have ht : T.map (MulAut.conj g).toMonoidHom = T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPbT hg)
    rw [ht]
  have hPQ : P ≤ Subgroup.normalizer (Q : Set H) := by
    rw [show Q = twoCoreIn P from Γ.twoCoreAt_def cp.a]
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hcover : P ⊔ Pb = ⊤ := by
    rcases cp.edge_stabilizers_are_P with hedge | hedge
    · rw [show P = P1 from hedge.1, show Pb = P2 from hedge.2, ctx.sectionSeven.generated]
    · rw [show P = P2 from hedge.1, show Pb = P1 from hedge.2, sup_comm, ctx.sectionSeven.generated]
  have hQN : Q.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hcover]
    exact sup_le hPQ hPbQ
  have hQp : IsPGroup 2 Q := by
    rw [show Q = twoCoreIn P from Γ.twoCoreAt_def cp.a]
    exact (pCore_isPGroup (p := 2) (G := P)).map P.subtype
  have hQbot : Q = ⊥ := le_bot_iff.mp
    ((show Q ≤ pCore 2 H from le_sSup ⟨hQN, hQp⟩).trans_eq h.twoCore_eq_bot)
  have hPset := (SevenSix.edge_local_data h Γ cp).1
  apply hPset.1.1.2.2.1
  exact (show Q = twoCoreIn P from Γ.twoCoreAt_def cp.a).symm.trans hQbot

end Stellmacher.SectionEight

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_three_action_comparison_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcore : QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a)
    (hcontained : QAt ctx.Γ ctx.criticalPath.a ≤ QAt ctx.Γ ctx.criticalPath.firstStep) :
    baumannIn S ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  classical
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Pb := stabilizer Γ cp.firstStep
  let Q := q Γ cp.a
  let TA := q Γ cp.firstStep
  let T := TA.subgroupOf P
  have hloc := (SevenSix.edge_local_data h Γ cp).1
  have hPset := (pFamily_iff_pSet _ _ _).mp hloc.1
  obtain ⟨hSP,U,hU⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hUS : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  have hUne : (U : Subgroup P) ≠ ⊥ := by
    intro hb
    apply h.S_nontrivial
    rw [← hU,hb,Subgroup.map_bot]
  have heven : Even (Nat.card P) := by
    have hd : 2 ∣ Nat.card U := U.isPGroup'.card_eq_or_dvd.resolve_left
      (fun hc => hUne (Subgroup.card_eq_one.mp hc))
    exact even_iff_two_dvd.mpr (hd.trans (Subgroup.card_subgroup_dvd_card (U : Subgroup P)))
  have hsec : SectionTwo.Hypotheses P :=
    ⟨hloc.2,heven,(SevenSix.edge_characteristic_data h Γ cp).1⟩
  have h3 : SectionThree.Hypotheses P (U : Subgroup P) := ⟨heven,hUne,U.isPGroup'⟩
  have hcoreNe : pCore 2 P ≠ ⊥ := by
    intro hb
    apply hPset.1.2.2.1
    change (pCore 2 P).map P.subtype = ⊥
    rw [hb,Subgroup.map_bot]
  have hUneCore : (U : Subgroup P) ≠ pCore 2 P := by
    intro he
    apply hPset.1.2.2.2
    exact hU.symm.trans (congrArg (fun A : Subgroup P => A.map P.subtype) he)
  have huniq : IsUniqueMaximalContaining (U : Subgroup P) (⊤ : Subgroup P) :=
    native_uniqueMaximalContaining P (U : Subgroup P) (by rw [hU]; exact hPset.2)
  have hnative : (⊤ : Subgroup P) ∈ SectionThree.PSet ⊤ (U : Subgroup P) := by
    have hh := pFamily_range_of_injective (MonoidHom.id P) Function.injective_id U
      (U : Subgroup P) (Subgroup.map_id _) hcoreNe hUneCore huniq
    rw [(MonoidHom.id P).range_eq_top_of_surjective Function.surjective_id,pFamily_iff_pSet] at hh
    exact hh
  let V := SectionTwo.vSubgroup U
  have hVmap : V.map P.subtype = z Γ cp.a := vertexZ_eq_local_vSubgroup Γ cp.a U
  have hQmap : (pCore 2 P).map P.subtype = Q := (Γ.twoCoreAt_def cp.a).symm
  have hVcore : V = pCore 2 P := by
    apply Subgroup.map_injective P.subtype_injective
    exact hVmap.trans (hcore.symm.trans hQmap.symm)
  let _ : IsElementaryAbelian 2 V := (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian hsec U).2
  let _ : IsMulCommutative (pCore 2 P) := hVcore ▸ (inferInstance : IsMulCommutative V)
  have hCV : SectionTwo.cSubgroup U = pCore 2 P := by
    change Subgroup.centralizer (V : Set P) = pCore 2 P
    rw [hVcore]
    exact le_antisymm hsec.centralizer_twoCore_le
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
  let π := QuotientGroup.mk' (pCore 2 P)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = SectionTwo.cSubgroup U := by rw [QuotientGroup.ker_mk', hCV]
  have hTS : TA ≤ S := (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hTP : TA ≤ P := hTS.trans hSP
  have hTmap : T.map P.subtype = TA := Subgroup.map_subgroupOf_eq_of_le hTP
  have hTU : T ≤ (U : Subgroup P) := by rw [hUS]; exact Subgroup.subgroupOf_mono P hTS
  have hVT : V ≤ T := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [hVmap,hTmap]
    exact hcore.symm.le.trans hcontained
  have hCT : π.ker ≤ T := by rw [hker,hCV,← hVcore]; exact hVT
  have hSPb : S ≤ Pb := (SevenSix.edge_sylow_data h Γ cp).2.1
  have hPbT : Pb ≤ Subgroup.normalizer (TA : Set H) := by
    rw [show TA = twoCoreIn Pb from Γ.twoCoreAt_def cp.firstStep]
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hUnT : (U : Subgroup P) ≤ Subgroup.normalizer (T : Set P) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro s hs t ht
    have hsS : (s : H) ∈ S := by
      exact hU.le (Subgroup.mem_map_of_mem P.subtype hs)
    exact Subgroup.le_normalizer_iff.mp hPbT (s : H) (hSPb hsS) t ht
  have hJn : ((elementaryAbelianMaxJ T).subgroupOf (U : Subgroup P)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((sSup_le fun _ ha => ha.1).trans hTU)).mpr
    intro s hs
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (elementaryAbelianMaxJ T).map (MulAut.conj s).toMonoidHom = elementaryAbelianMaxJ T
    rw [← elementaryAbelianMaxJ_map_equiv]
    have ht : T.map (MulAut.conj s).toMonoidHom = T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hUnT hs)
    rw [ht]
  have hJmap : (elementaryAbelianMaxJ T).map P.subtype = elementaryAbelianMaxJ TA := by
    rw [← elementaryAbelianMaxJ_map_injective P.subtype P.subtype_injective,hTmap]
  have hJnot : ¬ elementaryAbelianMaxJ T ≤ pCore 2 P := by
    intro hc
    apply eight_three_thompson_not_le_core_local ctx hcore hcontained
    have hm := Subgroup.map_mono (f := P.subtype) hc
    rwa [hJmap,hQmap] at hm
  have hTop : twoCoreAmbient (⊤ : Subgroup P) = pCore 2 P :=
    pCore_map_iso 2 (Subgroup.topEquiv : (⊤ : Subgroup P) ≃* P)
  have hnot : ¬ elementaryAbelianMaxJ T ≤ twoCoreAmbient (⊤ : Subgroup P) := by
    rwa [hTop]
  have hoddQ := SectionThree.odd_card_twoResidual_of_core_quotient
    (U : Subgroup P) h3 hnative hsec.solvable π hπ (QuotientGroup.ker_mk' _)
  have hodd : Odd (Nat.card ((twoResidualAmbient (⊤ : Subgroup P)).map π)) := by
    rw [map_twoResidualAmbient_of_subgroup_image ⊤ π ⊤ (Subgroup.map_top_of_surjective π hπ)]
    exact hoddQ
  let _ := SectionTwo.quotientConjugationAction U π hπ hker
  have hJTne : (elementaryAbelianMaxJ T).map π ≠ ⊥ := by
    intro hb
    apply hJnot
    simpa only [π,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hb
  let Ub := U.mapSurjective hπ
  have hUbne : (Ub : Subgroup (P ⧸ pCore 2 P)) ≠ ⊥ := by
    intro hb
    apply hJTne
    exact bot_unique ((Subgroup.map_mono ((sSup_le fun _ ha => ha.1).trans hTU)).trans_eq hb)
  have h2 : 2 ∣ Nat.card Ub := Ub.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hc => hUbne (Subgroup.card_eq_one.mp hc))
  let _ : Group.IsSolvable P := hsec.solvable
  have hOne : SectionOne.Hypotheses (P ⧸ pCore 2 P) V :=
    ⟨Group.isSolvable_of_surjective hπ,
      even_iff_two_dvd.mpr
        (h2.trans (Subgroup.card_subgroup_dvd_card (Ub : Subgroup (P ⧸ pCore 2 P)))),
      SectionTwo.quotientConjugationAction_faithful U π hπ hker,
      SectionTwo.lemma_two_one hsec U π hπ hker⟩
  let B := (U : Subgroup P) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (U : Subgroup P)) : Set P)
  have hBT := SectionTwo.baumann_le_of_thompson_residual hsec U h3 hnative π hπ hker
    B T rfl hTU hVT hCT hJn hnot hodd hOne
  have hBmap : B.map P.subtype = baumannIn S := by
    rw [baumann_map_injective P.subtype P.subtype_injective,hU]
    rfl
  have hm := Subgroup.map_mono (f := P.subtype) hBT
  rwa [hBmap,hTmap] at hm

end Stellmacher.SectionEight
