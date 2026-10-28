module
public import CFSG.Quasithin.Chapter14.Section06.SourceF9
public import CFSG.Quasithin.Chapter14.Section06.MaximalOvergroups
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Ambient
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Constructions
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

public import Theory.GroupTheory.OddCoreFourCentralization
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.SourceInputs
public import Theory.GroupTheory.PerfectSmallTwoAction

/-!
# The original suitable-involution intersection and odd core

The F.9 source setup at Mc puts the whole abelian plane closure inside O₂(Mc).
Consequently the suitable involution belongs to O₂(I ∩ Mc), and its centralizer
inside O₂(Mc) lies in the original Tᵤ ≤ I. The central involution of the ambient
Sylow subgroup then supplies every hypothesis of 1.1.5 on the literal
intersection, giving F*(I ∩ Mc) = O₂(I ∩ Mc).

The original L-transitivity on the plane transports V ≤ O₂(Mc) to
V ≤ O₂(C_G(v)) for every v in V#. Coprime four-group fixed-point generation
therefore makes O(I) centralize V. It lies in Mc and is trivial by the already
proved characteristic-two intersection. The Sylow witness is precisely the
one furnished by 14.6.6; maximality in the outside family is unnecessary for
these first three conclusions.

Every component escapes the characteristic-two intersection. A component in M
would centralize the normal four-group V by the existing perfect-action theorem,
so it escapes M as well. Its join with the original Sylow intersection retains
the nontrivial two-core of I, and 14.6.4 gives the required maximal intersection.

Source: Aschbacher–Smith, 14.6.7, printed p.1024 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem source_intersection_data
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I) :
    ∃ z, z ∈ centralInvolutions T ∧ Chapter1.Lemma115Hypotheses I S Mc z ∧
      localModule T M ≤ I ∧
      ∀ v ∈ localModule T M, v ≠ 1 →
        localModule T M ≤ (centralizer ({v} : Set G)).pCoreIn 2 := by
  let V := localModule T M
  let U := conjugateSpanBy V Mc
  let h := Section02.source_lemma_14_2_4 hG T hempty hM hunique hmany hcard e
  have hZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,hne,hMc,hpair⟩ :=
    plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard hZ
  have hMcMax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).1
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [hMc]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  have hMcOutside : Mc ∈ Chapter1.HOutside G (T : Set G) (M : Set G) :=
    ⟨⟨Chapter1.mem_H_of_isTwoLocal hMcMax.1,hTMc⟩,
      fun hh => hne (hMcMax.eq_of_le hM.1.1.1 hh).symm⟩
  have hUMc : U ≤ Mc.pCoreIn 2 :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab Mc
      hMcOutside).UH_le_QH
  have hQMcT : Mc.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] using
      pCoreIn_le_sylow Mc (T.subtype hTMc)
  have hHMc : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
      H hH.1 hH.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  have huU : u ∈ U := (conjugateSpanBy_mono le_rfl hHMc) hu
  have hVU : V ≤ U := le_conjugateSpanBy _ _
  have hVT : V ≤ (T : Subgroup G) := hVU.trans (hUMc.trans hQMcT)
  have hZV : centralInvolutions T ≤ V := le_conjugateSpanBy _ _
  let := hab
  have hVTu : V ≤ (T : Subgroup G) ⊓ centralizer ({u} : Set G) := by
    intro v hv
    refine ⟨hVT hv,?_⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg U.subtype (mul_comm (⟨v,hVU hv⟩ : U) ⟨u,huU⟩))
  have hVI : V ≤ I := hVTu.trans hI.2.1
  have huI : u ∈ I :=
    hI.2.1 ⟨hUMc.trans hQMcT huU,mem_centralizer_singleton_iff.mpr rfl⟩
  have huQ : u ∈ (I ⊓ Mc).pCoreIn 2 :=
    inf_pCoreIn_le_of_le 2 inf_le_right ⟨⟨huI,pCoreIn_le 2 Mc (hUMc huU)⟩,hUMc huU⟩
  have hcore : Mc.pCoreIn 2 ⊓ centralizer ((I ⊓ Mc).pCoreIn 2 : Set G) ≤ I := by
    intro g hg
    apply hI.2.1
    refine ⟨hQMcT hg.1,?_⟩
    exact mem_centralizer_singleton_iff.mpr (hg.2 u huQ).symm
  obtain ⟨z,hz,hz2,hzg⟩ := Nonabelian.Fusion.exists_generator_of_card_two
    (centralInvolutions T) hZ
  have hzC : centralizer ({z} : Set G) = Mc := by
    rw [hMc,←hzg,zpowers_eq_closure,centralizer_closure]
  have h115 : Chapter1.Lemma115Hypotheses I S Mc z := by
    refine ⟨hI.1,?_,hcore,hz2,?_,?_,hzC.le⟩
    · refine ⟨Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T Mc hMcMax hTMc),
        Chapter1.mem_H_of_isTwoLocal hMcMax.1,?_⟩
      rw [hS]
      exact inf_le_left.trans hTMc
    · rw [hS]
      exact ⟨hVT (hZV hz),hVI (hZV hz)⟩
    · intro s hs
      rw [hS] at hs
      exact centralInvolutions_le_centralizer_sylow T hz s hs.1
  refine ⟨z,hz,h115,hVI,?_⟩
  intro v hv hvne
  have hzne : z ≠ 1 := by intro he; rw [he,orderOf_one] at hz2; omega
  obtain ⟨l,hl,hlz⟩ := h.nonidentity_transitive z v
    (by simpa only [Section02.rankTwoSeed_eq_localModule] using hZV hz)
    (by simpa only [Section02.rankTwoSeed_eq_localModule] using hv) hzne hvne
  have hlN : l ∈ normalizer (V : Set G) := by
    simpa only [Section02.rankTwoSeed_eq_localModule] using h.L_normalizes_seed hl
  have hVcore : V ≤ Mc.pCoreIn 2 := hVU.trans hUMc
  have hVmap : V.map (MulAut.conj l).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp hlN
  have hm := Subgroup.map_mono (f := (MulAut.conj l).toMonoidHom) hVcore
  rw [hVmap,map_pCoreIn_of_injective 2 Mc _
    (MulAut.conj l).injective,←hzC,
    CentralizerSmallKernelTransport.map_centralizer (MulAut.conj l)] at hm
  exact hlz ▸ hm


/-- Original 14.6.7(1–3), with the actual Sylow intersection from 14.6.6.
The marked involution for 1.1.5 is chosen in the original Sylow omega-center;
the suitable involution u supplies the local core-centralizer bound. -/
theorem source_lemma_14_6_7_initial
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I) :
    (∃ z, z ∈ centralInvolutions T ∧ Chapter1.Lemma115Hypotheses I S Mc z) ∧
      generalizedFitting (I ⊓ Mc : Subgroup G) = pCore 2 (I ⊓ Mc : Subgroup G) ∧
      pPrimeCore 2 I = ⊥ := by
  obtain ⟨z,hz,h115,hVI,hlocal⟩ :=
    source_intersection_data hG T hempty hM hunique hmany hcard e hab H hH u hu I hI S hS
  let := InitialSource.localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  have hD := pPrimeCore_map_le_centralizer_of_four_local_cores I (localModule T M)
    hcard hVI hlocal
  have hinside : pPrimeCore 2 I ≤ Mc.subgroupOf I := by
    intro a ha
    apply h115.centralizer_le
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hD (mem_map_of_mem I.subtype ha) z (le_conjugateSpanBy _ _ hz)
  have hbot := congrArg (Subgroup.map (Mc.subgroupOf I).subtype)
    h115.oddCore_intersection_eq_bot
  rw [map_subgroupOf_eq_of_le hinside,Subgroup.map_bot] at hbot
  exact ⟨⟨z,hz,h115⟩,generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp h115.intersection_mem_He),hbot⟩


/-- Original 14.6.7, including the component and maximal-intersection clause. -/
theorem source_lemma_14_6_7
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I) :
    (∃ z, z ∈ centralInvolutions T ∧ Chapter1.Lemma115Hypotheses I S Mc z) ∧
      generalizedFitting (I ⊓ Mc : Subgroup G) = pCore 2 (I ⊓ Mc : Subgroup G) ∧
      pPrimeCore 2 I = ⊥ ∧
      ∀ K : Subgroup I, IsComponent I K →
        ¬ K.map I.subtype ≤ I ⊓ Mc ∧
        K.map I.subtype ⊔ ((T : Subgroup G) ⊓ I) ∈ IStar (T : Subgroup G)
          (outsideOvergroups (Chapter1.H G)
            ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M) := by
  obtain ⟨⟨z,hz,h115⟩,hfit,hodd⟩ :=
    source_lemma_14_6_7_initial hG T hempty hM hunique hmany hcard e hab H hH
      u hu I hI.1 S hS
  refine ⟨⟨z,hz,h115⟩,hfit,hodd,?_⟩
  intro K hK
  let KG := K.map I.subtype
  have hKMc : ¬ KG ≤ Mc := (h115.component_inputs K hK).1
  have hKM : ¬ KG ≤ M := by
    intro hKM
    let V := localModule T M
    let := hK.2
    let : Group.IsPerfect KG := Group.IsPerfect.map I.subtype
    let : Group.IsPerfect (KG.subgroupOf M) := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hKM).symm.toMonoidHom)
      (subgroupOfEquivOfLe hKM).symm.surjective
    let : (V.subgroupOf M).Normal :=
      normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
    have hVM : V ≤ M := localModule_le T hM.1.2
    have hc := le_centralizer_of_isPerfect_of_card_le_four (KG.subgroupOf M)
      (V.subgroupOf M) (by
        rw [Nat.card_congr (subgroupOfEquivOfLe hVM).toEquiv,hcard])
    have hKC : KG ≤ centralizer (V : Set G) := by
      intro k hk v hv
      exact congrArg M.subtype (hc (show (⟨k,hKM hk⟩ : M) ∈ KG.subgroupOf M from hk)
        ⟨v,hVM hv⟩ hv)
    apply hKMc
    intro k hk
    apply h115.centralizer_le
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hKC hk z (le_conjugateSpanBy _ _ hz)
  let J := KG ⊔ ((T : Subgroup G) ⊓ I)
  have hJI : J ≤ I := sup_le (map_subtype_le _) inf_le_right
  have hcoreI : I.pCoreIn 2 ≤ (T : Subgroup G) ⊓ I := by
    rw [←hS]
    exact pCoreIn_le_sylow I S
  have hcoreJ : I.pCoreIn 2 ≤ J.pCoreIn 2 :=
    (le_inf (hcoreI.trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 hJI)
  have hJ : J ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M := by
    refine ⟨?_,?_,?_,?_⟩
    · intro hb
      exact hI.1.1 (bot_unique (hb ▸ hcoreJ))
    · exact (le_inf inf_le_left hI.1.2.1).trans le_sup_right
    · exact fun hh => hKMc (le_sup_left.trans hh)
    · exact fun hh => hKM (le_sup_left.trans hh)
  exact ⟨fun hh => hKMc (hh.trans inf_le_right),
    (lemma14_6_4 hI hJ le_sup_right).1⟩

end CFSG.Quasithin.Chapter14.Section06


