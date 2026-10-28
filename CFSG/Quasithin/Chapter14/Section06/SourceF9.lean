module
public import CFSG.Quasithin.Chapter14.Section02.RankTwoLocal
public import CFSG.Quasithin.Chapter14.Section06.SourceCentrality
public import CFSG.Quasithin.ChapterF.Section09.Basic
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PPerfectHom

/-!
# The actual F.9 input and moved central line in the abelian plane branch

The original rank-two setup supplies the plane action, its faithful kernel,
the flag and the local characteristic-two groups. Abelian closure in Mc makes
the F.9 commutator-lifting condition immediate on the same conjugate spans.
The normal core of the point-action kernel is the already proved local tilde
kernel. Thus all F.9.1 hypotheses are constructed from the original source
data and the abelian-closure assumption of Hypothesis 14.5.1.

For 14.6.2, a nontrivial two-perfect subgroup X of the generalized-Fitting
preimage cannot centralize the local span, since its centralizer lies in the
two-core. If the moved space centralizes that core, source 14.6.1(5) and
two-perfect commutator idempotence force it to vanish. Its nonzero commutator
with the core therefore contains the original central subgroup of order two.

Source: Aschbacher--Smith, Hypothesis 14.5.1 and Lemmas 14.5.15, 14.6.1(5),
14.6.2, printed pp.1013, 1017, 1020--1021; F.9.1--2, pp.317--318.
The abelian reduction 14.3.16 and the subsequent 14.6.3--25 argument remain
separate source obligations.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]
  {K : GroupClass} {T : Sylow 2 G} {L M H : Subgroup G}

private theorem rankTwo_f9_hypothesis (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    (hH : H ∈ F.Hz L M) (hab : IsMulCommutative F.U) :
    ChapterF.Section09.Setup.Hypothesis
      { T := T, L := L, V := rankTwoSeed T M, Vplus := rankTwoSeed T M,
        V₁ := F.Vi 1, H := H } := by
  let V := rankTwoSeed T M
  let J := L ⊔ (T : Subgroup G)
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V,F.Vi 1,H⟩
  let := rankTwoSeed_elementary h
  let := hab
  have hVJ : V ≤ J := h.seed_le_sylow.trans le_sup_right
  have hNV : J ≤ normalizer (V : Set G) :=
    (sup_le h.L_le h.sylow_le).trans RankTwoHypothesis.M_normalizes_seed
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hVH : V ≤ H := h.seed_le_sylow.trans hTH
  have hnat : 3 ≤ 2 → Nonempty (InvariantFlag.AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  have hg := F.localKernel_hypothesis h.simpleQTKE L M H (by decide) h.seed_le_sylow
    h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat hH
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hHC : H ≤ centralizer (F.Vi 1 : Set G) := hH.2.1.trans
    (normalizer_le_centralizer_of_card_two _ hp)
  have hLC : D.L₁ = F.Li L 1 := by
    change (pResidual 2 (L ⊓ centralizer (F.Vi 1 : Set G) : Subgroup G)).map
      (L ⊓ centralizer (F.Vi 1 : Set G)).subtype = _
    have he : centralizer (F.Vi 1 : Set G) = normalizer (F.Vi 1 : Set G) :=
      le_antisymm (Subgroup.centralizer_le_normalizer _) (normalizer_le_centralizer_of_card_two _ hp)
    simp only [InvariantFlag.Li, InvariantFlag.Gi]
    norm_num
    exact congrArg (fun A : Subgroup G => (pResidual 2 (L ⊓ A : Subgroup G)).map
      (L ⊓ A).subtype) he
  have hk : centralizer (V.subgroupOf J : Set J) = pCore 2 J := by
    apply map_injective J.subtype_injective
    have he : (centralizer (V.subgroupOf J : Set J)).map J.subtype =
        J ⊓ centralizer (V : Set G) := by
      ext x
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact ⟨x.property,fun v hv => congrArg Subtype.val (hx ⟨v,hVJ hv⟩ hv)⟩
      · rintro ⟨hx,hc⟩
        exact ⟨⟨x,hx⟩,fun v hv => Subtype.ext (hc v hv),rfl⟩
    rw [he]
    exact h.centralizer
  have hred : IsPReduced 2 (V.subgroupOf J) := by
    let hn : (V.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hNV
    refine ⟨hn, IsElementaryAbelian.subgroupOf hVJ, ?_⟩
    let q := QuotientGroup.quotientMulEquivOfEq hk
    have he := pCore_map_iso 2 q
    rw [pCore_quotient_pCore_eq_bot] at he
    exact (Subgroup.map_eq_bot_iff_of_injective _ q.injective).mp he
  have hcharL : generalizedFitting L = pCore 2 L := by
    let := h.L_normal
    apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe h.L_le)).mp
      (normal_core_selfCentralizing
        (h.simpleQTKE.evenCharacteristic T M h.maximal h.sylow_le) (L.subgroupOf M))
  have hker : (F.localTildeAction H hH.2.1).ker = pCore 2 H :=
    F.localKernel_eq_pCore h.simpleQTKE L M H (by decide) h.seed_le_sylow
      h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat
      h.M_eq_normalizer h.unique h.seed_centralizer_le h.centralizer_L hH
  refine {
    elementary := inferInstance
    residual := h.L_residual
    normalizes_L := h.sylow_normalizes_L
    characteristic_L := hcharL
    V_le_LT := hVJ
    reduced := hred
    sylow_centralizer := ?_
    point_card := hp
    normalizes_point := F.invariant 1
    point_lt := lt_of_le_of_ne (F.le_seed 1) hg.quotient_nonzero
    plus_le := le_rfl
    H_centralizes := hHC
    local_le := ?_
    characteristic_H := hg.characteristic_two
    kernel_core := ?_
    local_normalizes := ?_
    irreducible := ?_
    normalizer_control := le_rfl
    generated_core := ?_
    commutator_lifting := ?_ }
  · apply le_antisymm
    · exact (le_inf (inf_le_left.trans le_sup_right) inf_le_right).trans h.centralizer.le
    · exact le_inf
        ((pCoreIn_le_sylow J (T.subtype le_sup_right)).trans_eq (map_subgroupOf_eq_of_le le_sup_right))
        (h.centralizer.ge.trans inf_le_right)
  · change D.L₁ ⊔ (T : Subgroup G) ≤ H
    rw [hLC]
    exact sup_le (fun x hx => hH.1.2 (Or.inl hx)) hTH
  · let : ((F.Vi 1).subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer (hHC.trans (Subgroup.centralizer_le_normalizer _))
    rw [←centralizerModulo_conjugateSpanBy_eq_normalCore V H (F.Vi 1) hVH]
    intro x hx
    rw [←hker]
    apply (F.mem_localTildeAction_ker_iff H hH.2.1 x).mpr
    have hc := (mem_centralizerModulo_iff.mp hx).2
    intro a ha
    have hh := hc ⟨a,conjugateSpanBy_le_self hVH ha⟩ ha
    have hi : ⁅a,(x : G)⁆ ∈ F.Vi 1 := hh
    simpa only [commutatorElement_inv] using (F.Vi 1).inv_mem hi
  · change D.L₁ ⊔ (T : Subgroup G) ≤ normalizer (V : Set G)
    rw [hLC]
    exact sup_le ((F.Li_le L 1).trans (inf_le_left.trans h.L_normalizes_seed))
      (h.sylow_le.trans RankTwoHypothesis.M_normalizes_seed)
  · intro W hpW hWV hn
    apply F.localKernel_irreducible L (by decide) h.L_normalizes_seed hnat W hpW hWV
    rw [←hLC]
    exact le_sup_left.trans hn
  · exact sup_twoCore_eq_bot_of_unique J H M (fun N hN hJN =>
      Set.mem_singleton_iff.mp (h.unique ▸ ⟨hN,hJN⟩)) hH.2.2
  · intro g hg' _ _ _
    have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
    have hVgU : V.map (MulAut.conj g).toMonoidHom ≤ F.U := by
      rintro x ⟨v,hv,rfl⟩
      exact subset_closure ⟨g,hH.2.1 hg',v,hv,rfl⟩
    have hc : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        (hVU.trans ((le_centralizer_iff_isMulCommutative.mpr hab).trans (centralizer_le hVgU)))
    exact ⟨hc,by simpa only [commutator_comm] using hc⟩

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- All F.9.1 hypotheses on the original plane, residual, point and outside subgroup. -/
theorem source_rankTwo_f9_hypothesis
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) :
    ChapterF.Section09.Setup.Hypothesis
      { T := T, L := sourceResidual M Mc, V := localModule T M,
        Vplus := localModule T M, V₁ := centralInvolutions T, H := H } := by
  let h := Section02.source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨he,F,hp,_,hHz,_⟩ :=
    Section02.source_lemma_14_2_6 hG T hempty hM hu hmany hcard e
  let := he
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFH : F.H = Mc := by
    change normalizer (F.Vi 1 : Set G) = Mc
    rw [hp,hMc]
    exact le_antisymm (normalizer_le_centralizer_of_card_two _
      (plane_centralInvolutions_card T M hM.1.2 hcard e)) (Subgroup.centralizer_le_normalizer _)
  have habF : IsMulCommutative F.U := by
    change IsMulCommutative (conjugateSpanBy (rankTwoSeed T M) F.H)
    rw [hFH,Section02.rankTwoSeed_eq_localModule]
    exact hab
  simpa only [Section02.rankTwoSeed_eq_localModule,hp] using
    rankTwo_f9_hypothesis h F (hHz.symm ▸ hH) habF

private theorem point_le_moved_space
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH] (X : Subgroup G)
    (hX : X ≤ D.H) (hp : IsPPerfect 2 X) (hne : X ≠ ⊥)
    (hQX : D.QH ≤ normalizer (X : Set G))
    (hcent : X ≤ centralizer (omegaOneCenterAmbient D.QH : Set G)) :
    D.V₁ ≤ ⁅D.UH,X⁆ := by
  let W := ⁅D.UH,X⁆
  have hnU : D.H ≤ normalizer (D.UH : Set G) := le_normalizer_conjugateSpanBy _ _
  have hWU : W ≤ D.UH := le_normalizer_iff_commutator_le_left.mp (hX.trans hnU)
  have hWQ : W ≤ D.QH := hWU.trans h.UH_le_QH
  have hQW : D.QH ≤ normalizer (W : Set G) := by
    intro q hq
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅D.UH,X⁆).map (MulAut.conj q).toMonoidHom = _
    rw [map_commutator]
    have hu : D.UH.map (MulAut.conj q).toMonoidHom = D.UH :=
      mem_normalizer_iff_map_conj_eq.mp (hnU (pCoreIn_le 2 D.H hq))
    have hx : X.map (MulAut.conj q).toMonoidHom = X :=
      mem_normalizer_iff_map_conj_eq.mp (hQX hq)
    rw [hu,hx]
  have hWne : W ≠ ⊥ := by
    intro hz
    have hXC : X ≤ centralizer (D.UH : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
    have hXQ : X ≤ D.QH := by
      rw [←h.kernel_UH_eq_QH]
      intro x hx
      exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨hX hx,fun a ha => by
        rw [commutatorElement_eq_one_iff_mul_comm.mpr (hXC hx a ha)]
        exact D.V₁.one_mem⟩
    have hh := hp.hom_eq_one_of_isPGroup (pCore_isPGroup.map D.H.subtype) (inclusion hXQ)
    apply hne
    apply eq_bot_iff.mpr
    intro x hx
    exact congrArg Subtype.val (DFunLike.congr_fun hh ⟨x,hx⟩)
  have hcommne : ⁅W,D.QH⁆ ≠ ⊥ := by
    intro hz
    have hWomega : W ≤ omegaOneCenterAmbient D.QH := by
      intro w hw
      exact (mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨hWQ hw,elemPow_eq_one_of_isElementaryAbelian w (hWU hw),
          (commutator_eq_bot_iff_le_centralizer.mp hz) hw⟩
    have hbot : ⁅W,X⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hcent.trans (centralizer_le hWomega)))
    exact hWne ((commutator_isPPerfect_idempotent X D.UH hp
      (IsElementaryAbelian.isPGroup 2 _) (hX.trans hnU)).symm.trans hbot)
  have hAZ : ⁅W,D.QH⁆ ≤ D.V₁ :=
    (commutator_mono hWU le_rfl).trans h.commutator_UH_QH_le_point
  have hAW : ⁅W,D.QH⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp hQW
  have hc : Nat.card (⁅W,D.QH⁆ : Subgroup G) = 2 := by
    have hd : Nat.card (⁅W,D.QH⁆ : Subgroup G) ∣ 2 := by simpa only [h.point_card] using card_dvd_of_le hAZ
    exact (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left (fun he => hcommne (card_eq_one.mp he))
  have he : ⁅W,D.QH⁆ = D.V₁ := eq_of_le_of_card_ge hAZ (by rw [hc,h.point_card])
  exact he ▸ hAW
/-- Original 14.6.2 with its action kernel and generalized-Fitting centrality discharged. -/
theorem source_lemma_14_6_2
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (X : Subgroup G) (hX : X ≤ ChapterA.Section04.twoGeneralizedFittingPreimage H)
    (hp : IsPPerfect 2 X) (hne : X ≠ ⊥)
    (hQX : H.pCoreIn 2 ≤ normalizer (X : Set G)) :
    centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) H,X⁆ := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  have h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH
  have hHZ := (Section02.source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1 hH.2).2
  have hHMc : H ≤ Mc := by
    have huniq := (Section02.source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1 hH.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from huniq ▸ Set.mem_singleton Mc).2
  let := h.elementary
  let := hab
  let : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc) :=
    conjugateSpanBy_elementary_of_commutative _ _
  let : IsElementaryAbelian 2 D.UH :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hHMc)
  exact point_le_moved_space h X (hX.trans (map_subtype_le _)) hp hne hQX
    (hX.trans (source_generalizedFittingPreimage_centralizes_omegaCore hG T hempty hH hHZ))

end CFSG.Quasithin.Chapter14.Section06

