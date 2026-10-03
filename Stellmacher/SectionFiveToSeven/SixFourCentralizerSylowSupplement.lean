module
public import Stellmacher.SectionFiveToSeven.SixFourGeneratingResidual
public import Stellmacher.SectionFiveToSeven.SixFourFixingFactor
public import Stellmacher.SectionFiveToSeven.FiveTwoInitialReductions
public import Stellmacher.SectionThree.SubnormalOddQuotient
public import Stellmacher.CentralizerInvolutionCore
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# The Sylow-controlled centralizer supplement in Stellmacher (6.4)

Under the central-action branch of Hypothesis Two, let w be a vector of
the canonical Section Six module fixed by the full preimage of nontrivial
barred J and outside Ω₁(Z(S)). If C_{P₂}(w) and S generate P₂, there is
a subgroup C of that centralizer with Sylow subgroup C_S(w) and C join S=P₂.
The witness is allowed to be smaller than the full centralizer.

The fixing-factor theorem gives B(S) ≤ T=C_S(w), and the elementary native
module puts the nonidentity involution w in S. Thus the full centralizer
has nontrivial two-core. Extract a generating residual K inside it using
an actual Sylow overgroup of T, with K=[K,B(S)] and T normalizing K.
The central action forces alternative (5.1)(b), so S is the ambient Sylow
and P₂ has the PStar property. The initial reductions of (5.2) make K
subnormal in O²(P₂). Subnormal core monotonicity puts O₂(K) in O₂(P₂),
hence in S and therefore in T. The subnormal quotient theorem makes
K/O₂(K) odd. Relative-index transfer now makes T Sylow in K join T,
which still generates P₂ together with S.

This justifies the local-factor selection on journal p.32 of Stellmacher
(6.4) without asserting that C_S(w) is Sylow in the full centralizer.
Source: `refs/files/stellmacher-n-group.pdf`, Journal of Algebra 190 (1997),
pp.31–32. The original ambient group, barred action and generated join are
preserved; the smaller supplement is an intermediate proof construction.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

public theorem sixFour_centralizer_sylow_supplement
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ = ⊥)
    (hJ : sectionSixBarredCritical h ≠ ⊥) (w : H)
    (hwV : w ∈ sectionSixV S P1)
    (hwJ : w ∈ Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H))
    (hwZ : w ∉ omegaOneCenter S)
    (hgen : P2 = sectionSixCentralizerJoin P2 S w) :
    ∃ C : Subgroup H,
      C ≤ P2 ⊓ Subgroup.centralizer ({w} : Set H) ∧
      IsSylowTwoIn (S ⊓ Subgroup.centralizer ({w} : Set H)) C ∧
      C ⊔ S = P2 := by
  classical
  have hZP : omegaOneCenter S ≤ P2 :=
    (Subgroup.map_subtype_le _).trans h.fiveOne.P2_mem.1.2.1.1
  have hZn : NormalIn (omegaOneCenter S) P2 := by
    refine ⟨hZP, (Subgroup.normal_subgroupOf_iff_le_normalizer hZP).mpr ?_⟩
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcase : S = (S0 : Subgroup H) ∧ P2 ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter S : Set H)) S := by
    cases h.fiveOne.alternative with
    | a _ _ hn => exact (hn hZn).elim
    | b hS hstar => exact ⟨hS,hstar⟩
    | c _ _ _ _ hn _ _ _ _ _ _ _ _ => exact (hn hZn).elim
  obtain ⟨hS,hstar⟩ := hcase
  let C := P2 ⊓ Subgroup.centralizer ({w} : Set H)
  let T := S ⊓ Subgroup.centralizer ({w} : Set H)
  have hTC : T ≤ C := inf_le_inf_right _ h.fiveOne.P2_mem.1.2.1.1
  have hCS : C ⊔ S = P2 := by
    simpa only [sectionSixCentralizerJoin, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure] using hgen.symm
  have hsetup := sectionSix_barred_action_setup h
  obtain ⟨vector,hvector,hvectorEq⟩ := Subgroup.mem_map.mp (hsetup.localV_image.ge hwV)
  let v : sectionSixLocalV h := ⟨vector,hvector⟩
  have hveq : ((v : P1) : H) = w := hvectorEq
  have hvJ : ((v : P1) : H) ∈ Subgroup.centralizer
      (sectionSixBarredCriticalPreimage h : Set H) := by
    rw [hveq]
    exact hwJ
  have hvZ : ((v : P1) : H) ∉ omegaOneCenter S := by
    rw [hveq]
    exact hwZ
  have hBT : baumannIn S ≤ T := by
    have hx := (sixFour_canonical_fixing_factor h hJ v hvJ hvZ).1
    rw [hveq] at hx
    exact hx
  let SP := sectionSixSylow h
  obtain ⟨hsol,hchar,_⟩ := lemma_five_three S0 S P1 P2 h
  have hSPne : (SP : Subgroup P1) ≠ ⊥ := by
    intro hbot
    apply h.fiveOne.S_nontrivial
    rw [← hsetup.sylow_image, show (sectionSixSylow h : Subgroup P1) = ⊥ from hbot,
      Subgroup.map_bot]
  have hdvd : 2 ∣ Nat.card SP := SP.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hc => hSPne (Subgroup.card_eq_one.mp hc))
  have hsec : SectionTwo.Hypotheses P1 :=
    ⟨hsol, even_iff_two_dvd.mpr (hdvd.trans (SP : Subgroup P1).card_subgroup_dvd_card),hchar⟩
  have hVdata := SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian hsec SP
  let _ : IsElementaryAbelian 2 (sectionSixLocalV h) := hVdata.2
  have hw2 : w ^ 2 = 1 := by
    rw [← hvectorEq]
    exact congrArg P1.subtype
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := sectionSixLocalV h) vector hvector)
  have hwS : w ∈ S := by
    rw [← hvectorEq]
    exact hsetup.sylow_image.le (Subgroup.mem_map_of_mem P1.subtype
      ((hVdata.1.trans ((pCore_isPGroup (p := 2) (G := P1)).le_sylow_of_normal SP)) hvector))
  have hwne : w ≠ 1 := fun he => hwZ (he ▸ (omegaOneCenter S).one_mem)
  have hwC : w ∈ C := ⟨h.fiveOne.P2_mem.1.2.1.1 hwS,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hcore : twoCoreIn C ≠ ⊥ :=
    centralizer_twoCore_ne_bot C w hwC inf_le_right hw2 hwne
  obtain ⟨K,hKC,hKB,hKS,hTK⟩ := sixFour_generating_residual h hS C T
    inf_le_left hBT hTC inf_le_left hCS hcore
  have hKP : K ≤ P2 := hKC.trans inf_le_left
  have hstar0 : P2 ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter (S0 : Subgroup H) : Set H))
      (S0 : Subgroup H) := hS ▸ hstar
  have hlocal0 : ∀ U : Subgroup H, IsTwoLocal U → baumannIn (S0 : Subgroup H) ≤ U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U := hS ▸ h.local_B
  have hKB0 : K = ⁅K, baumannIn (S0 : Subgroup H)⁆ := hS ▸ hKB
  have hred := five_two_initial_reductions S0 P2 K hstar0 hKP hlocal0 hKB0
  have hKsub : IsSubnormalIn K (twoResidualAmbient P2) := hred.2.2.1
  obtain ⟨p,hp,hp2,hpK⟩ := SectionThree.subnormal_quotient_twoCore_is_odd_pGroup S
    h.sectionThreeHypotheses P2 ((pFamily_iff_pSet ⊤ S P2).mp h.fiveOne.P2_mem)
    hred.1 K hKsub
  have hodd : Odd (Nat.card (K ⧸ pCore 2 K)) := by
    let _ : Fact p.Prime := ⟨hp⟩
    obtain ⟨n,hn⟩ := hpK.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hRnormal : ((twoResidualAmbient P2).subgroupOf P2).Normal := by
    dsimp only [twoResidualAmbient]
    rw [subgroupOf_map_subtype_eq]
    unfold twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal fun N => Subgroup.normal_iInf_normal fun hN => hN.1
  have hKcoreS : (pCore 2 K).map K.subtype ≤ S := by
    have ha := pCoreAmbient_mono_of_isSubnormalIn K (twoResidualAmbient P2) 2 hKsub.1 hKsub.2
    have hb := pCoreAmbient_mono_of_isSubnormalIn (twoResidualAmbient P2) P2 2
      (Subgroup.map_subtype_le _) hRnormal.isSubnormal
    obtain ⟨_,U,hU⟩ := h.fiveOne.P2_mem.1.2.1
    exact (ha.trans hb).trans (hU ▸ Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := P2)).le_sylow_of_normal U))
  have hKcoreT : (pCore 2 K).map K.subtype ≤ T := le_inf hKcoreS
    ((Subgroup.map_subtype_le _).trans (hKC.trans inf_le_right))
  have hTp : IsPGroup 2 T := (hS ▸ S0.isPGroup').to_le inf_le_left
  have hindex : ¬ 2 ∣ (pCore 2 K).index := by
    rw [Subgroup.index_eq_card]
    exact hodd.not_two_dvd_nat
  obtain ⟨U,hU⟩ := IsPGroup.exists_sylow_sup_of_coprime_index K T hTp hTK
    (pCore 2 K) hindex hKcoreT
  refine ⟨K ⊔ T, sup_le hKC hTC, ⟨le_sup_right,U,hU⟩, ?_⟩
  rw [sup_assoc, sup_eq_right.mpr (show T ≤ S from inf_le_left), hKS]

end Stellmacher.SectionsFiveToSeven
