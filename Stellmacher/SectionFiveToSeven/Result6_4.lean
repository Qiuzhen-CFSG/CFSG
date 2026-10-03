module
public import Stellmacher.SectionFiveToSeven.SixFourCentralizerFactor
public import Stellmacher.SectionFiveToSeven.SixFourSelectedModuleContainment
public import Stellmacher.SectionFiveToSeven.SixFourFixedPairCentralization
public import Stellmacher.SectionFiveToSeven.SixFourRepeatModuleTransfer

/-!
# Stellmacher (6.4): canonical barred nongeneration

Under Hypothesis Two, suppose P₂ centralizes Ω₁(Z(S)) and the canonical
faithful quotient of P₁ has nontrivial action-critical subgroup J(V,bar S).
A vector w in V that centralizes the full preimage of this barred subgroup,
but lies outside Ω₁(Z(S)), has C_{P₂}(w) join S different from P₂.

Assume generation. The barred fixing-factor theorem supplies B(S) ≤ C_S(w)
and a raw one-seven factor fixing w. Lift that factor to F₁ and use the
centralizer supplement to select F₂, both with Sylow C_S(w) and both
centralizing the nonidentity involution w. The fixed-pair transfer, using
(5.2), (5.4), and the pair-core normalizer, makes O²(F₂) centralize
[Ω₁(Z(S)),O²(F₁)], hence the selected four-element action module. The
repeated module transfer centralizes the entire original V. Since
F₂=O²(F₂) C_S(w) and F₂ join S=P₂, P₂ normalizes V. The group P₁ already
normalizes V, so the nontrivial two-group V lies in the two-core of the
literal join P₁ join P₂, contradicting Hypothesis Two.

Source: Stellmacher, Journal of Algebra 190 (1997), (6.4), journal pp.31–32,
`refs/files/stellmacher-n-group.pdf`. The journal's barred actor and its
full preimage are retained through the canonical quotient action. The
repository LaTeX transcription omitted these bars; an unquotiented actor
would also include elementary subgroups of the action kernel and therefore
does not express the source hypothesis. The ambient group and generated
join are unchanged throughout.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

/-- **Stellmacher (6.4).** The indicated fixed-vector centralizer does not generate P₂ with S. -/
public theorem lemma_six_four
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (V : Subgroup H) (hV : V = sectionSixV S P1)
    (hcomm : ⁅P2, omegaOneCenter S⁆ = ⊥)
    (hJ : sectionSixBarredCritical h ≠ ⊥) :
    ∀ w : H, w ∈ V →
      w ∈ Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H) →
      w ∉ omegaOneCenter S → P2 ≠ sectionSixCentralizerJoin P2 S w := by
  subst V
  intro w hwV hwJ hwZ hgen
  classical
  let _ := sectionSixQuotientAction h
  have hsetup := sectionSix_barred_action_setup h
  obtain ⟨vector,hvector,hvectorEq⟩ := Subgroup.mem_map.mp (hsetup.localV_image.ge hwV)
  let v : sectionSixLocalV h := ⟨vector,hvector⟩
  have hveq : ((v : P1) : H) = w := hvectorEq
  have hvJ : ((v : P1) : H) ∈ Subgroup.centralizer
      (sectionSixBarredCriticalPreimage h : Set H) := by rw [hveq]; exact hwJ
  have hvZ : ((v : P1) : H) ∉ omegaOneCenter S := by rw [hveq]; exact hwZ
  obtain ⟨hBT,D,hD,hvD⟩ := sixFour_canonical_fixing_factor h hJ v hvJ hvZ
  rw [hveq] at hBT
  obtain ⟨F1,hF1,hF1P,hDF,hF1w⟩ := sixFour_first_factor_lift h hJ v hvJ hvZ D hD hvD
  rw [hveq] at hF1 hF1w
  obtain ⟨F2,hF2,hFS,hFK⟩ := sixFour_centralizer_factor h hcomm hJ w hwV hwJ hwZ hgen
  let T := S ⊓ Subgroup.centralizer ({w} : Set H)
  let K := twoResidualAmbient F2
  have hF1top : F1 ∈ PFamily ⊤ T := ⟨⟨le_top,hF1.1.2⟩,hF1.2⟩
  have hF2top : F2 ∈ PFamily ⊤ T := ⟨⟨le_top,hF2.1.2⟩,hF2.2⟩
  have hF2P : F2 ≤ P2 := hF2.1.1.trans inf_le_left
  have hKP : K ≤ P2 := (Subgroup.map_subtype_le _).trans hF2P
  have hKB : K = ⁅K,baumannIn S⁆ := hFK.symm
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
    ⟨hsol,even_iff_two_dvd.mpr (hdvd.trans (SP : Subgroup P1).card_subgroup_dvd_card),hchar⟩
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
  have hwT : w ∈ T := ⟨hwS,Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hpair := sixFour_fixed_pair_centralization h hcomm T F1 F2 hBT inf_le_left
    hF1top hF2top hF2P w hwT hw2 hwne hF1w (hF2.1.1.trans inf_le_right) hKB
  have hWle := sixFour_selected_module_containment h hJ D hD F1 hF1P hDF
  have hWK : ⁅(commutatorAction D (sectionSixLocalV h)).map
      (P1.subtype.comp (sectionSixLocalV h).subtype),K⁆ = ⊥ :=
    bot_unique ((Subgroup.commutator_mono hWle le_rfl).trans_eq hpair)
  have hKS : K ⊔ S = P2 := by
    calc
      K ⊔ S = (K ⊔ T) ⊔ S := by rw [sup_assoc,sup_eq_right.mpr (show T ≤ S from inf_le_left)]
      _ = F2 ⊔ S := by rw [SectionThree.twoResidual_sup_sylowImage hF2.1.2.1.2]
      _ = P2 := hFS
  have hVK := sixFour_repeat_module_transfer h hcomm hJ D hD K hKP hKB hWK
  let V0 := sectionSixV S P1
  let L := P1 ⊔ P2
  have hVP1 : V0 ≤ P1 := by
    change sectionSixV S P1 ≤ P1
    rw [← hsetup.localV_image]
    exact Subgroup.map_subtype_le _
  have hVnormalP1 : (V0.subgroupOf P1).Normal := by
    change ((sectionSixV S P1).subgroupOf P1).Normal
    rw [← hsetup.localV_image,subgroupOf_map_subtype_eq]
    change (SectionTwo.vSubgroup SP).Normal
    unfold SectionTwo.vSubgroup
    infer_instance
  have hP1N : P1 ≤ Subgroup.normalizer (V0 : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVP1).mp hVnormalP1
  have hKN : K ≤ Subgroup.normalizer (V0 : Set H) :=
    ((Subgroup.le_centralizer_iff).mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVK)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hSN : S ≤ Subgroup.normalizer (V0 : Set H) :=
    h.fiveOne.P1_mem.1.2.1.1.trans hP1N
  have hP2N : P2 ≤ Subgroup.normalizer (V0 : Set H) := hKS ▸ sup_le hKN hSN
  have hVL : V0 ≤ L := hVP1.trans le_sup_left
  have hVnormalL : (V0.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVL).mpr (sup_le hP1N hP2N)
  have hVp : IsPGroup 2 V0 := by
    change IsPGroup 2 (sectionSixV S P1)
    rw [← hsetup.localV_image]
    exact (IsElementaryAbelian.isPGroup 2 (sectionSixLocalV h)).map P1.subtype
  have hVpL : IsPGroup 2 (V0.subgroupOf L) :=
    hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVL).symm
  have hVcore : V0 ≤ twoCoreIn L := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hVL]
    exact Subgroup.map_mono (show V0.subgroupOf L ≤ pCore 2 L from le_sSup ⟨hVnormalL,hVpL⟩)
  have hwbot : w ∈ (⊥ : Subgroup H) := h.fiveOne.join_twoCore_eq_bot ▸ hVcore hwV
  exact hwne hwbot

end Stellmacher.SectionsFiveToSeven
