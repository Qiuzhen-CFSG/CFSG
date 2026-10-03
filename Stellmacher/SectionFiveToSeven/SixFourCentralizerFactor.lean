module
public import Stellmacher.SectionFiveToSeven.SixFourCentralizerSylowSupplement
public import Stellmacher.CentralizerInvolutionCore
public import Stellmacher.SectionFiveToSeven.Result6_1
public import Stellmacher.SectionFiveToSeven.Result5_3
public import Stellmacher.SectionFiveToSeven.HypothesisTwoSectionThree
public import Stellmacher.SectionFiveToSeven.PFamilyBridge
public import Stellmacher.SectionThree.LemmaThreeFour
public import Stellmacher.SectionThree.LocalFamilyGeneratingExtraction
public import Stellmacher.BaumannIntermediate
public import Stellmacher.SectionFiveToSeven.SixFourFixingFactor

/-!
# Second-factor extraction for Stellmacher (6.4)

For the canonical barred fixed vector, the centralizer contains a local-family
member over C_S(w) which generates the original second amalgam member with S.
Its two-residual has full commutator with B(S). The public unconditional
`sixFour_centralizer_factor` uses every original canonical hypothesis,
including the central-action assumption on P₂.

The imported supplement theorem constructs a subgroup of C_{P₂}(w) whose
prescribed Sylow subgroup is C_S(w) and which still generates P₂ with S.
The central involution w gives that subgroup a nontrivial two-core. Baumann
heredity and (6.1) exclude generation by its Sylow normalizer, so local-family
generation selects the desired factor. In the core alternative of (3.4),
Baumann heredity would make the factor and hence P₂ normalize B(S), again
contradicting (6.1). The remaining alternative is the residual commutator.

The generic extraction theorem and conditional wrappers remain public for
the Thompson-in-core branch and other supplied-Sylow applications. The full
centralizer is not required to have C_S(w) as Sylow.

Source: Stellmacher, Journal of Algebra 190 (1997), (6.4), journal p.32,
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

private theorem selected_residual
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (C T F : Subgroup H) (hTS : T ≤ S) (hBT : baumannIn S ≤ T)
    (hF : F ∈ PFamily C T) (hgen : F ⊔ S = P2) :
    ⁅twoResidualAmbient F, baumannIn S⁆ = twoResidualAmbient F := by
  have hFP : F ≤ P2 := le_sup_left.trans_eq hgen
  have hBP : baumannIn S ≤ P2 :=
    (inf_le_left : baumannIn S ≤ S).trans h.fiveOne.P2_mem.1.2.1.1
  have hBnot := lemma_six_one S0 S P1 P2 h
  have hSp := h.sectionThreeHypotheses.nontrivial_two_subgroup.2
  have hBN : S ≤ Subgroup.normalizer (baumannIn S : Set H) :=
    S.le_normalizer.trans (normalizer_le_normalizer_baumann S)
  have hBnormT : ((baumannIn S).subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBT).mpr (hTS.trans hBN)
  have hTne : T ≠ ⊥ := by
    intro hh
    exact hBnot ((hBT.trans_eq hh).trans bot_le)
  have hthree : SectionThree.Hypotheses H T :=
    ⟨h.sectionThreeHypotheses.even_order, hTne, hSp.to_le hTS⟩
  have hsolP : Group.IsSolvable P2 := (lemma_five_three S0 S P1 P2 h).2.2.1
  let _ : Group.IsSolvable P2 := hsolP
  have hsolF : Group.IsSolvable F := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hFP)
  rcases SectionThree.lemma_three_four T hthree F
      ((pFamily_iff_pSet C T F).mp hF |> fun hh => ⟨⟨le_top, hh.1.2⟩, hh.2⟩)
      (baumannIn S) ⟨hBT, hBnormT⟩ hsolF with hBcore | hres
  · exfalso
    have hcoreT : twoCoreIn F ≤ T := by
      obtain ⟨_, R, hR⟩ := hF.1.2.1
      rw [← hR]
      exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := F)).le_sylow_of_normal R)
    have hBcoreEq : baumannIn (twoCoreIn F) = baumannIn S :=
      baumann_eq_of_intermediate S (twoCoreIn F) hBcore (hcoreT.trans hTS)
    have hFnormCore : F ≤ Subgroup.normalizer (twoCoreIn F : Set H) := by
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
      rw [subgroupOf_map_subtype_eq]
      infer_instance
    have hFnormB : F ≤ Subgroup.normalizer (baumannIn S : Set H) := by
      rw [← hBcoreEq]
      exact hFnormCore.trans (normalizer_le_normalizer_baumann (twoCoreIn F))
    have hPnormB : P2 ≤ Subgroup.normalizer (baumannIn S : Set H) := by
      rw [← hgen]
      exact sup_le hFnormB hBN
    let _ : ((baumannIn S).subgroupOf P2).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mpr hPnormB
    have hBp : IsPGroup 2 ((baumannIn S).subgroupOf P2) :=
      (hSp.to_le (inf_le_left : baumannIn S ≤ S)).of_equiv
        (Subgroup.subgroupOfEquivOfLe hBP).symm
    have hle : (baumannIn S).subgroupOf P2 ≤ pCore 2 P2 := le_sSup ⟨inferInstance, hBp⟩
    apply hBnot
    rw [← Subgroup.map_subgroupOf_eq_of_le hBP]
    exact Subgroup.map_mono hle
  · exact hres

/-- Select a generating local factor from a supplied Sylow supplement containing B(S). -/
public theorem sixFour_generating_factor_of_sylow
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (C T : Subgroup H) (hTS : T ≤ S) (hBT : baumannIn S ≤ T)
    (hSylow : IsSylowTwoIn T C) (hcoreC : twoCoreIn C ≠ ⊥)
    (hCP : C ≤ P2) (hgen : C ⊔ S = P2) :
    ∃ F : Subgroup H, F ∈ PFamily C T ∧ F ⊔ S = P2 ∧
      ⁅twoResidualAmbient F, baumannIn S⁆ = twoResidualAmbient F := by
  have hBnot := lemma_six_one S0 S P1 P2 h
  have hSp := h.sectionThreeHypotheses.nontrivial_two_subgroup.2
  have hBP : baumannIn S ≤ P2 :=
    (inf_le_left : baumannIn S ≤ S).trans h.fiveOne.P2_mem.1.2.1.1
  have hBN : S ≤ Subgroup.normalizer (baumannIn S : Set H) :=
    S.le_normalizer.trans (normalizer_le_normalizer_baumann S)
  have hPnot : ¬ P2 ≤ Subgroup.normalizer (baumannIn S : Set H) := by
    intro hPnormB
    let _ : ((baumannIn S).subgroupOf P2).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mpr hPnormB
    have hBp : IsPGroup 2 ((baumannIn S).subgroupOf P2) :=
      (hSp.to_le (inf_le_left : baumannIn S ≤ S)).of_equiv
        (Subgroup.subgroupOfEquivOfLe hBP).symm
    have hle : (baumannIn S).subgroupOf P2 ≤ pCore 2 P2 := le_sSup ⟨inferInstance, hBp⟩
    apply hBnot
    rw [← Subgroup.map_subgroupOf_eq_of_le hBP]
    exact Subgroup.map_mono hle
  have hBTeq : baumannIn T = baumannIn S := baumann_eq_of_intermediate S T hBT hTS
  have hTne : T ≠ ⊥ := by
    intro hh
    exact hBnot ((hBT.trans_eq hh).trans bot_le)
  have hthree : SectionThree.Hypotheses H T :=
    ⟨h.sectionThreeHypotheses.even_order, hTne, hSp.to_le hTS⟩
  have hTcore : T ≠ twoCoreIn C := by
    intro heq
    have hCnormT : C ≤ Subgroup.normalizer (T : Set H) := by
      rw [heq]
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
      rw [subgroupOf_map_subtype_eq]
      infer_instance
    have hCnormB : C ≤ Subgroup.normalizer (baumannIn S : Set H) := by
      rw [← hBTeq]
      exact hCnormT.trans (normalizer_le_normalizer_baumann T)
    exact hPnot (hgen.ge.trans (sup_le hCnormB hBN))
  have hL : C ∈ SectionThree.LSet (⊤ : Subgroup H) T :=
    ⟨le_top, hSylow.2, hcoreC, hTcore⟩
  have hnormalizer : (C ⊓ Subgroup.normalizer (T : Set H)) ⊔ S ≠ P2 := by
    intro heq
    apply hPnot
    apply heq.ge.trans
    apply sup_le ?_ hBN
    apply inf_le_right.trans
    rw [← hBTeq]
    exact normalizer_le_normalizer_baumann T
  obtain ⟨F, hF, hFS⟩ := SectionThree.exists_pSet_generating_of_normalizer_join_ne
    S T P2 C hthree ((pFamily_iff_pSet ⊤ S P2).mp h.fiveOne.P2_mem)
    hL hCP hgen hnormalizer
  have hFfamily := (pFamily_iff_pSet C T F).mpr hF
  exact ⟨F, hFfamily, hFS, selected_residual S0 S P1 P2 h C T F hTS hBT hFfamily hFS⟩

public theorem sixFour_centralizer_factor_of_sylow_supplement
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hJ : sectionSixBarredCritical h ≠ ⊥) (w : H)
    (hwV : w ∈ sectionSixV S P1)
    (hwJ : w ∈ Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H))
    (hwZ : w ∉ omegaOneCenter S)
    (C : Subgroup H) (hC : C ≤ P2 ⊓ Subgroup.centralizer ({w} : Set H))
    (hSyl : IsSylowTwoIn (S ⊓ Subgroup.centralizer ({w} : Set H))
      C) (hgen : C ⊔ S = P2) :
    ∃ F : Subgroup H,
      F ∈ PFamily (P2 ⊓ Subgroup.centralizer ({w} : Set H))
        (S ⊓ Subgroup.centralizer ({w} : Set H)) ∧
      F ⊔ S = P2 ∧ ⁅twoResidualAmbient F, baumannIn S⁆ = twoResidualAmbient F := by
  have hsetup := sectionSix_barred_action_setup h
  obtain ⟨vector, hvector, rfl⟩ := Subgroup.mem_map.mp (hsetup.localV_image.ge hwV)
  let localVector : sectionSixLocalV h := ⟨vector, hvector⟩
  have hBT := (sixFour_canonical_fixing_factor h hJ localVector hwJ hwZ).1
  let SP := sectionSixSylow h
  obtain ⟨hsol, hchar, _⟩ := lemma_five_three S0 S P1 P2 h
  have hSPne : (SP : Subgroup P1) ≠ ⊥ := by
    intro hbot
    apply h.fiveOne.S_nontrivial
    rw [← hsetup.sylow_image, show (sectionSixSylow h : Subgroup P1) = ⊥ from hbot,
      Subgroup.map_bot]
  have hdvd : 2 ∣ Nat.card SP := SP.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hcard => hSPne (Subgroup.card_eq_one.mp hcard))
  have hsec : SectionTwo.Hypotheses P1 :=
    ⟨hsol, even_iff_two_dvd.mpr (hdvd.trans (SP : Subgroup P1).card_subgroup_dvd_card), hchar⟩
  have hVdata := SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian hsec SP
  let _ : IsElementaryAbelian 2 (sectionSixLocalV h) := hVdata.2
  have hvectorTwo : (vector : H) ^ 2 = 1 := congrArg P1.subtype
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := sectionSixLocalV h)
      vector hvector)
  have hvectorS : (vector : H) ∈ S := hsetup.sylow_image.le
    (Subgroup.mem_map_of_mem P1.subtype
      (((hVdata.1.trans ((pCore_isPGroup (p := 2) (G := P1)).le_sylow_of_normal SP)))
        hvector))
  have hvectorNe : (vector : H) ≠ 1 := by
    intro hone
    apply hwZ
    change (vector : H) ∈ omegaOneCenter S
    rw [hone]
    exact (omegaOneCenter S).one_mem
  have hvectorC : (vector : H) ∈ C := hSyl.1
    ⟨hvectorS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  obtain ⟨F, hF, hFS, hFB⟩ := sixFour_generating_factor_of_sylow S0 S P1 P2 h C _
    inf_le_left hBT hSyl
    (centralizer_twoCore_ne_bot C _ hvectorC (hC.trans inf_le_right)
      hvectorTwo hvectorNe) (hC.trans inf_le_left) hgen
  exact ⟨F, ⟨⟨hF.1.1.trans hC, hF.1.2⟩, hF.2⟩, hFS, hFB⟩

public theorem sixFour_centralizer_factor_of_sylow
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hJ : sectionSixBarredCritical h ≠ ⊥) (w : H)
    (hwV : w ∈ sectionSixV S P1)
    (hwJ : w ∈ Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H))
    (hwZ : w ∉ omegaOneCenter S)
    (hgen : P2 = sectionSixCentralizerJoin P2 S w)
    (hSyl : IsSylowTwoIn (S ⊓ Subgroup.centralizer ({w} : Set H))
      (P2 ⊓ Subgroup.centralizer ({w} : Set H))) :
    ∃ F : Subgroup H,
      F ∈ PFamily (P2 ⊓ Subgroup.centralizer ({w} : Set H))
        (S ⊓ Subgroup.centralizer ({w} : Set H)) ∧
      F ⊔ S = P2 ∧ ⁅twoResidualAmbient F, baumannIn S⁆ = twoResidualAmbient F := by
  apply sixFour_centralizer_factor_of_sylow_supplement h hJ w hwV hwJ hwZ
    _ le_rfl hSyl
  simpa only [sectionSixCentralizerJoin, Subgroup.zpowers_eq_closure,
    Subgroup.centralizer_closure] using hgen.symm

/-- The canonical second centralizer factor in Stellmacher (6.4). -/
public theorem sixFour_centralizer_factor
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ = ⊥)
    (hJ : sectionSixBarredCritical h ≠ ⊥) (w : H)
    (hwV : w ∈ sectionSixV S P1)
    (hwJ : w ∈ Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H))
    (hwZ : w ∉ omegaOneCenter S)
    (hgen : P2 = sectionSixCentralizerJoin P2 S w) :
    ∃ F : Subgroup H,
      F ∈ PFamily (P2 ⊓ Subgroup.centralizer ({w} : Set H))
        (S ⊓ Subgroup.centralizer ({w} : Set H)) ∧
      F ⊔ S = P2 ∧ ⁅twoResidualAmbient F, baumannIn S⁆ = twoResidualAmbient F := by
  obtain ⟨C,hC,hSyl,hCS⟩ :=
    sixFour_centralizer_sylow_supplement h hcomm hJ w hwV hwJ hwZ hgen
  exact sixFour_centralizer_factor_of_sylow_supplement h hJ w hwV hwJ hwZ C hC hSyl hCS

end Stellmacher.SectionsFiveToSeven
