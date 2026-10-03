module
public import Stellmacher.SectionFiveToSeven.SixOneCoreContainmentReduction
public import Stellmacher.SectionFiveToSeven.SixOneBaumannSylow
public import Stellmacher.SectionFiveToSeven.SixOneFactorCharacteristicObstruction
public import Stellmacher.SectionFiveToSeven.PFamilyInjective
public import Stellmacher.SectionTwo.LocalActionFactorSelection
public import Stellmacher.SectionTwo.SelectedFactorResidualModule
public import Stellmacher.PushingUp.SL2TwoCoreResidualCardFour
public import Stellmacher.CharacteristicTwoNormal
public import Stellmacher.CharacteristicTwoCoreOvergroup
public import Stellmacher.SL2FrattiniUniqueMaximal
public import Theory.GroupTheory.Commutator.NormalClosureSupplement

/-!
# The selected native factor and actual module in (6.1)

Under Hypothesis Two and the contradictory containment B(S)≤O₂(P₂),
select K inside the native group P₁ with the supplied Sylow subgroup T.
Its injection into H has Sylow image B(S), belongs to the actual local
family, and generates P₁ together with S. The native group satisfies the
Section Two hypotheses, characteristic-Sylow obstruction, and nested SL₂(2)
Frattini condition. Its actual residual commutator W₁ has order four,
lies in B(S), equals [Ω₁Z(B(S)),O²(K)] in H, and is normalized by L₁.

The native core/noncentral data and rich action-factor selection choose K.
The Baumann Sylow theorem and normal characteristic-two inheritance put K
in the characteristic-two setting, while the injective obstruction retains
the exact Sylow T. The local pushing-up theorem gives the actual order-four
commutator. The selected quotient factor identifies that commutator and
makes it L₁-normal. Residual-Sylow generation and the normal-closure
commutator identity give the omega-center description. All subgroup maps
use the original injection P₁.subtype composed with K.subtype.

Source: Stellmacher (6.1), Journal of Algebra 190 (1997), p.30,
`refs/latex/stellmacher-n-group.tex`, from selection of E₁ through W₁.
The four-element conclusion is about [O₂(K),O²(K)], as in the scan;
it is not asserted for the full commutator of the original P₁-module.
-/

open scoped Pointwise
namespace Stellmacher.SectionsFiveToSeven
universe u

private theorem residual_normal {G : Type*} [Group G] :
    (twoResidualAmbient (⊤ : Subgroup G)).Normal := by
  have hres : (twoResidualSubgroup (⊤ : Subgroup G)).Normal := by
    unfold twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal fun N => Subgroup.normal_iInf_normal fun hN => hN.1
  unfold twoResidualAmbient
  exact hres.map _ fun x => ⟨⟨x, by simp⟩, rfl⟩

private theorem closure_map_subtype {H : Type*} [Group H]
    (X P : Subgroup H) (hXP : X ≤ P) :
    (Subgroup.normalClosure (X.subgroupOf P : Set P)).map P.subtype =
      conjugateClosure X P := by
  rw [Subgroup.normalClosure, MonoidHom.map_closure, conjugateClosure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨a, ha⟩ := isConj_iff.mp hconj
    refine ⟨a, ⟨z, hz⟩, ?_⟩
    exact congrArg Subtype.val ha.symm
  · rintro ⟨a, z, rfl⟩
    let zP : P := ⟨z, hXP z.property⟩
    refine ⟨a * zP * a⁻¹, ?_, rfl⟩
    exact Group.mem_conjugatesOfSet_iff.mpr ⟨zP, z.property, isConj_iff.mpr ⟨a, rfl⟩⟩

public theorem sixOne_selected_factor
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2) (hB : baumannIn S ≤ twoCoreIn P2) :
    ∃ (K : Subgroup P1) (T : Sylow 2 K),
      let f := P1.subtype.comp K.subtype
      let W := (⁅pCore 2 K, twoResidualAmbient (⊤ : Subgroup K)⁆).map f
      (T : Subgroup K).map f = baumannIn S ∧
      f.range ≤ sectionSixL (baumannIn S) P1 ∧ f.range ⊔ S = P1 ∧
      SectionTwo.Hypotheses K ∧
      (∀ X : Subgroup T, X.Characteristic → X ≠ ⊥ →
        ¬ (X.map (T : Subgroup K).subtype).Normal) ∧
      IsSL2Two ((K ⧸ pCore 2 K) ⧸ frattini (K ⧸ pCore 2 K)) ∧
      f.range ∈ PFamily (⊤ : Subgroup H) (baumannIn S) ∧
      Nat.card W = 4 ∧ W ≤ baumannIn S ∧
      W = ⁅omegaOneCenter (baumannIn S), twoResidualIn f.range⁆ ∧
      sectionSixL (baumannIn S) P1 ≤ Subgroup.normalizer (W : Set H) ∧
      (P1 : Set H) = (S : Set H) * (sectionSixL (baumannIn S) P1 : Set H) := by
  classical
  obtain ⟨_hS, hJ⟩ := sixOne_coreContainment_reduction S0 S P1 P2 h hB
  obtain ⟨hSP1, SP, hSP⟩ := h.fiveOne.P1_mem.1.2.1
  obtain ⟨hsec, hcore, hnot, hunique⟩ := sixOne_native_local_data S0 S P1 P2 h hJ SP hSP
  let B : Subgroup P1 := (SP : Subgroup P1) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (SP : Subgroup P1)) : Set P1)
  let L := Subgroup.normalClosure (B : Set P1)
  have hBm : B.map P1.subtype = baumannIn S := by
    rw [baumann_map_injective P1.subtype P1.subtype_injective, hSP]
    rfl
  have hBL : baumannIn S ≤ P1 := hBm ▸ Subgroup.map_subtype_le B
  have hBsub : (baumannIn S).subgroupOf P1 = B := by
    rw [← hBm]
    exact Subgroup.comap_map_eq_self_of_injective P1.subtype_injective _
  have hLm : L.map P1.subtype = sectionSixL (baumannIn S) P1 := by
    dsimp only [L]
    rw [← hBsub]
    exact closure_map_subtype (baumannIn S) P1 hBL
  let _ : (SectionTwo.vSubgroup SP).Normal := Subgroup.normalClosure_normal
  let _ : (SectionTwo.cSubgroup SP).Normal := Subgroup.normal_centralizer
  let q := QuotientGroup.mk' (SectionTwo.cSubgroup SP)
  have hq := QuotientGroup.mk'_surjective (SectionTwo.cSubgroup SP)
  have hker : q.ker = SectionTwo.cSubgroup SP := QuotientGroup.ker_mk' _
  let _ := SectionTwo.quotientConjugationAction SP q hq hker
  obtain ⟨K, T, D, hBK, hKL, hT, hA, hgen, hDK, hDN, hDF⟩ :=
    SectionTwo.two_four_exists_local_action_factor hsec SP q hq hker hcore hnot hunique
  change B ≤ K at hBK
  change K ≤ L at hKL
  change (T : Subgroup K).map K.subtype = B at hT
  change (D.subgroupOf (L.map q)).Normal at hDN
  let f : K →* H := P1.subtype.comp K.subtype
  have hf : Function.Injective f := P1.subtype_injective.comp K.subtype_injective
  have hTm : (T : Subgroup K).map f = baumannIn S := by
    rw [show f = P1.subtype.comp K.subtype from rfl, ← Subgroup.map_map, hT, hBm]
  have hfrange : f.range = K.map P1.subtype := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hgenm : f.range ⊔ S = P1 := by
    rw [hfrange, ← hSP, ← Subgroup.map_sup, hgen,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hchar := sixOne_factor_characteristic_obstruction_of_injective
    S0 S P1 P2 h hB f hf T hTm hgenm
  have hBne : B ≠ ⊥ := by
    intro hb
    apply hJ
    have hJB : elementaryAbelianMaxJ S ≤ baumannIn S := by
      refine le_inf (sSup_le fun _ hA => hA.1) ?_
      intro j hj
      apply Subgroup.mem_centralizer_iff.mpr
      intro z hz
      exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 j hj |>.symm
    rw [← hBm, hb, Subgroup.map_bot] at hJB
    exact hJB.trans bot_le
  have hTne : (T : Subgroup K) ≠ ⊥ := by
    intro ht
    apply hBne
    rw [← hT, ht, Subgroup.map_bot]
  obtain ⟨PB, hPB⟩ := SectionTwo.lemma_two_three hsec SP hcore B L rfl rfl
  let _ : L.Normal := Subgroup.normalClosure_normal
  have hcharL : IsCharacteristicTwoType L :=
    characteristicTwo_normal_subgroup hsec.solvable hsec.centralizer_twoCore_le L
  have hQLK : (pCore 2 L).map L.subtype ≤ K := by
    have hQP : pCore 2 L ≤ (PB : Subgroup L) :=
      (pCore_isPGroup (p := 2) (G := L)).le_sylow_of_normal PB
    exact (Subgroup.map_mono hQP).trans (hPB ▸ hBK)
  have hcharK : IsCharacteristicTwoType K :=
    characteristicTwo_of_contains_core_in L K hcharL hKL hQLK
  have hsolvK : Group.IsSolvable K := by
    let _ := hsec.solvable
    infer_instance
  have hdvd : 2 ∣ Nat.card T := T.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hc => hTne (Subgroup.card_eq_one.mp hc))
  have hevenK : Even (Nat.card K) := even_iff_two_dvd.mpr
    (hdvd.trans (Subgroup.card_subgroup_dvd_card (T : Subgroup K)))
  have hsecK : SectionTwo.Hypotheses K := ⟨hsolvK, hevenK, hcharK⟩
  obtain ⟨_hSLaction, hWcard, hWeq⟩ := PushingUp.sl2Two_coreResidual_card_four hsecK T hchar hA
  let R := twoResidualAmbient (⊤ : Subgroup K)
  let W0 := ⁅pCore 2 K, R⁆
  let W := W0.map f
  have hRmap : R.map K.subtype = twoResidualAmbient K := by
    exact map_twoResidualAmbient_of_subgroup_image ⊤ K.subtype K
      ((MonoidHom.range_eq_map K.subtype).symm.trans (Subgroup.range_subtype K))
  have hWmap : W0.map K.subtype = ⁅twoCoreAmbient K, twoResidualAmbient K⁆ := by
    rw [Subgroup.map_commutator, hRmap]
    rfl
  have hWcardP : Nat.card (⁅twoCoreAmbient K, twoResidualAmbient K⁆ : Subgroup P1) = 4 := by
    rw [← hWmap, Subgroup.card_map_of_injective K.subtype_injective]
    exact hWcard
  have hWnormP := (SectionTwo.selected_factor_residual_module hsec SP q hq hker
    B L rfl rfl PB hPB K hBK hKL D hDK hDN hWcardP hDF).2
  have hWcardH : Nat.card W = 4 := by
    rw [Subgroup.card_map_of_injective hf]
    exact hWcard
  have hW0ne : W0 ≠ ⊥ := by
    intro hb
    have hc : Nat.card W0 = 1 := Subgroup.card_eq_one.mpr hb
    have hc4 : Nat.card W0 = 4 := hWcard
    omega
  have hQne : pCore 2 K ≠ ⊥ := by
    intro hb
    apply hW0ne
    simp [W0, hb]
  have hTnot : (T : Subgroup K) ≠ pCore 2 K := by
    intro ht
    have htopne : (⊤ : Subgroup T) ≠ ⊥ := by
      intro hb
      apply hTne
      have hm := congrArg (Subgroup.map (T : Subgroup K).subtype) hb
      simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype, Subgroup.map_bot] using hm
    apply hchar ⊤ inferInstance htopne
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype, ht]
    infer_instance
  have hUK := isUniqueMaximalContaining_of_sl2Two_frattini T hA
  have hFamily := pFamily_range_of_injective f hf T (baumannIn S) hTm hQne hTnot hUK
  have hWB : W ≤ baumannIn S := by
    rw [← hTm]
    apply Subgroup.map_mono
    exact (Subgroup.commutator_le_left _ _).trans
      ((pCore_isPGroup (p := 2) (G := K)).le_sylow_of_normal T)
  let _ : R.Normal := residual_normal
  have hWomega : W0 = ⁅omegaOneCenterAmbient (T : Subgroup K), R⁆ := by
    rw [show W0 = ⁅pCore 2 K, R⁆ from rfl, hWeq]
    apply Subgroup.normalClosure_commutator_eq_of_centralizing_supplement
      (omegaOneCenterAmbient (T : Subgroup K)) R (T : Subgroup K)
      (twoResidualAmbient_top_sup_sylow T)
    intro z hz
    exact Subgroup.mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
  have hWomegaH : W = ⁅omegaOneCenter (baumannIn S), twoResidualIn f.range⁆ := by
    rw [show W = W0.map f from rfl, hWomega, Subgroup.map_commutator,
      ← omegaOneCenterAmbient_map_injective f hf, hTm]
    congr 1
    exact map_twoResidualAmbient_of_subgroup_image ⊤ f f.range
      (MonoidHom.range_eq_map f).symm
  have hWnormH : sectionSixL (baumannIn S) P1 ≤ Subgroup.normalizer (W : Set H) := by
    rw [← hLm]
    apply Subgroup.le_normalizer_iff.mpr
    rintro _ ⟨l, hl, rfl⟩ x hx
    have hWe : W = (⁅twoCoreAmbient K, twoResidualAmbient K⁆).map P1.subtype := by
      rw [← hWmap, Subgroup.map_map]
    rw [hWe] at hx ⊢
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨l * w * l⁻¹, (Subgroup.mem_normalizer_iff.mp (hWnormP hl) w).mp hw, by simp⟩
  have hSL : (SP : Subgroup P1) ⊔ L = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le (hKL.trans le_sup_right) le_sup_left
  have hprod : (P1 : Set H) = (S : Set H) *
      (sectionSixL (baumannIn S) P1 : Set H) := by
    ext x
    constructor
    · intro hx
      have hxm : (⟨x, hx⟩ : P1) ∈ (SP : Subgroup P1) ⊔ L := by simp [hSL]
      obtain ⟨s, hs, l, hl, hsl⟩ := Subgroup.mem_sup_of_normal_right.mp hxm
      exact Set.mem_mul.mpr ⟨s, hSP ▸ Subgroup.mem_map_of_mem P1.subtype hs,
        l, hLm ▸ Subgroup.mem_map_of_mem P1.subtype hl, congrArg Subtype.val hsl⟩
    · rintro ⟨s, hs, l, hl, rfl⟩
      exact P1.mul_mem (hSP1 hs) ((hLm ▸ Subgroup.map_subtype_le L) hl)
  exact ⟨K, T, hTm, hfrange ▸ (Subgroup.map_mono hKL).trans_eq hLm,
    hgenm, hsecK, hchar, hA, hFamily, hWcardH, hWB, hWomegaH, hWnormH, hprod⟩

end Stellmacher.SectionsFiveToSeven
