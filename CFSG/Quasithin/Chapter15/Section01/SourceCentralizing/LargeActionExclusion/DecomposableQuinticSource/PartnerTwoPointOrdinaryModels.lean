module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.PartnerTwoPointActor
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryQuinticPair
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryMathieuLarge
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryBinaryLinear
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryBinaryExceptional
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryRows
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryTits
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryActionBounds

/-!
# Ordinary exclusion with the literal marked subgroup retained

The ordinary catalogue uses the specified marked centralizer and its actual
Sylow subgroup. The quintic actor permutes with that Sylow and moves its
residual support. A faithful elementary sixteen gives the small-quotient
bounds. All native model arguments retain the same component and denominator;
no identification of the marked subgroup with a Thompson four-group is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker ClassificationModels
open Chapter1.Section02.LocalModels Chapter15.Section03.Candidates.ComponentStructure
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]

/-- The ordinary quintic catalogue works at any genuine marked subgroup,
provided its actual Sylow has a permuting quintic actor and faithful sixteen. -/
theorem PreparedChosenModule.quintic_ordinary_component_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥) :
    letI := h.elementary
    let G1 := centralizer (Z1 : Set G)
    let C := M ⊓ G1
    let R := (pResidual 2 C).map C.subtype
    let W := ⁅V,R⁆
    let S := (T : Subgroup G) ⊓ G1
    L ≤ G1 → IsComponent G1 (L.subgroupOf G1) →
    center L = pCore 2 L → IsQuasisimple (L ⧸ pCore 2 L) →
    Chapter1.IsSylowIn 2 (S ⊓ L) L →
    R ⊔ W ≤ normalizer (L : Set G) → ⁅L,W⁆ ≠ ⊥ →
    centralInvolutions T ≤ normalizer (L : Set G) →
    centralInvolutions T ⊓ centralizer (L : Set G) = ⊥ →
    Chapter1.IsSylowIn 2 S G1 →
    (∃ P : Sylow 2 G1, (P : Subgroup G1).map G1.subtype = S ∧
      ∀ z ∈ centralInvolutions T, z ≠ 1 → Chapter1.Lemma115Hypotheses G1 P Mc z) →
    ¬ L ≤ G1 ⊓ Mc → ¬ L ≤ M →
    ((G1 ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc →
    normalizer ((pResidual 2 (G1 ⊓ Mc : Subgroup G)).map (G1 ⊓ Mc).subtype : Set G) ≤ Mc →
    G1 ⊓ normalizer ((G1 ⊓ Mc).pCoreIn 2 : Set G) = G1 ⊓ Mc →
    (pResidual 2 (M ⊓ Mc ⊓ G1 : Subgroup G)).map (M ⊓ Mc ⊓ G1).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype →
    (∃ hWN : W ≤ normalizer (L : Set G), Nat.card (internalActionImage W L hWN) = 16) →
    (∃ Y : Subgroup G, IsPGroup 5 Y ∧ IsPPerfect 2 Y ∧ Y ≤ R ∧
      (S : Set G) * (Y : Set G) = (Y : Set G) * (S : Set G) ∧ ⁅W,Y⁆ = W) →
    (∃ α : MulAut L, ModelAction115 L α) → False := by
  let := h.elementary
  intro G1 C R W S hLG hLc hcenter hquasi hSyl hnL hmove hnZ hfaith hSylG h115 hout houtM
    hcontrol hbound hcoreN hI hfaith16 hactor hmodel
  let : IsQuasisimple (L.subgroupOf G1) := hLc.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLG)
  let : IsQuasisimple (L ⧸ pCore 2 L) := hquasi
  obtain ⟨hWN,hcard⟩ := hfaith16
  have hWV : W ≤ V := (marked_residual_movement h.normalized Z1).1
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  let A := internalActionImage W L hWN
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_surjective
    (actionHom W L hWN).rangeRestrict (actionHom W L hWN).rangeRestrict_surjective
  obtain ⟨Y,hY,hperfect,hYR,hperm,hWY⟩ := hactor
  have hYC : Y ≤ C := hYR.trans (map_subtype_le _)
  have hYN : Y ≤ normalizer (L : Set G) := hYR.trans (le_sup_left.trans hnL)
  have hYn : ¬ Y ≤ centralizer (L : Set G) := by
    intro hc
    have hWc : W ≤ centralizer (L : Set G) := by
      rw [←hWY,commutator_comm]
      apply commutator_le.mpr
      intro y hy w hw
      exact commutator_mem_centralizer_of_normalizes L (hc hy) (hWN hw)
    exact hmove (by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr hWc)
  have hsmall := raw_ordinary_sixteen_small_quotient_exclusions hcenter A hcard
  have hpairs {X : Type} [Group X] (e : (L ⧸ pCore 2 L) ≃* X)
      (hz : center X = ⊥) (ho : IsPGroup 2 (MulAut.Outer X)) :=
    raw_quintic_normal_elementary_pair T hM.1.2 h.normalized h.le_selected
      (hZ.trans inf_le_left) hLG hcenter hSyl hY hYR hnL hWY hmove e hz ho
  have h25 {X : Type} [Group X] [Finite X] (e : (L ⧸ pCore 2 L) ≃* X) (hf : Facts X) :=
    raw_two_five_sylow_overgroup T hcenter hSyl
      (raw_cubic_component_normalizes hG (hZ.trans inf_le_left) hZne
        ⟨hLG,hLc.isCComponent⟩ (Facts.of_equiv e hf)) hY hYN hYn hperm e hf
  have hlargeMathieu :
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M22) ∧
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M23) ∧
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M24) := by
    refine ⟨?_,?_,?_⟩
    · rintro ⟨e⟩
      have hf : Facts Sporadic.Mathieu.M22 := CaseIComponentData.facts_of_small_model
        (.inr (.inr (.inl ⟨MulEquiv.refl _⟩)))
      obtain ⟨P,H,a,b,hPH,h5,hc⟩ := h25 e hf
      have h3 : ¬3 ∣ Nat.card H := Nat.prime_three.coprime_iff_not_dvd.mp
        ((((by decide : Nat.Coprime 3 2).pow_right a).mul_right
          ((by decide : Nat.Coprime 3 5).pow_right b)).of_dvd_right hc)
      have h11 : ¬11 ∣ Nat.card H := (by decide : Nat.Prime 11).coprime_iff_not_dvd.mp
        ((((by decide : Nat.Coprime 11 2).pow_right a).mul_right
          ((by decide : Nat.Coprime 11 5).pow_right b)).of_dvd_right hc)
      rw [Sporadic.Mathieu.M22QuinticSylow.card_eq_128 P H hPH h3 h11] at h5
      norm_num at h5
    · rintro ⟨e⟩
      have hf : Facts Sporadic.Mathieu.M23 := CaseIComponentData.facts_of_small_model
        (.inr (.inr (.inr (.inl ⟨MulEquiv.refl _⟩))))
      obtain ⟨P,H,a,b,hPH,h5,hc⟩ := h25 e hf
      exact Sporadic.Mathieu.M23QuinticSylow.not_five_of_two_five_sylow_overgroup
        P H hPH a b hc h5
    · rintro ⟨e⟩
      have hf : Facts Sporadic.Mathieu.M24 := CaseIComponentData.facts_of_small_model
        (.inr (.inr (.inr (.inr (.inl ⟨MulEquiv.refl _⟩)))))
      obtain ⟨P,H,a,b,hPH,h5,hc⟩ := h25 e hf
      have h3 : ¬3 ∣ Nat.card H := Nat.prime_three.coprime_iff_not_dvd.mp
        ((((by decide : Nat.Coprime 3 2).pow_right a).mul_right
          ((by decide : Nat.Coprime 3 5).pow_right b)).of_dvd_right hc)
      rw [Sporadic.Mathieu.M24QuinticSylow.card_eq_1024 P H hPH h3] at h5
      norm_num at h5
  have hnobinarylin (n : ℕ) (hn : n=4 ∨ n=5)
      (e : (L ⧸ pCore 2 L) ≃* SL(n,ZMod 2)) : False := by
    obtain ⟨P,H,a,b,hPH,h5,hc⟩ := h25 e (linear hn)
    exact binary_no_two_five_sylow_overgroup hn P H a b hPH h5 hc
  have hnobinarypsl (n : ℕ) (hn : n=4 ∨ n=5) (hm : ClassicalGroup.IsPSL L n 2) : False := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    let f : L ≃* SL(n,ZMod 2) := (e.trans (Atlas.fieldEquivPSL n k)).trans
      (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega))
    have hz : center L = ⊥ := by
      apply (center L).eq_bot_iff_card.mpr
      rw [Nat.card_congr (centerCongr f).toEquiv,(linear hn).1,card_bot]
    let q : (L ⧸ pCore 2 L) ≃* SL(n,ZMod 2) :=
      ((QuotientGroup.quotientMulEquivOfEq (hcenter.symm.trans hz)).trans
        QuotientGroup.quotientBot).trans f
    exact hnobinarylin n hn q
  have hsporadic :
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M12) ∧
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.LeechRelated.J2.Carrier) ∧
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.LeechRelated.HS.Carrier) ∧
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Held.He) ∧
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Rudvalis.Model) := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · rintro ⟨e⟩
      obtain ⟨P,E,D,hE,_,_,_,_,_,hc⟩ := hpairs e Sporadic.Mathieu.m12_center_eq_bot
        Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics.outer_isPGroup_two
      have hb := (primeRank_le_iff_elementary_card_le Sporadic.Mathieu.M12).mp
        Sporadic.Mathieu.m12_twoRank_le_three E hE
      norm_num at hb
      omega
    · rintro ⟨e⟩
      obtain ⟨P,E,D,hE,hEP,hPE,_,_,_,hc⟩ := hpairs e
        Sporadic.LeechRelated.J2.OrdinaryLocal.center_eq_bot Sporadic.LeechRelated.J2.outer_isTwoGroup
      let := hE
      have hb := Sporadic.LeechRelated.J2.sylow_normal_elementary_card_le_four P
        (E.subgroupOf P) ((normal_subgroupOf_iff_le_normalizer hEP).mpr hPE)
        (IsElementaryAbelian.subgroupOf hEP)
      rw [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv] at hb
      omega
    · rintro ⟨e⟩
      have ho : IsPGroup 2 (MulAut.Outer Sporadic.LeechRelated.HS.Carrier) :=
        IsPGroup.of_card_dvd_pow (n := 1) (by
          simpa only [pow_one] using Sporadic.LeechRelated.HS.outer_card_dvd_two)
      obtain ⟨P,E,D,hE,_,hPE,_,_,_,hc⟩ := hpairs e
        Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot ho
      have hb := Sporadic.LeechRelated.HS.normal_elementary_card_le_eight P E hE hPE
      omega
    · rintro ⟨e⟩
      obtain ⟨P,E,D,hE,hEP,hPE,hD,hED,hEn,_⟩ := hpairs e
        Held.LocalPairs.center_eq_bot Held.outer_isPGroup_two
      let := hE
      have hb : Nat.card E ≤ 64 :=
        (primeRank_le_iff_elementary_card_le Held.He).mp Held.primeRank_two_le_six E hE
      have hc := card_eq_sixteen_of_quintic_movement E D hD hED hEn hb
      exact Held.sylow_normal_sixteen_normalizer_not_five P E hEP hE hc hPE
        (five_dvd_normalizer_of_quintic_movement E D hD hED hEn)
    · rintro ⟨e⟩
      let : IsQuasisimple (L.subgroupOf G1) := hLc.2
      let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLG)
      let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
      let f := (QuotientGroup.quotientMulEquivOfEq hcenter).trans e
      let : IsSimpleGroup Rudvalis.Model := f.symm.isSimpleGroup
      obtain ⟨P,E,D,hE,_,hPE,hD,hED,hEn,_⟩ := hpairs e
        Rudvalis.LowCentralizers.model_center_eq_bot Rudvalis.outer_isPGroup_two
      let := hE
      have hb : Nat.card E ≤ 64 :=
        (primeRank_le_iff_elementary_card_le Rudvalis.Model).mp Rudvalis.primeRank_le_six E hE
      have hc := card_eq_sixteen_of_quintic_movement E D hD hED hEn hb
      exact Rudvalis.SylowElementarySixteen.normalizer_sixteen_not_five P E hE hc hPE
        (five_dvd_normalizer_of_quintic_movement E D hD hED hEn)
  have hnoM11 (e : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M11) : False :=
    no_small_automorphism_quotient hcenter A hcard (fun B hB => by
      have hb := (primeRank_le_iff_elementary_card_le (MulAut Sporadic.Mathieu.M11)).mp
        Sporadic.Mathieu.m11_automorphism_twoRank_le_two B hB
      norm_num at hb
      omega) e
  have hdvd {X : Type} [Group X] (e : (L ⧸ pCore 2 L) ≃* X) :=
    raw_quintic_aut_five_divides hcenter hY hYR hnL hWY hmove e
  have hbinary : ¬Nonempty ((L ⧸ pCore 2 L) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) ∧
      ¬Nonempty ((L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
    constructor
    · rintro ⟨e⟩
      exact Triality.Standard.BinaryPrimeActors.five_not_dvd_card_aut (hdvd e)
    · rintro ⟨e⟩
      have hh := hdvd e
      have hc : Nat.card (MulAut (commutator (Atlas.G2.Model (ZMod 2)))) = 12096 :=
        (Nat.card_congr Atlas.G2.LieAutomorphismExtensions.binaryAutomorphismEquiv.toEquiv).symm.trans
          Atlas.G2.LieAutomorphismExtensions.card_binaryFull
      norm_num [hc] at hh
  obtain ⟨α,hm⟩ := hmodel
  have hr := remaining_rows hcenter hsmall.1 hsmall.2.1 hsmall.2.2.1 hsmall.2.2.2 hm
  have hrest : α ∈ (MulAut.conj (G := L)).range ∧
      ((IsSimpleGroup L ∧ RawOrdinaryLieRemaining L) ∨
        (center L ≠ ⊥ ∧ center L = pCore 2 L ∧
          (ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4 ∨ IsG2At (L ⧸ pCore 2 L) 4))) := by
    refine ⟨hr.inner,?_⟩
    rcases hr with ⟨hsimple,hLie,_⟩ | ⟨hnc,hc,hmodel,_⟩ | ⟨name,hn3,⟨e⟩,_⟩
    · refine Or.inl ⟨hsimple,?_⟩
      rcases hLie with hB | h3 | hSp | hG2 | hTrial | hRee | hDerived | hTits | ⟨n,hn,h45⟩
      · exact Or.inl hB
      · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr (Or.inl hSp))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hG2)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hTrial))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hRee)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hDerived))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hTits))))))
      · exact (hnobinarypsl n hn h45).elim
    · exact Or.inr ⟨hnc,hc,hmodel⟩
    · exfalso
      obtain ⟨h12,hj2,hhs,hhe,hru⟩ := hsporadic
      obtain ⟨h22,h23,h24⟩ := hlargeMathieu
      cases name with
      | m11 => exact hnoM11 e
      | m12 => exact h12 ⟨e⟩
      | m22 => exact h22 ⟨e⟩
      | m23 => exact h23 ⟨e⟩
      | m24 => exact h24 ⟨e⟩
      | j2 => exact hj2 ⟨e⟩
      | j3 => exact hn3 rfl
      | j4 =>
          exact (h.raw_ordinary_not_jankoFour hG T hempty hM hJ hu hZ hZne
            hLG hLc hcenter hnZ hfaith hSylG hSyl h115 hout).false e
      | hs => exact hhs ⟨e⟩
      | he => exact hhe ⟨e⟩
      | ru => exact hru ⟨e⟩
  have hrestrictions : α ∈ (MulAut.conj (G := L)).range ∧ IsSimpleGroup L ∧
      (IsBenderModel L ∨ Nonempty (L ≃* Tits.ParrottGroup)) := by
    have hnocover := h.raw_ordinary_not_linearThree_four_cover hG T hempty hM hJ hu
      hZ hZne hLG hLc hcenter hnZ hfaith hSylG hSyl hcontrol hbound hI hmove
    have hnolinear : ¬∃ n : ℕ, 1≤n ∧ ClassicalGroup.IsPSL L 3 (2^n) := by
      rintro ⟨n,hn,F,_,_,hF,⟨e⟩⟩
      by_cases hn1 : n=1
      · subst n
        let := Fintype.ofFinite F
        let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
          simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod,pow_one] using hF)
        let e2 : L ≃* PSL(3,ZMod 2) := e.trans (Atlas.fieldEquivPSL 3 k)
        have hz : center L = ⊥ := by
          apply (Subgroup.eq_bot_iff_forall _).mpr
          intro z hz
          have hh : e2 z ∈ center PSL(3,ZMod 2) := (centerCongr e2 ⟨z,hz⟩).property
          rw [Group.IsPerfect.center_quotient_center_eq_bot SL(3,ZMod 2),mem_bot] at hh
          exact e2.injective (hh.trans (map_one e2).symm)
        have hc : pCore 2 L = ⊥ := hcenter.symm.trans hz
        let ec := ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e2
        exact hsmall.2.2.2 7 (by decide) (by decide)
          ⟨ec.trans Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm⟩
      · exact h.raw_ordinary_not_linearThree hG T hempty hM hJ hu hZ hZne hLG hLc
          hcenter hnZ hfaith hSylG hSyl hcontrol hbound hI hmove (by omega) hF e
    have hnog2 (n : ℕ) (hn : 1<n) := h.raw_ordinary_not_higherG2 hG T hempty hM hJ hu
      hZ hZne hLG hLc hcenter hSylG hSyl hout n hn
    obtain ⟨hinner,hrows⟩ := hrest
    rcases hrows with ⟨hsimple,hrows⟩ | ⟨_,_,hlinear | hg⟩
    · let := hsimple
      let : IsQuasisimple (L.subgroupOf G1) := hLc.2
      let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLG)
      have hcb : pCore 2 L = ⊥ := hcenter.symm.trans center_eq_bot_of_simple_perfect
      let eq : (L ⧸ pCore 2 L) ≃* L :=
        (QuotientGroup.quotientMulEquivOfEq hcb).trans QuotientGroup.quotientBot
      obtain ⟨htrial,hderived⟩ := hbinary
      refine ⟨hinner,hsimple,?_⟩
      rcases hrows with hb | hl | ⟨n,hn,F,_,_,hF,⟨e⟩⟩ | ⟨n,hn,hg⟩ | ⟨n,hn,ht⟩ | ⟨m,hm,hr⟩ | ⟨ed⟩ | htits
      · exact Or.inl hb
      · exact (hnolinear hl).elim
      · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
        exact (h.raw_ordinary_not_symplectic hG T hM hJ hu hZ hZne hLG hLc hcenter hSylG hSyl
          hcontrol hbound hcoreN hout hI hmove (by omega) hF
          (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)).elim
      · exact (hnog2 n (by omega) (Or.inl hg)).elim
      · by_cases hn1 : n=1
        · subst n
          obtain ⟨et⟩ := (Triality.Standard.isTrialityGroupAt_two_iff L).mp (by simpa only [pow_one] using ht)
          exact (htrial ⟨eq.trans et⟩).elim
        · exact (h.raw_ordinary_not_higherTriality hG T hempty hM hJ hu hZ hZne
            hLG hLc hcenter hSylG hSyl hout n (by omega) ht).elim
      · exact (h.raw_ordinary_not_higherRee hG T hempty hM hJ hu hZ hZne
          hLG hLc hcenter hSylG hSyl hout m hm hr).elim
      · exact (hderived ⟨eq.trans (Classical.choice ed)⟩).elim
      · exact Or.inr htits
    · exact (hnocover hlinear).elim
    · exact (hnog2 2 (by decide) (Or.inr hg)).elim
  have hnosmalllinear (n : ℕ) (hn : 2 ≤ n) (hnsmall : n ≤ 3)
      (hm : ClassicalGroup.IsPSL L 2 (2^n)) : False := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let A := (internalActionImage W L hWN).map (MulAut.congr e).toMonoidHom
    have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
    have hh := (primeRank_le_iff_elementary_card_le (MulAut PSL(2,F))).mp
      (Theory.PSL2.BinaryAutomorphismRank.psl2_automorphism_two_rank_le hn hF) A hA
    have hcardA : Nat.card A = 16 := by
      rw [card_map_of_injective (MulAut.congr e).injective]
      exact hcard
    have hpw : 2^n ≤ 8 := by
      exact Nat.pow_le_pow_right (by decide) hnsmall
    rw [hcardA] at hh
    omega
  obtain ⟨_,_,hB | ⟨et⟩⟩ := hrestrictions
  · cases hB with
    | linear n hn model =>
      by_cases hlarge : 2<n
      · exact h.raw_ordinary_not_binary_linear_gt_two hG T hM hJ hu hZ hZne hLG hLc
          hSylG hSyl hcontrol hbound hI hmove hout hlarge model
      · exact hnosmalllinear n hn (by omega) model
    | unitary n hn model =>
      exact h.raw_ordinary_not_binary_unitary hG T hM hJ hu hZ hZne hLG hLc hcenter
        hSylG hSyl hcontrol hbound hI hmove hout hn model
    | suzuki m hm model =>
      exact h.raw_ordinary_not_suzuki hG T hM hJ hu hZ hZne hLG hLc hcenter
        hSylG hSyl hcontrol hbound hI hmove hout (by omega) (Classical.choice model)
  · exact raw_tits_actor_contradiction hG T hM h.normalized
      (hZ.trans inf_le_left) hZne hLG hLc hSyl hnZ h115 hI houtM
      hY hperfect hYC hWY hmove (Classical.choice et)

end CFSG.Quasithin.Chapter15.Section01
