module

import FeitThompson.PFsection1.PFsection1_7
import FeitThompson.PFsection4.PFsection4_3
import FeitThompson.PFsection4.PFsection4_4
import FeitThompson.PFsection4.PFsection4_5_to_10
import FeitThompson.PFsection5.PFsection5_3
import FeitThompson.PFsection8.PFsection8_5_b
import FeitThompson.PFsection9.PFsection9_3
import FeitThompson.PFsection9.PFsection9_7
public import FeitThompson.PFsection9.Basic

noncomputable section

open scoped IsMulCommutative commutatorElement

namespace Section9

universe u v w

@[expose] public noncomputable def reducibleCharacterFilter_sec9
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) : Finset (Section1.ClassFunction M) := by
  classical
  exact S.filter fun χ => ¬ Section1.IsIrreducibleCharacterOnGroup χ

private noncomputable def linearHCCharacterFilter_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF C : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) : Finset (Section1.ClassFunction M) := by
  classical
  exact S.filter fun χ => inducedFromLinearCharacterOfHC M MF C χ


private noncomputable def quotientSubgroupOfMapToAmbientQuotientOfInf_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF H0 K : Subgroup G}
    (hMF_M : MF ≤ M)
    [hNMF : (H0.subgroupOf MF).Normal]
    [hKM : (K.subgroupOf M).Normal]
    (hH0K : H0 ≤ K) :
    (MF ⧸ H0.subgroupOf MF) →* (M ⧸ K.subgroupOf M) := by
  refine QuotientGroup.lift (H0.subgroupOf MF)
    ((QuotientGroup.mk' (K.subgroupOf M)).comp (Subgroup.inclusion hMF_M)) ?_
  intro x hx
  change QuotientGroup.mk' (K.subgroupOf M) (Subgroup.inclusion hMF_M x) = 1
  apply (QuotientGroup.eq_one_iff (N := K.subgroupOf M)
    (x := Subgroup.inclusion hMF_M x)).2
  exact hH0K (by simpa [Subgroup.mem_subgroupOf] using hx)

private theorem quotientSubgroupOfMapToAmbientQuotientOfInf_injective_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF H0 K : Subgroup G}
    (hMF_M : MF ≤ M)
    [hNMF : (H0.subgroupOf MF).Normal]
    [hKM : (K.subgroupOf M).Normal]
    (hH0K : H0 ≤ K)
    (hKinf : K ⊓ MF = H0) :
    Function.Injective
      (quotientSubgroupOfMapToAmbientQuotientOfInf_sec9 (M := M) (MF := MF)
        (H0 := H0) (K := K) hMF_M hH0K) := by
  let f := quotientSubgroupOfMapToAmbientQuotientOfInf_sec9 (M := M) (MF := MF)
    (H0 := H0) (K := K) hMF_M hH0K
  rw [← (MonoidHom.ker_eq_bot_iff f)]
  ext x
  constructor
  · intro hx
    rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨y, rfl⟩
    have hfy : f (QuotientGroup.mk' (H0.subgroupOf MF) y) = 1 := hx
    have hqK :
        QuotientGroup.mk' (K.subgroupOf M) (Subgroup.inclusion hMF_M y) = 1 := by
      simpa [f, quotientSubgroupOfMapToAmbientQuotientOfInf_sec9] using hfy
    have hyKM : Subgroup.inclusion hMF_M y ∈ K.subgroupOf M :=
      (QuotientGroup.eq_one_iff (N := K.subgroupOf M)
        (x := Subgroup.inclusion hMF_M y)).1 hqK
    have hyK : (y : G) ∈ K := by
      simpa [Subgroup.mem_subgroupOf] using hyKM
    have hyInf : (y : G) ∈ K ⊓ MF := ⟨hyK, y.property⟩
    have hyH0 : (y : G) ∈ H0 := by
      simpa [hKinf] using hyInf
    have hyH0MF : y ∈ H0.subgroupOf MF := by
      simpa [Subgroup.mem_subgroupOf] using hyH0
    exact (QuotientGroup.eq_one_iff (N := H0.subgroupOf MF) (x := y)).2 hyH0MF
  · intro hx
    have hx1 : x = 1 := by simpa using hx
    simp [hx1]

private theorem quotientSubgroupOfMapToAmbientQuotientOfInf_map_subgroup_eq_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF H0 K L : Subgroup G}
    (hL_MF : L ≤ MF) (hMF_M : MF ≤ M)
    [hNMF : (H0.subgroupOf MF).Normal]
    [hKM : (K.subgroupOf M).Normal]
    (hH0K : H0 ≤ K) :
    let f := quotientSubgroupOfMapToAmbientQuotientOfInf_sec9 (M := M) (MF := MF)
      (H0 := H0) (K := K) hMF_M hH0K
    ((L.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))).map f =
      (L.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)) := by
  intro f
  ext x
  constructor
  · intro hx
    rcases hx with ⟨ybar, hybar, rfl⟩
    rcases hybar with ⟨y, hyL, rfl⟩
    refine ⟨Subgroup.inclusion hMF_M y, ?_, ?_⟩
    · simpa [Subgroup.mem_subgroupOf] using hyL
    · simp [f, quotientSubgroupOfMapToAmbientQuotientOfInf_sec9]
  · intro hx
    rcases hx with ⟨y, hyL, rfl⟩
    let yMF : MF := ⟨(y : G),
      hL_MF (by simpa [Subgroup.mem_subgroupOf] using hyL)⟩
    have hyIncl : Subgroup.inclusion hMF_M yMF = y := by
      ext
      rfl
    refine ⟨QuotientGroup.mk' (H0.subgroupOf MF) yMF, ?_, ?_⟩
    · exact ⟨yMF, by simpa [yMF, Subgroup.mem_subgroupOf] using hyL, rfl⟩
    · simp [f, quotientSubgroupOfMapToAmbientQuotientOfInf_sec9, hyIncl]

private theorem quotientSubgroupOfMapToAmbientQuotientOfInf_map_subgroup_card_eq_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF H0 K L : Subgroup G}
    (hL_MF : L ≤ MF) (hMF_M : MF ≤ M)
    [hNMF : (H0.subgroupOf MF).Normal]
    [hKM : (K.subgroupOf M).Normal]
    (hH0K : H0 ≤ K)
    (hKinf : K ⊓ MF = H0) :
    Nat.card ((L.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) =
      Nat.card ((L.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))) := by
  let f := quotientSubgroupOfMapToAmbientQuotientOfInf_sec9 (M := M) (MF := MF)
    (H0 := H0) (K := K) hMF_M hH0K
  have hf : Function.Injective f :=
    quotientSubgroupOfMapToAmbientQuotientOfInf_injective_sec9
      (M := M) (MF := MF) (H0 := H0) (K := K) hMF_M hH0K hKinf
  have hmap :
      ((L.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))).map f =
        (L.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)) :=
    quotientSubgroupOfMapToAmbientQuotientOfInf_map_subgroup_eq_sec9
      (M := M) (MF := MF) (H0 := H0) (K := K) (L := L)
      hL_MF hMF_M hH0K
  calc
    Nat.card ((L.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) =
        Nat.card (((L.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))).map f) := by
          rw [hmap]
    _ = Nat.card ((L.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))) :=
        Subgroup.card_map_of_injective hf

private theorem theorem_9_nb_redM_W2_map_mk_H0_MF_card_eq_of_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 H0 : Subgroup G}
    {p q : ℕ}
    [hH0normalMF : (H0.subgroupOf MF).Normal] :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
            quotientChiefFactorData_9_6 M MF H0 W1 hp) →
        Nat.card ((W2.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))) = p := by
  intro h92 hpData
  rcases hpData with ⟨hp, hp_eq, hho, h96⟩
  rcases hho with
    ⟨_hH0_le_MF, hMF_le_M, hH0_normal_M, _hH0_normal_MF, _hH0lt,
      _helem, _htypeIIIIV⟩
  rcases h96 with
    ⟨_hH0_le_MF96, _hMF_le_M96, _hnormal96, _hchief, hWbar, _hcard⟩
  rcases h92.mf.1 with ⟨hMF_le_M92, hMF_normal_M, _hMFnil, _hMFhall⟩
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, ⟨hW1_le_M, _hW1hall⟩,
      _hcompMW1, _hUleD, _hUnil, _hW1normU, _hcompDU, _hMFnotcyc,
      _hsecond, _hfitEq, _hfitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMF_le_M92).1 hMF_normal_M
  have hW1_norm_MF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    hW1_le_M.trans hM_norm_MF
  letI : Subgroup.Normalizes W1 MF := ⟨hW1_norm_MF⟩
  have hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF) :=
    subgroupOf_MF_isInvariant_of_subgroupOf_M_normal_sec9 M MF W1 H0
      hMF_le_M hW1_le_M hH0_normal_M hW1_norm_MF
  rcases hWbar with ⟨_hnormalSrc, hsourceCard⟩
  have hsourceCard' :
      Nat.card {x : MF ⧸ H0.subgroupOf MF //
        ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
          ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p := by
    simpa [hp_eq] using hsourceCard
  have hsource_eq_fixed :
      Nat.card {x : MF ⧸ H0.subgroupOf MF //
        ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
          ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} =
        Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF)) := by
    simpa using
      quotient_W1_fixedPointSubgroup_card_eq_barW2_subtype_sec9
        MF W1 H0 hH0_inv_W1 hH0normalMF
  have hfixed_card :
      Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF)) = p :=
    hsource_eq_fixed.symm.trans hsourceCard'
  have hfixed_eq :
      fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF) =
        (W2.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF)) :=
    quotient_W1_fixedPointSubgroup_eq_W2_map_of_hypothesis_9_2_sec9
      M MF U W1 W2 H0 q h92 hH0normalMF hH0_inv_W1
  simpa [hfixed_eq] using hfixed_card

private theorem theorem_9_nb_redM_W2_map_mk_K_card_eq_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  letI : (K.subgroupOf M).Normal := hKnormal
                  Nat.card ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) = p := by
  intro h92 _hH0MF _hpprime hpData hKnormal _hKD hKinf
  letI : (K.subgroupOf M).Normal := hKnormal
  have hpDataFull := hpData
  rcases hpData with ⟨_hp, _hp_eq, hho, _h96⟩
  rcases hho with
    ⟨_hH0_le_MF, hMF_le_M, _hH0_normal_M, hH0normalMF, _hH0lt,
      _helem, _htypeIIIIV⟩
  letI : (H0.subgroupOf MF).Normal := hH0normalMF
  have hW2MF : W2 ≤ MF := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hSecondLe, _hFittingEq,
        _hFittingLeD, hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
    exact hW2le.trans inf_le_left
  have hH0K : H0 ≤ K := by
    intro x hx
    have hxInf : x ∈ K ⊓ MF := by
      simpa [hKinf] using hx
    exact hxInf.1
  have hcard_eq :
      Nat.card ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) =
        Nat.card ((W2.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))) :=
    quotientSubgroupOfMapToAmbientQuotientOfInf_map_subgroup_card_eq_sec9
      (M := M) (MF := MF) (H0 := H0) (K := K) (L := W2)
      hW2MF hMF_le_M hH0K hKinf
  have hcard_H0 :
      Nat.card ((W2.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))) = p :=
    theorem_9_nb_redM_W2_map_mk_H0_MF_card_eq_of_source_sec9
      (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) (H0 := H0)
      (p := p) (q := q) h92 hpDataFull
  exact hcard_eq.trans hcard_H0

private theorem theorem_9_nb_redM_W2_map_mk_K_isCyclic_source_core_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 _H0 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        letI : (K.subgroupOf M).Normal := hKnormal
        let qM : M →* M ⧸ K.subgroupOf M :=
          QuotientGroup.mk' (K.subgroupOf M)
        IsCyclic ((W2.subgroupOf M).map qM) := by
  intro h92 hKnormal
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change IsCyclic ((W2.subgroupOf M).map qM)
  have hW2cyc : IsCyclic W2 := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hSecondLe, _hFittingEq,
        _hFittingLeD, _hW2le, hW2cyc, _hW2ne, _hCent, _hHatW⟩
    exact hW2cyc
  have hW2M : W2 ≤ M :=
    W2_le_M_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hW2sub_cyclic : IsCyclic (W2.subgroupOf M) :=
    (Subgroup.subgroupOfEquivOfLe (H := W2) (K := M) hW2M).isCyclic.mpr hW2cyc
  letI : IsCyclic (W2.subgroupOf M) := hW2sub_cyclic
  exact isCyclic_of_surjective
    (f := qM.subgroupMap (W2.subgroupOf M))
    (MonoidHom.subgroupMap_surjective qM (W2.subgroupOf M))

private theorem natCard_ne_one_of_eq_prime_sec9
    {α : Type u} [Finite α] {p : ℕ}
    (hp : Nat.Prime p) :
    Nat.card α = p → Nat.card α ≠ 1 := by
  intro hcard hone
  exact hp.ne_one (by
    rw [← hcard]
    exact hone)

private theorem theorem_9_nb_redM_W2_le_ambientDerived_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      W2 ≤ ambientDerivedSubgroup M := by
  intro h92
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  intro x hx
  have hSecond_le_D :
      section16SecondDerivedSubgroup M ≤ ambientDerivedSubgroup M := by
    simpa [section16SecondDerivedSubgroup] using
      (section12_ambientDerivedSubgroup_le (G := G)
        (E := ambientDerivedSubgroup M))
  exact hSecond_le_D (hW2le hx).2

private theorem theorem_9_nb_redM_W1_inf_W2_eq_bot_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      W1 ⊓ W2 = ⊥ := by
  intro h92
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, hcompMW1, _hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  apply le_antisymm
  · intro x hx
    have hxD : x ∈ ambientDerivedSubgroup M :=
      theorem_9_nb_redM_W2_le_ambientDerived_sec9 M MF U W1 W2 q h92 hx.2
    have hxInf : x ∈ ambientDerivedSubgroup M ⊓ W1 := ⟨hxD, hx.1⟩
    simpa using hcompMW1.2.2.2.le_bot hxInf
  · exact bot_le

private theorem theorem_9_nb_redM_W2_le_centralizer_W1_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      W2 ≤ Subgroup.centralizer (W1 : Set G) := by
  intro h92
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, hCent, _hHatW⟩
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  by_cases hx1 : x = 1
  · simp [hx1]
  · have hyCent : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) x := by
      simpa [hCent x hx hx1] using hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp hyCent.2).symm

private theorem theorem_9_nb_redM_W_internalDirectProduct_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      Section2.IsInternalDirectProduct
        ((W1 ⊔ W2).subgroupOf M) (W1.subgroupOf M) (W2.subgroupOf M) := by
  classical
  intro h92
  have hW2centW1 : W2 ≤ Subgroup.centralizer (W1 : Set G) :=
    theorem_9_nb_redM_W2_le_centralizer_W1_sec9 M MF U W1 W2 q h92
  have hW1infW2 : W1 ⊓ W2 = ⊥ :=
    theorem_9_nb_redM_W1_inf_W2_eq_bot_sec9 M MF U W1 W2 q h92
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  rcases hW1hall with ⟨hW1M, _hW1HallSub⟩
  have hW2M : W2 ≤ M :=
    W2_le_M_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hW1_norm_W2 : W1 ≤ Subgroup.normalizer (W2 : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hcomm : a * y = y * a :=
        Subgroup.mem_centralizer_iff.mp (hW2centW1 hy) a ha
      have hconj : a * y * a⁻¹ = y := by
        calc
          a * y * a⁻¹ = y * a * a⁻¹ := by rw [hcomm]
          _ = y := by simp [mul_assoc]
      simpa [hconj] using hy
    · intro hy
      let y' : G := a * y * a⁻¹
      have hy'W2 : y' ∈ W2 := by simpa [y'] using hy
      have hcomm' : a * y' = y' * a :=
        Subgroup.mem_centralizer_iff.mp (hW2centW1 hy'W2) a ha
      have hconj : a⁻¹ * y' * a = y' := by
        have h := congrArg (fun t : G => a⁻¹ * t) hcomm'
        simpa [mul_assoc] using h.symm
      have hy_eq : y = y' := by
        calc
          y = a⁻¹ * y' * a := by simp [y', mul_assoc]
          _ = y' := hconj
      simpa [hy_eq] using hy'W2
  let W : Subgroup G := W1 ⊔ W2
  let W1W : Subgroup W := W1.subgroupOf W
  let W2W : Subgroup W := W2.subgroupOf W
  haveI : W2W.Normal := by
    simpa [W, W2W] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := W1) (N := W2) hW1_norm_W2)
  have hW1W_W2W_top : W1W ⊔ W2W = ⊤ := by
    calc
      W1W ⊔ W2W = W.subgroupOf W := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := W1) (A' := W2) (B := W)
          (by simp [W])
          (by simp [W])
      _ = ⊤ := by simp
  refine
    { left_le := ?_
      right_le := ?_
      commute := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro x hx
    have hxW1 : ((x : M) : G) ∈ W1 := by
      simpa [Subgroup.mem_subgroupOf] using hx
    simpa [Subgroup.mem_subgroupOf] using
      ((le_sup_left : W1 ≤ W1 ⊔ W2) hxW1)
  · intro x hx
    have hxW2 : ((x : M) : G) ∈ W2 := by
      simpa [Subgroup.mem_subgroupOf] using hx
    simpa [Subgroup.mem_subgroupOf] using
      ((le_sup_right : W2 ≤ W1 ⊔ W2) hxW2)
  · intro h hh k hk
    have hhW1 : ((h : M) : G) ∈ W1 := by
      simpa [Subgroup.mem_subgroupOf] using hh
    have hkW2 : ((k : M) : G) ∈ W2 := by
      simpa [Subgroup.mem_subgroupOf] using hk
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hW2centW1 hkW2) ((h : M) : G) hhW1
  · apply le_antisymm
    · intro x hx
      have hxAmb : ((x : M) : G) ∈ W1 ⊓ W2 := by
        constructor
        · simpa [Subgroup.mem_subgroupOf] using hx.1
        · simpa [Subgroup.mem_subgroupOf] using hx.2
      have hxBotG : ((x : M) : G) ∈ (⊥ : Subgroup G) := by
        simpa [hW1infW2] using hxAmb
      ext
      simpa using hxBotG
    · exact bot_le
  · intro c hc
    let cW : W := ⟨((c : M) : G), by simpa [W, Subgroup.mem_subgroupOf] using hc⟩
    have hcSup : cW ∈ W1W ⊔ W2W := by
      rw [hW1W_W2W_top]
      simp
    rcases (Subgroup.mem_sup_of_normal_right (s := W1W) (t := W2W) (x := cW)).1
        hcSup with
      ⟨aW, haW, bW, hbW, hab⟩
    have haW1 : (aW : G) ∈ W1 := by
      simpa [W1W, Subgroup.mem_subgroupOf] using haW
    have hbW2 : (bW : G) ∈ W2 := by
      simpa [W2W, Subgroup.mem_subgroupOf] using hbW
    let aM : M := ⟨(aW : G), hW1M haW1⟩
    let bM : M := ⟨(bW : G), hW2M hbW2⟩
    refine ⟨aM, ?_, bM, ?_, ?_⟩
    · simpa [aM, Subgroup.mem_subgroupOf] using haW1
    · simpa [bM, Subgroup.mem_subgroupOf] using hbW2
    · apply Subtype.ext
      have hval := congrArg (fun z : W => (z : G)) hab
      simpa [aM, bM, cW] using hval.symm

private theorem theorem_9_nb_redM_M_mod_K_quotient_semidirect_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        K ≤ ambientDerivedSubgroup M →
          letI : (K.subgroupOf M).Normal := hKnormal
          let qM : M →* M ⧸ K.subgroupOf M :=
            QuotientGroup.mk' (K.subgroupOf M)
          Section2.IsInternalSemidirectProduct
            (⊤ : Subgroup (M ⧸ K.subgroupOf M))
            (((ambientDerivedSubgroup M).subgroupOf M).map qM)
            ((W1.subgroupOf M).map qM) := by
  intro h92 hKnormal hKD
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change Section2.IsInternalSemidirectProduct
    (⊤ : Subgroup (M ⧸ K.subgroupOf M))
    (((ambientDerivedSubgroup M).subgroupOf M).map qM)
    ((W1.subgroupOf M).map qM)
  have hNleD : K.subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M := by
    intro x hx
    have hxK : (x : G) ∈ K := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact hKD hxK
  have hcomp :
      ((ambientDerivedSubgroup M).subgroupOf M).IsComplement' (W1.subgroupOf M) :=
    ambientDerived_W1_isComplement'_subgroupOf_M_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92
  have hcompQuot :
      (((ambientDerivedSubgroup M).subgroupOf M).map qM).IsComplement'
        ((W1.subgroupOf M).map qM) :=
    isComplement'_map_mk'_of_le_isComplement'
      ((ambientDerivedSubgroup M).subgroupOf M) (W1.subgroupOf M)
      (K.subgroupOf M) hNleD hcomp
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : ((ambientDerivedSubgroup M).subgroupOf M).Normal := hDnormal
  have hDmapNormal :
      (((ambientDerivedSubgroup M).subgroupOf M).map qM).Normal :=
    hDnormal.map qM (QuotientGroup.mk'_surjective (K.subgroupOf M))
  letI : (((ambientDerivedSubgroup M).subgroupOf M).map qM).Normal := hDmapNormal
  exact internalSemidirectProduct_top_of_normal_isComplement'_sec9 hcompQuot

private theorem theorem_9_nb_redM_W1_map_mk_K_card_eq_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        K ≤ ambientDerivedSubgroup M →
          letI : (K.subgroupOf M).Normal := hKnormal
          Nat.card ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) =
            Nat.card W1 := by
  intro h92 hKnormal hKD
  letI : (K.subgroupOf M).Normal := hKnormal
  have hNleD : K.subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M := by
    intro x hx
    have hxK : (x : G) ∈ K := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact hKD hxK
  have hcomp :
      ((ambientDerivedSubgroup M).subgroupOf M).IsComplement' (W1.subgroupOf M) :=
    ambientDerived_W1_isComplement'_subgroupOf_M_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92
  have hW1M : W1 ≤ M :=
    W1_le_M_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  calc
    Nat.card ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
        = Nat.card (W1.subgroupOf M) :=
          natCard_map_mk'_eq_of_le_isComplement'
            ((ambientDerivedSubgroup M).subgroupOf M) (W1.subgroupOf M)
            (K.subgroupOf M) hNleD hcomp
    _ = Nat.card W1 := natCard_subgroupOf_eq W1 M hW1M

private theorem theorem_9_nb_redM_W1_map_mk_K_card_ne_one_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        K ≤ ambientDerivedSubgroup M →
          letI : (K.subgroupOf M).Normal := hKnormal
          Nat.card ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) ≠ 1 := by
  intro h92 hKnormal hKD
  letI : (K.subgroupOf M).Normal := hKnormal
  have hcard :
      Nat.card ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) =
        Nat.card W1 :=
    theorem_9_nb_redM_W1_map_mk_K_card_eq_sec9
      M MF U W1 W2 K q h92 hKnormal hKD
  have h92W1 : hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) :=
    hypothesis_9_2_with_card_W1_sec9 h92
  have hW1prime : Nat.Prime (Nat.card W1) :=
    nat_card_W1_prime_of_hypothesis_9_2_sec9 M MF U W1 W2 h92W1
  intro hcard1
  exact hW1prime.ne_one (by
    rw [← hcard]
    exact hcard1)

private theorem theorem_9_nb_redM_W1_map_mk_K_isCyclic_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        letI : (K.subgroupOf M).Normal := hKnormal
        let qM : M →* M ⧸ K.subgroupOf M :=
          QuotientGroup.mk' (K.subgroupOf M)
        IsCyclic ((W1.subgroupOf M).map qM) := by
  intro h92 hKnormal
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change IsCyclic ((W1.subgroupOf M).map qM)
  have hW1cyc : IsCyclic W1 := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, hW1cyc, _hW1ne, _hW1hall, _hrest⟩
    exact hW1cyc
  have hW1M : W1 ≤ M :=
    W1_le_M_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hW1sub_cyclic : IsCyclic (W1.subgroupOf M) :=
    (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).isCyclic.mpr hW1cyc
  letI : IsCyclic (W1.subgroupOf M) := hW1sub_cyclic
  exact isCyclic_of_surjective
    (f := qM.subgroupMap (W1.subgroupOf M))
    (MonoidHom.subgroupMap_surjective qM (W1.subgroupOf M))

private theorem theorem_9_nb_redM_W1_map_mk_K_isHall_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        letI : (K.subgroupOf M).Normal := hKnormal
        let qM : M →* M ⧸ K.subgroupOf M :=
          QuotientGroup.mk' (K.subgroupOf M)
        ∃ π : Set Nat.Primes,
          IsHallSubgroup π ((W1.subgroupOf M).map qM) := by
  intro h92 hKnormal
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change ∃ π : Set Nat.Primes, IsHallSubgroup π ((W1.subgroupOf M).map qM)
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hrest⟩
  rcases hW1hall with ⟨_hW1M, hHall⟩
  exact ⟨subgroupPrimeSet W1,
    isHallSubgroup_map_of_surjective_sec9 hHall qM
      (QuotientGroup.mk'_surjective (K.subgroupOf M))⟩

private theorem theorem_9_nb_redM_M_mod_K_quotient_internalDirectProduct_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        K ≤ ambientDerivedSubgroup M →
          letI : (K.subgroupOf M).Normal := hKnormal
          let qM : M →* M ⧸ K.subgroupOf M :=
            QuotientGroup.mk' (K.subgroupOf M)
          Section2.IsInternalDirectProduct
            (((W1 ⊔ W2).subgroupOf M).map qM)
            ((W1.subgroupOf M).map qM)
            ((W2.subgroupOf M).map qM) := by
  classical
  intro h92 hKnormal hKD
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change Section2.IsInternalDirectProduct
    (((W1 ⊔ W2).subgroupOf M).map qM)
    ((W1.subgroupOf M).map qM)
    ((W2.subgroupOf M).map qM)
  let Wq : Subgroup (M ⧸ K.subgroupOf M) :=
    ((W1 ⊔ W2).subgroupOf M).map qM
  let W1q : Subgroup (M ⧸ K.subgroupOf M) :=
    (W1.subgroupOf M).map qM
  let W2q : Subgroup (M ⧸ K.subgroupOf M) :=
    (W2.subgroupOf M).map qM
  let Dq : Subgroup (M ⧸ K.subgroupOf M) :=
    ((ambientDerivedSubgroup M).subgroupOf M).map qM
  have hWprod :
      Section2.IsInternalDirectProduct
        ((W1 ⊔ W2).subgroupOf M) (W1.subgroupOf M) (W2.subgroupOf M) :=
    theorem_9_nb_redM_W_internalDirectProduct_sec9 M MF U W1 W2 q h92
  have hsemi :
      Section2.IsInternalSemidirectProduct
        (⊤ : Subgroup (M ⧸ K.subgroupOf M)) Dq W1q := by
    simpa [Dq, W1q, qM] using
      (theorem_9_nb_redM_M_mod_K_quotient_semidirect_sec9
        M MF U W1 W2 K q h92 hKnormal hKD)
  have hW2Dsub :
      W2.subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M := by
    intro x hx
    have hxW2 : ((x : M) : G) ∈ W2 := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxD : ((x : M) : G) ∈ ambientDerivedSubgroup M :=
      theorem_9_nb_redM_W2_le_ambientDerived_sec9 M MF U W1 W2 q h92 hxW2
    simpa [Subgroup.mem_subgroupOf] using hxD
  have hW2q_le_Dq : W2q ≤ Dq := by
    intro x hx
    rcases hx with ⟨y, hyW2, hxy⟩
    exact ⟨y, hW2Dsub hyW2, hxy⟩
  refine
    { left_le := ?_
      right_le := ?_
      commute := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro x hx
    rcases hx with ⟨y, hyW1, hxy⟩
    exact ⟨y, hWprod.left_le hyW1, hxy⟩
  · intro x hx
    rcases hx with ⟨y, hyW2, hxy⟩
    exact ⟨y, hWprod.right_le hyW2, hxy⟩
  · intro h hh k hk
    rcases hh with ⟨h0, hh0, hqh⟩
    rcases hk with ⟨k0, hk0, hqk⟩
    have hcomm : h0 * k0 = k0 * h0 :=
      hWprod.commute h0 hh0 k0 hk0
    calc
      h * k = qM h0 * qM k0 := by rw [← hqh, ← hqk]
      _ = qM (h0 * k0) := by rw [map_mul]
      _ = qM (k0 * h0) := by rw [hcomm]
      _ = qM k0 * qM h0 := by rw [map_mul]
      _ = k * h := by rw [← hqh, ← hqk]
  · apply le_antisymm
    · intro x hx
      have hxDq : x ∈ Dq := hW2q_le_Dq hx.2
      have hxInf : x ∈ Dq ⊓ W1q := ⟨hxDq, hx.1⟩
      have hxBot : x ∈ (⊥ : Subgroup (M ⧸ K.subgroupOf M)) := by
        simpa [hsemi.inf_eq_bot] using hxInf
      simpa using hxBot
    · exact bot_le
  · intro c hc
    rcases hc with ⟨c0, hc0, hqc⟩
    rcases hWprod.mul_surjective c0 hc0 with
      ⟨h0, hh0, k0, hk0, hc0eq⟩
    refine ⟨qM h0, ⟨h0, hh0, rfl⟩, qM k0, ⟨k0, hk0, rfl⟩, ?_⟩
    calc
      c = qM c0 := hqc.symm
      _ = qM (h0 * k0) := by rw [hc0eq]
      _ = qM h0 * qM k0 := by rw [map_mul]

private theorem theorem_9_nb_redM_M_mod_K_quotient_W_odd_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M W1 W2 K : Subgroup G)
    (hKnormal : (K.subgroupOf M).Normal) :
    letI : (K.subgroupOf M).Normal := hKnormal
    let qM : M →* M ⧸ K.subgroupOf M :=
      QuotientGroup.mk' (K.subgroupOf M)
    Odd (Nat.card (((W1 ⊔ W2).subgroupOf M).map qM)) := by
  intro
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change Odd (Nat.card (((W1 ⊔ W2).subgroupOf M).map qM))
  have hWq_dvd_quot :
      Nat.card (((W1 ⊔ W2).subgroupOf M).map qM) ∣
        Nat.card (M ⧸ K.subgroupOf M) :=
    Subgroup.card_subgroup_dvd_card (((W1 ⊔ W2).subgroupOf M).map qM)
  have hquot_dvd_M :
      Nat.card (M ⧸ K.subgroupOf M) ∣ Nat.card M :=
    Subgroup.card_quotient_dvd_card (K.subgroupOf M)
  have hM_dvd_G : Nat.card M ∣ Nat.card G :=
    Subgroup.card_subgroup_dvd_card M
  exact Odd.of_dvd_nat IsMinCE.odd_order
    (hWq_dvd_quot.trans (hquot_dvd_M.trans hM_dvd_G))

private theorem theorem_9_nb_redM_centralizerIn_ambientDerived_subgroupOf_M_eq_W2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      ∀ x : W1.subgroupOf M, x ≠ 1 →
        Section2.centralizerIn ((ambientDerivedSubgroup M).subgroupOf M) (x : M) =
          W2.subgroupOf M := by
  intro h92 x hx
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, hCent, _hHatW⟩
  have hxW1 : ((x : M) : G) ∈ W1 :=
    Subgroup.mem_subgroupOf.mp x.property
  have hxGne : ((x : M) : G) ≠ 1 := by
    intro hxG
    have hxM : (x : M) = 1 := Subtype.ext hxG
    exact hx (Subtype.ext hxM)
  ext y
  constructor
  · intro hy
    have hyDG : ((y : M) : G) ∈ ambientDerivedSubgroup M := by
      simpa [Subgroup.mem_subgroupOf] using hy.1
    have hyCommM : y * (x : M) = (x : M) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have hyCommG :
        ((y : M) : G) * ((x : M) : G) =
          ((x : M) : G) * ((y : M) : G) :=
      congrArg Subtype.val hyCommM
    have hyCentG :
        ((y : M) : G) ∈
          elementCentralizerIn (ambientDerivedSubgroup M) ((x : M) : G) :=
      ⟨hyDG, Subgroup.mem_centralizer_singleton_iff.mpr hyCommG⟩
    have hyW2G : ((y : M) : G) ∈ W2 := by
      simpa [hCent ((x : M) : G) hxW1 hxGne] using hyCentG
    simpa [Subgroup.mem_subgroupOf] using hyW2G
  · intro hy
    have hyW2G : ((y : M) : G) ∈ W2 := by
      simpa [Subgroup.mem_subgroupOf] using hy
    have hyCentG :
        ((y : M) : G) ∈
          elementCentralizerIn (ambientDerivedSubgroup M) ((x : M) : G) := by
      simpa [hCent ((x : M) : G) hxW1 hxGne] using hyW2G
    constructor
    · simpa [Subgroup.mem_subgroupOf] using hyCentG.1
    · have hyCommG :
          ((y : M) : G) * ((x : M) : G) =
            ((x : M) : G) * ((y : M) : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hyCentG.2
      have hyCommM : y * (x : M) = (x : M) * y := by
        apply Subtype.ext
        exact hyCommG
      exact Subgroup.mem_centralizer_singleton_iff.mpr hyCommM

private theorem theorem_9_nb_redM_M_mod_K_quotient_centralizer_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        K ≤ ambientDerivedSubgroup M →
          letI : (K.subgroupOf M).Normal := hKnormal
          let qM : M →* M ⧸ K.subgroupOf M :=
            QuotientGroup.mk' (K.subgroupOf M)
          ∀ x : (W1.subgroupOf M).map qM, x ≠ 1 →
            Section2.centralizerIn
              (((ambientDerivedSubgroup M).subgroupOf M).map qM)
              (x : M ⧸ K.subgroupOf M) =
              (W2.subgroupOf M).map qM := by
  classical
  intro h92 hKnormal hKD
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change ∀ x : (W1.subgroupOf M).map qM, x ≠ 1 →
    Section2.centralizerIn
      (((ambientDerivedSubgroup M).subgroupOf M).map qM)
      (x : M ⧸ K.subgroupOf M) =
      (W2.subgroupOf M).map qM
  have hP : Section8.typePDefinitionData M MF U W1 W2 := h92.typePDefinitionData
  have hDleM : ambientDerivedSubgroup M ≤ M := section12_ambientDerivedSubgroup_le
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : ((ambientDerivedSubgroup M).subgroupOf M).Normal := hDnormal
  have hsolvD : IsSolvable (ambientDerivedSubgroup M) :=
    typePDefinitionData_ambientDerived_solvable_sec9 hP
  have hsolvDsub : IsSolvable ((ambientDerivedSubgroup M).subgroupOf M) := by
    let e := Subgroup.subgroupOfEquivOfLe (H := ambientDerivedSubgroup M)
      (K := M) hDleM
    letI : IsSolvable (ambientDerivedSubgroup M) := hsolvD
    exact solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
  have hDcard :
      Nat.card ((ambientDerivedSubgroup M).subgroupOf M) =
        Nat.card (ambientDerivedSubgroup M) :=
    natCard_subgroupOf_eq (ambientDerivedSubgroup M) M hDleM
  have hW1M : W1 ≤ M :=
    W1_le_M_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hW1card : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    natCard_subgroupOf_eq W1 M hW1M
  have hcopW1D :
      Nat.Coprime (Nat.card W1) (Nat.card (ambientDerivedSubgroup M)) :=
    typePDefinitionData_W1_card_coprime_ambientDerived_sec9 hP
  have hcopD_W1sub :
      Nat.Coprime (Nat.card ((ambientDerivedSubgroup M).subgroupOf M))
        (Nat.card (W1.subgroupOf M)) := by
    rw [hDcard, hW1card]
    exact hcopW1D.symm
  have hcentW1 :
      ∀ x : W1.subgroupOf M, x ≠ 1 →
        Section2.centralizerIn ((ambientDerivedSubgroup M).subgroupOf M) (x : M) =
          W2.subgroupOf M :=
    theorem_9_nb_redM_centralizerIn_ambientDerived_subgroupOf_M_eq_W2_sec9
      M MF U W1 W2 q h92
  intro r hr
  apply le_antisymm
  · intro y hy
    have hyElem :
        y ∈ elementCentralizerIn
          (((ambientDerivedSubgroup M).subgroupOf M).map qM)
          (r : M ⧸ K.subgroupOf M) := by
      simpa [Section2.centralizerIn, Section2.elementCentralizer,
        elementCentralizerIn] using hy
    rcases r.property with ⟨w, hwW1, hwq⟩
    have hw_sub_ne : (⟨w, hwW1⟩ : W1.subgroupOf M) ≠ 1 := by
      intro hwone
      apply hr
      apply Subtype.ext
      calc
        (r : M ⧸ K.subgroupOf M) = qM w := hwq.symm
        _ = 1 := by
          have hwoneM : w = 1 := congrArg Subtype.val hwone
          simp [qM, hwoneM]
    let R0 : Subgroup M := Subgroup.zpowers w
    have hR0_le_W1 : R0 ≤ W1.subgroupOf M :=
      (Subgroup.zpowers_le).2 hwW1
    have hR0normD :
        R0 ≤ Subgroup.normalizer (((ambientDerivedSubgroup M).subgroupOf M) : Set M) := by
      exact hR0_le_W1.trans
        (Subgroup.le_normalizer_of_normal
          (H := (ambientDerivedSubgroup M).subgroupOf M))
    have hR0card_dvd_W1 : Nat.card R0 ∣ Nat.card (W1.subgroupOf M) := by
      rw [← natCard_subgroupOf_eq R0 (W1.subgroupOf M) hR0_le_W1]
      exact Subgroup.card_subgroup_dvd_card (R0.subgroupOf (W1.subgroupOf M))
    have hcopDR0 :
        Nat.Coprime (Nat.card ((ambientDerivedSubgroup M).subgroupOf M))
          (Nat.card R0) :=
      Nat.Coprime.of_dvd_right hR0card_dvd_W1 hcopD_W1sub
    have hKinv : ∀ r0 : R0, ∀ x ∈ K.subgroupOf M,
        (r0 : M) * x * (r0 : M)⁻¹ ∈ K.subgroupOf M := by
      intro r0 x hx
      exact (inferInstance : (K.subgroupOf M).Normal).conj_mem x hx (r0 : M)
    have hcentSubQuot :
        subgroupCentralizerIn
            (((ambientDerivedSubgroup M).subgroupOf M).map qM) (R0.map qM) =
          (subgroupCentralizerIn ((ambientDerivedSubgroup M).subgroupOf M) R0).map qM :=
      subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
        ((ambientDerivedSubgroup M).subgroupOf M) R0 (K.subgroupOf M)
        hR0normD hsolvDsub hcopDR0 hKinv
    have hySub :
        y ∈ subgroupCentralizerIn
          (((ambientDerivedSubgroup M).subgroupOf M).map qM) (R0.map qM) := by
      refine ⟨hyElem.1, ?_⟩
      change y ∈ Subgroup.centralizer
        ((R0.map qM : Subgroup (M ⧸ K.subgroupOf M)) :
          Set (M ⧸ K.subgroupOf M))
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases hz with ⟨b, hbR0, hbz⟩
      rcases Subgroup.mem_zpowers_iff.mp hbR0 with ⟨n, hn⟩
      have hcomm_r :
          y * (r : M ⧸ K.subgroupOf M) =
            (r : M ⧸ K.subgroupOf M) * y :=
        Subgroup.mem_centralizer_singleton_iff.mp hyElem.2
      have hcomm_qw : Commute y (qM w) := by
        change y * qM w = qM w * y
        rw [hwq]
        exact hcomm_r
      have hcomm_qb : Commute y (qM b) := by
        rw [← hn]
        simpa [qM] using hcomm_qw.zpow_right n
      calc
        z * y = qM b * y := by rw [hbz]
        _ = y * qM b := hcomm_qb.eq.symm
        _ = y * z := by rw [hbz]
    have hymap :
        y ∈ (subgroupCentralizerIn ((ambientDerivedSubgroup M).subgroupOf M) R0).map qM := by
      simpa [hcentSubQuot] using hySub
    rcases hymap with ⟨z, hzcent, hzy⟩
    have hcent_w :
        elementCentralizerIn ((ambientDerivedSubgroup M).subgroupOf M) w =
          W2.subgroupOf M := by
      simpa [Section2.centralizerIn, Section2.elementCentralizer,
        elementCentralizerIn] using hcentW1 ⟨w, hwW1⟩ hw_sub_ne
    have hzElem :
        z ∈ elementCentralizerIn ((ambientDerivedSubgroup M).subgroupOf M) w := by
      refine ⟨hzcent.1, ?_⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hcomm : w * z = z * w :=
        Subgroup.mem_centralizer_iff.mp hzcent.2 w (Subgroup.mem_zpowers w)
      exact hcomm.symm
    have hzW2 : z ∈ W2.subgroupOf M := by
      simpa [hcent_w] using hzElem
    exact ⟨z, hzW2, hzy⟩
  · intro y hy
    rcases r.property with ⟨w, hwW1, hwq⟩
    rcases hy with ⟨z, hzW2, hzy⟩
    have hw_sub_ne : (⟨w, hwW1⟩ : W1.subgroupOf M) ≠ 1 := by
      intro hwone
      apply hr
      apply Subtype.ext
      calc
        (r : M ⧸ K.subgroupOf M) = qM w := hwq.symm
        _ = 1 := by
          have hwoneM : w = 1 := congrArg Subtype.val hwone
          simp [qM, hwoneM]
    have hcent_w :
        elementCentralizerIn ((ambientDerivedSubgroup M).subgroupOf M) w =
          W2.subgroupOf M := by
      simpa [Section2.centralizerIn, Section2.elementCentralizer,
        elementCentralizerIn] using hcentW1 ⟨w, hwW1⟩ hw_sub_ne
    have hzElem :
        z ∈ elementCentralizerIn ((ambientDerivedSubgroup M).subgroupOf M) w := by
      simpa [hcent_w] using hzW2
    have hyD : y ∈ (((ambientDerivedSubgroup M).subgroupOf M).map qM) :=
      ⟨z, hzElem.1, hzy⟩
    have hcomm_zw : z * w = w * z :=
      Subgroup.mem_centralizer_singleton_iff.mp hzElem.2
    have hycomm :
        y * (r : M ⧸ K.subgroupOf M) =
          (r : M ⧸ K.subgroupOf M) * y := by
      calc
        y * (r : M ⧸ K.subgroupOf M) = qM z * qM w := by rw [hzy, hwq]
        _ = qM (z * w) := by rw [map_mul]
        _ = qM (w * z) := by rw [hcomm_zw]
        _ = qM w * qM z := by rw [map_mul]
        _ = (r : M ⧸ K.subgroupOf M) * y := by rw [hzy, hwq]
    refine ⟨hyD, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hycomm

private theorem theorem_9_nb_redM_M_mod_K_hypothesis_4_2_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  letI : (K.subgroupOf M).Normal := hKnormal
                  let qM : M →* M ⧸ K.subgroupOf M :=
                    QuotientGroup.mk' (K.subgroupOf M)
                  Section4.hypothesis_4_2_statement
                    (((ambientDerivedSubgroup M).subgroupOf M).map qM)
                    ((W1.subgroupOf M).map qM)
                    ((W2.subgroupOf M).map qM)
                    (((W1 ⊔ W2).subgroupOf M).map qM) := by
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change Section4.hypothesis_4_2_statement
    (((ambientDerivedSubgroup M).subgroupOf M).map qM)
    ((W1.subgroupOf M).map qM)
    ((W2.subgroupOf M).map qM)
    (((W1 ⊔ W2).subgroupOf M).map qM)
  have hdirect :
      Section2.IsInternalDirectProduct
        (((W1 ⊔ W2).subgroupOf M).map qM)
        ((W1.subgroupOf M).map qM)
        ((W2.subgroupOf M).map qM) :=
    theorem_9_nb_redM_M_mod_K_quotient_internalDirectProduct_sec9
      M MF U W1 W2 K q h92 hKnormal hKD
  exact
    ⟨theorem_9_nb_redM_M_mod_K_quotient_semidirect_sec9
        M MF U W1 W2 K q h92 hKnormal hKD,
      theorem_9_nb_redM_W1_map_mk_K_isHall_sec9
        M MF U W1 W2 K q h92 hKnormal,
      theorem_9_nb_redM_W1_map_mk_K_isCyclic_sec9
        M MF U W1 W2 K q h92 hKnormal,
      theorem_9_nb_redM_W1_map_mk_K_card_ne_one_sec9
        M MF U W1 W2 K q h92 hKnormal hKD,
      theorem_9_nb_redM_W2_map_mk_K_isCyclic_source_core_sec9
        M MF U W1 W2 H0 K q h92 hKnormal,
      natCard_ne_one_of_eq_prime_sec9 hpprime
        (theorem_9_nb_redM_W2_map_mk_K_card_eq_source_core_sec9
          M MF U W1 W2 H0 K p q h92 hH0MF hpprime hpData hKnormal hKD hKinf),
      theorem_9_nb_redM_M_mod_K_quotient_centralizer_sec9
        M MF U W1 W2 K q h92 hKnormal hKD,
      hdirect.left_le,
      hdirect.right_le,
      hdirect,
      theorem_9_nb_redM_M_mod_K_quotient_W_odd_sec9
        M W1 W2 K hKnormal⟩


private def quotientReducibleFamilyTransportData_sec9
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (p : ℕ)
    (S : Finset (Section1.ClassFunction M)) : Prop :=
  ∃ ι : Type u, ∃ instFintype : Fintype ι, ∃ instDecidableEq : DecidableEq ι,
    letI : Fintype ι := instFintype
    letI : DecidableEq ι := instDecidableEq
    ∃ μ : ι → Section1.ClassFunction M,
      Function.Injective μ ∧
        Fintype.card ι = p - 1 ∧
        (∀ i : ι,
          μ i ∈ S ∧ ¬ Section1.IsIrreducibleCharacterOnGroup (μ i)) ∧
        ∀ χ : Section1.ClassFunction M,
          χ ∈ S →
            ¬ Section1.IsIrreducibleCharacterOnGroup χ →
              ∃ i : ι, μ i = χ


private theorem theorem_9_reducible_filter_card_of_transport_data_sec9
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    {p : ℕ}
    {S : Finset (Section1.ClassFunction M)} :
    quotientReducibleFamilyTransportData_sec9 M p S →
        (reducibleCharacterFilter_sec9 M S).card = p - 1 := by
  classical
  intro hdata
  rcases hdata with ⟨ι, instFintype, instDecidableEq, μ, hμinj, hcard, hmem, hall⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  let R : Finset (Section1.ClassFunction M) := Finset.univ.image μ
  have hRcard : R.card = Fintype.card ι := by
    simpa [R] using
      (Finset.card_image_of_injective (Finset.univ : Finset ι) hμinj)
  have hRmem :
      ∀ χ : Section1.ClassFunction M,
        χ ∈ R ↔ χ ∈ S ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
    intro χ
    constructor
    · intro hχ
      rcases Finset.mem_image.mp hχ with ⟨i, _hi, rfl⟩
      exact hmem i
    · intro hχ
      rcases hall χ hχ.1 hχ.2 with ⟨i, rfl⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hReq : R = reducibleCharacterFilter_sec9 M S := by
    ext χ
    simpa [reducibleCharacterFilter_sec9] using hRmem χ
  rw [← hReq]
  exact hRcard.trans hcard


private def nbRedMQuotientTransportData_sec9
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G) [_hKnormal : (K.subgroupOf M).Normal]
    (_Wbar : Subgroup (M ⧸ K.subgroupOf M))
    (p : ℕ)
    (S : Finset (Section1.ClassFunction M)) : Prop :=
  ∃ ι : Type u, ∃ instFintype : Fintype ι, ∃ instDecidableEq : DecidableEq ι,
    letI : Fintype ι := instFintype
    letI : DecidableEq ι := instDecidableEq
    ∃ μ : ι → Section1.ClassFunction M,
      Function.Injective μ ∧
      Fintype.card ι = p - 1 ∧
      (∀ i : ι,
        μ i ∈ S ∧ ¬ Section1.IsIrreducibleCharacterOnGroup (μ i)) ∧
      ∀ χ : Section1.ClassFunction M,
        χ ∈ S →
          ¬ Section1.IsIrreducibleCharacterOnGroup χ →
            ∃ i : ι, μ i = χ

private def nbRedMQuotientLowerTransportData_sec9
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G) [_hKnormal : (K.subgroupOf M).Normal]
    (_Wbar : Subgroup (M ⧸ K.subgroupOf M))
    (p : ℕ)
    (S : Finset (Section1.ClassFunction M)) : Prop :=
  ∃ ι : Type u, ∃ instFintype : Fintype ι, ∃ instDecidableEq : DecidableEq ι,
    letI : Fintype ι := instFintype
    letI : DecidableEq ι := instDecidableEq
    ∃ μ : ι → Section1.ClassFunction M,
      Function.Injective μ ∧
      Fintype.card ι = p - 1 ∧
      ∀ i : ι,
        μ i ∈ S ∧ ¬ Section1.IsIrreducibleCharacterOnGroup (μ i)

private theorem quotientReducibleFamilyTransportData_of_nbRedMQuotientTransportData_sec9
    {G : Type u} [Group G] [Finite G]
    {M K : Subgroup G} [hKnormal : (K.subgroupOf M).Normal]
    {Wbar : Subgroup (M ⧸ K.subgroupOf M)}
    {p : ℕ}
    {S : Finset (Section1.ClassFunction M)} :
    nbRedMQuotientTransportData_sec9 M K Wbar p S →
      quotientReducibleFamilyTransportData_sec9 M p S := by
  intro hdata
  rcases hdata with
    ⟨ι, instFintype, instDecidableEq, μ, hμinj, hcard, hmem, hall⟩
  refine ⟨ι, instFintype, instDecidableEq, ?_⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  exact ⟨μ, hμinj, hcard, hmem, hall⟩

private theorem le_normalizer_sup_of_le_normalizer_sec9
    {G : Type u} [Group G] (A B N : Subgroup G)
    (hNA : N ≤ Subgroup.normalizer (A : Set G))
    (hNB : N ≤ Subgroup.normalizer (B : Set G)) :
    N ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hsup_closure :
        A ⊔ B = Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    have hxcl : x ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
      simpa [hsup_closure] using hx
    refine Subgroup.closure_induction (k := ((A : Set G) ∪ (B : Set G)))
      (p := fun y _hy => n * y * n⁻¹ ∈ (A ⊔ B : Subgroup G)) ?_ ?_ ?_ ?_
      hxcl
    · intro y hy
      rcases hy with hyA | hyB
      · exact (le_sup_left : A ≤ A ⊔ B)
          ((Subgroup.mem_normalizer_iff.mp (hNA hn) y).mp hyA)
      · exact (le_sup_right : B ≤ A ⊔ B)
          ((Subgroup.mem_normalizer_iff.mp (hNB hn) y).mp hyB)
    · simp
    · intro y z _hy _hz hyP hzP
      simpa [mul_assoc] using (A ⊔ B).mul_mem hyP hzP
    · intro y _hy hyP
      simpa [mul_assoc] using (A ⊔ B).inv_mem hyP
  · intro hx
    have hninv : n⁻¹ ∈ N := N.inv_mem hn
    have hforward_inv :
        ∀ y : G, y ∈ A ⊔ B → n⁻¹ * y * (n⁻¹)⁻¹ ∈ (A ⊔ B : Subgroup G) := by
      intro y hy
      have hsup_closure :
          A ⊔ B = Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
        rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
      have hycl : y ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
        simpa [hsup_closure] using hy
      refine Subgroup.closure_induction (k := ((A : Set G) ∪ (B : Set G)))
        (p := fun z _hz => n⁻¹ * z * (n⁻¹)⁻¹ ∈ (A ⊔ B : Subgroup G))
        ?_ ?_ ?_ ?_ hycl
      · intro z hz
        rcases hz with hzA | hzB
        · exact (le_sup_left : A ≤ A ⊔ B)
            ((Subgroup.mem_normalizer_iff.mp (hNA hninv) z).mp hzA)
        · exact (le_sup_right : B ≤ A ⊔ B)
            ((Subgroup.mem_normalizer_iff.mp (hNB hninv) z).mp hzB)
      · simp
      · intro z w _hz _hw hzP hwP
        simpa [mul_assoc] using (A ⊔ B).mul_mem hzP hwP
      · intro z _hz hzP
        simpa [mul_assoc] using (A ⊔ B).inv_mem hzP
    have := hforward_inv (n * x * n⁻¹) hx
    simpa [mul_assoc] using this

private theorem conj_mem_sup_of_commutator_mem_left_sec9
    {G : Type u} [Group G]
    {A B : Subgroup G} {n b : G}
    (hb : b ∈ B) (hcomm : ⁅b, n⁆ ∈ A) :
    n * b * n⁻¹ ∈ A ⊔ B := by
  have hcomm_inv : ⁅b, n⁆⁻¹ ∈ A := A.inv_mem hcomm
  have heq : n * b * n⁻¹ = ⁅b, n⁆⁻¹ * b := by
    simp [commutatorElement_def, mul_assoc]
  rw [heq]
  exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left hcomm_inv) (Subgroup.mem_sup_right hb)

private theorem le_normalizer_sup_of_le_normalizer_left_commutator_right_sec9
    {G : Type u} [Group G]
    (A B N : Subgroup G)
    (hNA : N ≤ Subgroup.normalizer (A : Set G))
    (hcomm : ∀ n : G, n ∈ N → ∀ b : G, b ∈ B → ⁅b, n⁆ ∈ A) :
    N ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hsup_closure :
        A ⊔ B = Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    have hxcl : x ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
      simpa [hsup_closure] using hx
    refine Subgroup.closure_induction (k := ((A : Set G) ∪ (B : Set G)))
      (p := fun y _hy => n * y * n⁻¹ ∈ (A ⊔ B : Subgroup G)) ?_ ?_ ?_ ?_
      hxcl
    · intro y hy
      rcases hy with hyA | hyB
      · exact (le_sup_left : A ≤ A ⊔ B)
          ((Subgroup.mem_normalizer_iff.mp (hNA hn) y).mp hyA)
      · exact conj_mem_sup_of_commutator_mem_left_sec9 hyB (hcomm n hn y hyB)
    · simp
    · intro y z _hy _hz hyP hzP
      simpa [mul_assoc] using (A ⊔ B).mul_mem hyP hzP
    · intro y _hy hyP
      simpa [mul_assoc] using (A ⊔ B).inv_mem hyP
  · intro hx
    have hninv : n⁻¹ ∈ N := N.inv_mem hn
    have hforward_inv :
        ∀ y : G, y ∈ A ⊔ B → n⁻¹ * y * (n⁻¹)⁻¹ ∈ (A ⊔ B : Subgroup G) := by
      intro y hy
      have hsup_closure :
          A ⊔ B = Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
        rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
      have hycl : y ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
        simpa [hsup_closure] using hy
      refine Subgroup.closure_induction (k := ((A : Set G) ∪ (B : Set G)))
        (p := fun z _hz => n⁻¹ * z * (n⁻¹)⁻¹ ∈ (A ⊔ B : Subgroup G))
        ?_ ?_ ?_ ?_ hycl
      · intro z hz
        rcases hz with hzA | hzB
        · exact (le_sup_left : A ≤ A ⊔ B)
            ((Subgroup.mem_normalizer_iff.mp (hNA hninv) z).mp hzA)
        · exact conj_mem_sup_of_commutator_mem_left_sec9 hzB
            (hcomm n⁻¹ hninv z hzB)
      · simp
      · intro z w _hz _hw hzP hwP
        simpa [mul_assoc] using (A ⊔ B).mul_mem hzP hwP
      · intro z _hz hzP
        simpa [mul_assoc] using (A ⊔ B).inv_mem hzP
    have := hforward_inv (n * x * n⁻¹) hx
    simpa [mul_assoc] using this

private theorem quotientCentralizerIn_le_normalizer_of_le_normalizers_sec9
    {G : Type u} [Group G]
    {M MF U H0 C N : Subgroup G}
    (hNleM : N ≤ M)
    (hNnormU : N ≤ Subgroup.normalizer (U : Set G))
    (hNnormMF : N ≤ Subgroup.normalizer (MF : Set G))
    (hH0leM : H0 ≤ M)
    (hH0normalM : (H0.subgroupOf M).Normal)
    (hC : quotientCentralizerIn MF H0 U C) :
    N ≤ Subgroup.normalizer (C : Set G) := by
  have hforward :
      ∀ n : G, n ∈ N → ∀ x : G, x ∈ C → n * x * n⁻¹ ∈ C := by
    intro n hn x hxC
    have hxU : x ∈ U := hC.1 hxC
    have hconjU : n * x * n⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hNnormU hn) x).mp hxU
    rw [(hC.2 (n * x * n⁻¹) hconjU)]
    intro h hhMF
    have hninv_normMF : n⁻¹ ∈ Subgroup.normalizer (MF : Set G) :=
      (Subgroup.normalizer (MF : Set G)).inv_mem (hNnormMF hn)
    have hh' : n⁻¹ * h * n ∈ MF := by
      simpa [mul_assoc] using
        (Subgroup.mem_normalizer_iff.mp hninv_normMF h).mp hhMF
    have hcomm : ⁅x, n⁻¹ * h * n⁆ ∈ H0 :=
      (hC.2 x hxU).mp hxC (n⁻¹ * h * n) hh'
    let nM : M := ⟨n, hNleM hn⟩
    let cM : M := ⟨⁅x, n⁻¹ * h * n⁆, hH0leM hcomm⟩
    have hcM : cM ∈ H0.subgroupOf M := by
      simpa [cM, Subgroup.mem_subgroupOf] using hcomm
    have hconjM : nM * cM * nM⁻¹ ∈ H0.subgroupOf M :=
      hH0normalM.conj_mem cM hcM nM
    have hconjH0 : n * ⁅x, n⁻¹ * h * n⁆ * n⁻¹ ∈ H0 := by
      simpa [nM, cM, Subgroup.mem_subgroupOf] using hconjM
    have hcomm_eq :
        ⁅n * x * n⁻¹, h⁆ = n * ⁅x, n⁻¹ * h * n⁆ * n⁻¹ := by
      simp [commutatorElement_def]
      group
    rw [hcomm_eq]
    exact hconjH0
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward n hn x
  · intro hx
    have hninv : n⁻¹ ∈ N := N.inv_mem hn
    have hmem := hforward n⁻¹ hninv (n * x * n⁻¹) hx
    simpa [mul_assoc] using hmem

private theorem subgroupOf_subgroupOf_normal_of_le_normalizer_sec9
    {G : Type u} [Group G] {M D H : Subgroup G}
    (hHD : H ≤ D) (hDnormH : D ≤ Subgroup.normalizer (H : Set G)) :
    ((H.subgroupOf M).subgroupOf (D.subgroupOf M)).Normal := by
  have hHmDm : H.subgroupOf M ≤ D.subgroupOf M := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hHD hx
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hHmDm).2 ?_
  intro d hdD
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hdG : ((d : M) : G) ∈ D := by
      simpa [Subgroup.mem_subgroupOf] using hdD
    have hxG : ((x : M) : G) ∈ H := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hconjG : ((d : M) : G) * ((x : M) : G) * ((d : M) : G)⁻¹ ∈ H :=
      ((Subgroup.mem_normalizer_iff.mp (hDnormH hdG) ((x : M) : G)).mp hxG)
    simpa [Subgroup.mem_subgroupOf] using hconjG
  · intro hx
    have hdG : ((d : M) : G) ∈ D := by
      simpa [Subgroup.mem_subgroupOf] using hdD
    have hconjG : ((d : M) : G) * ((x : M) : G) * ((d : M) : G)⁻¹ ∈ H := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxG : ((x : M) : G) ∈ H :=
      ((Subgroup.mem_normalizer_iff.mp (hDnormH hdG) ((x : M) : G)).mpr hconjG)
    simpa [Subgroup.mem_subgroupOf] using hxG

private theorem normalizer_le_normalizer_commutator_self_sec9
    {G : Type u} [Group G] (C U : Subgroup G)
    (hU_norm_C : U ≤ Subgroup.normalizer (C : Set G)) :
    U ≤ Subgroup.normalizer ((⁅C, C⁆ : Subgroup G) : Set G) := by
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← Subgroup.map_subtype_commutator C] at hx ⊢
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    let φ : C ≃* C :=
      { toFun := fun c =>
          ⟨u * (c : G) * u⁻¹,
            ((Subgroup.mem_normalizer_iff.mp (hU_norm_C hu) (c : G)).mp c.property)⟩
        invFun := fun c =>
          ⟨u⁻¹ * (c : G) * (u⁻¹)⁻¹,
            ((Subgroup.mem_normalizer_iff.mp
              (hU_norm_C (U.inv_mem hu)) (c : G)).mp c.property)⟩
        left_inv := by
          intro c
          apply Subtype.ext
          simp [mul_assoc]
        right_inv := by
          intro c
          apply Subtype.ext
          simp [mul_assoc]
        map_mul' := by
          intro a b
          apply Subtype.ext
          simp [mul_assoc] }
    refine ⟨φ y, ?_, ?_⟩
    · have hycomap : y ∈ (commutator C).comap φ.toMonoidHom := by
        exact (SetLike.ext_iff.mp
          ((inferInstance : (commutator C).Characteristic).fixed φ) y).mpr hy
      simpa [Subgroup.mem_comap] using hycomap
    · simpa [φ, hyx]
  · intro hx
    rw [← Subgroup.map_subtype_commutator C] at hx ⊢
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    let φ : C ≃* C :=
      { toFun := fun c =>
          ⟨u⁻¹ * (c : G) * (u⁻¹)⁻¹,
            ((Subgroup.mem_normalizer_iff.mp
              (hU_norm_C (U.inv_mem hu)) (c : G)).mp c.property)⟩
        invFun := fun c =>
          ⟨u * (c : G) * u⁻¹,
            ((Subgroup.mem_normalizer_iff.mp (hU_norm_C hu) (c : G)).mp c.property)⟩
        left_inv := by
          intro c
          apply Subtype.ext
          simp [mul_assoc]
        right_inv := by
          intro c
          apply Subtype.ext
          simp [mul_assoc]
        map_mul' := by
          intro a b
          apply Subtype.ext
          simp [mul_assoc] }
    refine ⟨φ y, ?_, ?_⟩
    · have hycomap : y ∈ (commutator C).comap φ.toMonoidHom := by
        exact (SetLike.ext_iff.mp
          ((inferInstance : (commutator C).Characteristic).fixed φ) y).mpr hy
      simpa [Subgroup.mem_comap] using hycomap
    · calc
        C.subtype (φ y) = u⁻¹ * C.subtype y * u := by simp [φ]
        _ = u⁻¹ * (u * x * u⁻¹) * u := by rw [hyx]
        _ = x := by group

private theorem pf4_piColumn_injective_of_xChar_sec9
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar) :
    Function.Injective (fun j : J => Section4Scratch.piColumn piChar j) := by
  classical
  have hresCol :
      ∀ j : J,
        Section1.subgroupRestriction K (Section4Scratch.piColumn piChar j) =
          (Fintype.card I : ℂ) • xChar j := by
    intro j
    ext t
    calc
      Section1.subgroupRestriction K (Section4Scratch.piColumn piChar j) t =
          ∑ i : I, piChar i j t := by
            simp [Section4Scratch.piColumn, Section1.subgroupRestriction]
      _ = ∑ _i : I, xChar j t := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simpa [Section1.subgroupRestriction] using congrFun (h45a.1 i j) t
      _ = (Fintype.card I : ℂ) * xChar j t := by
            simp [Finset.sum_const]
      _ = ((Fintype.card I : ℂ) • xChar j) t := by
            simp
  have hcardI_ne : (Fintype.card I : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i0⟩).ne'
  have hxInj : Function.Injective xChar :=
    Section4Scratch.xChar_injective_pf45 K piChar xChar h45a i0 j0 ω σ
      deltaSign hω h43b
  intro j k hEq
  have hsmul :
      (Fintype.card I : ℂ) • xChar j =
        (Fintype.card I : ℂ) • xChar k := by
    calc
      (Fintype.card I : ℂ) • xChar j =
          Section1.subgroupRestriction K (Section4Scratch.piColumn piChar j) :=
        (hresCol j).symm
      _ = Section1.subgroupRestriction K (Section4Scratch.piColumn piChar k) := by
        exact congrArg (Section1.subgroupRestriction K) hEq
      _ = (Fintype.card I : ℂ) • xChar k :=
        hresCol k
  have hxEq : xChar j = xChar k := by
    ext t
    have ht := congrFun hsmul t
    exact mul_left_cancel₀ hcardI_ne (by simpa using ht)
  exact hxInj hxEq

private def nbRedMPF4QuotientColumnData_sec9
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (p : ℕ) : Prop :=
  ∃ I : Type u, ∃ J : Type u,
    ∃ instFintypeI : Fintype I, ∃ instFintypeJ : Fintype J,
      ∃ instDecidableEqI : DecidableEq I, ∃ instDecidableEqJ : DecidableEq J,
        letI : Fintype I := instFintypeI
        letI : Fintype J := instFintypeJ
        letI : DecidableEq I := instDecidableEqI
        letI : DecidableEq J := instDecidableEqJ
        ∃ i0 : I, ∃ j0 : J,
          ∃ ω : I → J → Section1.ClassFunction W,
            ∃ hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω,
              ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L,
                ∃ piChar : I → J → Section1.ClassFunction L,
                  ∃ deltaSign : J → ℂ,
                    ∃ xChar : J → Section1.ClassFunction K,
                      Section4.theorem_4_3_b_statement
                        W1 W2 W I J i0 j0 ω σ piChar deltaSign hω ∧
                      Section4.theorem_4_3_c_statement
                        W2 W I J piChar deltaSign ω ∧
                      Section4Scratch.theorem_4_5_a_statement K piChar xChar ∧
                      Section4Scratch.theorem_4_5_b_statement K piChar xChar ∧
                      deltaSign j0 = 1 ∧
                      piChar i0 j0 = Section1.principalCharacter L ∧
                      Function.Injective
                        (fun j : J => Section4Scratch.piColumn piChar j) ∧
                      (Finset.univ.erase j0).card = p - 1

private theorem theorem_9_nb_redM_quotient_notation_3_3_source_core_sec9
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L) :
    Section4.hypothesis_4_2_statement K W1 W2 W →
      ∃ I : Type u, ∃ J : Type u,
        ∃ instFintypeI : Fintype I, ∃ instFintypeJ : Fintype J,
          ∃ instDecidableEqI : DecidableEq I, ∃ instDecidableEqJ : DecidableEq J,
            letI : Fintype I := instFintypeI
            letI : Fintype J := instFintypeJ
            letI : DecidableEq I := instDecidableEqI
            letI : DecidableEq J := instDecidableEqJ
            ∃ i0 : I, ∃ j0 : J,
              ∃ ω : I → J → Section1.ClassFunction W,
                Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω := by
  intro h42
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
    (Section4.theorem_4_3_a K W1 W2 W h42).2
  exact Section3.exists_notation_3_3_of_hypothesis_3_1 h31

private theorem theorem_9_nb_redM_pf4_quotient_column_data_of_notation_sec9
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (p : ℕ) :
    Section4.hypothesis_4_2_statement K W1 W2 W →
      Nat.card W2 = p →
        (∃ I : Type u, ∃ J : Type u,
          ∃ instFintypeI : Fintype I, ∃ instFintypeJ : Fintype J,
            ∃ instDecidableEqI : DecidableEq I, ∃ instDecidableEqJ : DecidableEq J,
              letI : Fintype I := instFintypeI
              letI : Fintype J := instFintypeJ
              letI : DecidableEq I := instDecidableEqI
              letI : DecidableEq J := instDecidableEqJ
              ∃ i0 : I, ∃ j0 : J,
                ∃ ω : I → J → Section1.ClassFunction W,
                  Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω) →
          nbRedMPF4QuotientColumnData_sec9 K W1 W2 W p := by
  classical
  intro h42 hW2card hnotation
  rcases hnotation with
    ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
      i0, j0, ω, hω⟩
  letI : Fintype I := instFintypeI
  letI : Fintype J := instFintypeJ
  letI : DecidableEq I := instDecidableEqI
  letI : DecidableEq J := instDecidableEqJ
  rcases Section4.theorem_4_3 K W1 W2 W I J i0 j0 ω h42 hω with
    ⟨_h43a, σ, piChar, deltaSign, h43b, h43c, _h43d⟩
  rcases Section4Scratch.theorem_4_5 K W1 W2 W i0 j0 ω σ piChar deltaSign
      h42 hω h43b h43c with
    ⟨xChar, h45a, h45b⟩
  have h44 := Section4.proposition_4_4 K W1 W2 W I J i0 j0 ω σ
    piChar deltaSign h42 hω h43b h43c
  have hpiColumnInj :
      Function.Injective (fun j : J => Section4Scratch.piColumn piChar j) :=
    pf4_piColumn_injective_of_xChar_sec9
      (K := K) (W1 := W1) (W2 := W2) (W := W) (i0 := i0) (j0 := j0)
      (ω := ω) (σ := σ) (piChar := piChar) (xChar := xChar)
      (deltaSign := deltaSign) hω h43b h45a
  have hJcard : Fintype.card J = p := by
    calc
      Fintype.card J = Nat.card W2 := hω.card_right
      _ = p := hW2card
  have hnonbaseCard : (Finset.univ.erase j0).card = p - 1 := by
    calc
      (Finset.univ.erase j0).card = Fintype.card J - 1 := by simp
      _ = p - 1 := by rw [hJcard]
  refine
    ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
      i0, j0, ω, hω, σ, piChar, deltaSign, xChar, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, hnonbaseCard⟩
  · exact h43b
  · exact h43c
  · exact h45a
  · exact h45b
  · exact h44.2.1
  · exact h44.2.2
  · exact hpiColumnInj

private theorem pf4_exists_ne_one_mem_of_natCard_ne_one_sec9
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) (hK : Nat.card K ≠ 1) :
    ∃ x, x ∈ K ∧ x ≠ 1 := by
  by_contra hcontra
  have hforall : ∀ x : K, x = 1 := by
    intro x
    by_contra hx
    have hx' : (x : L) ≠ 1 := by
      intro hx1
      exact hx (Subtype.ext hx1)
    exact hcontra ⟨x, x.2, hx'⟩
  have hcard : Nat.card K = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨1, fun x => hforall x⟩
  exact hK hcard

private theorem pf4_w2_le_K_of_hypothesis_4_2_sec9
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W) :
    W2 ≤ K := by
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, hcard1, _hcyc2, _hcard2,
    hcent, _hW1, _hW2, _hW, _hodd⟩
  rcases pf4_exists_ne_one_mem_of_natCard_ne_one_sec9 W1 hcard1 with
    ⟨x, hxW1, hx1⟩
  have hcentx : Section2.centralizerIn K x = W2 := by
    exact hcent ⟨x, hxW1⟩ (by
      intro hxsub
      exact hx1 (Subtype.ext_iff.mp hxsub))
  intro z hz
  have hz' : z ∈ Section2.centralizerIn K x := by
    simpa [hcentx] using hz
  exact (Subgroup.mem_inf.mp hz').1

private theorem pf4_hypothesis_4_6_self_of_hypothesis_4_2_sec9
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W) :
    Section4Scratch.hypothesis_4_6_statement K W1 W2 W K
      ({x : L | x ∈ K ∧ x ≠ 1}) := by
  classical
  have h42' := h42
  rcases h42 with ⟨hsemi, _hHall, _hcyc1, _hW1card, _hcyc2, _hW2card,
    _hcent, _hW1, hW2, _hW, _hodd⟩
  have hKnorm : K.Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rcases hsemi.mul_surjective g trivial with ⟨k, hk, w, hw, hg⟩
    rw [hg]
    have hconjW : Section2.conjBy w n ∈ K := hsemi.right_normalizes_left w hw n hn
    have hconj : k * (w * n * w⁻¹) * k⁻¹ ∈ K := by
      exact K.mul_mem (K.mul_mem hk hconjW) (K.inv_mem hk)
    simpa [Section2.conjBy, mul_assoc] using hconj
  have hW2K : W2 ≤ K := pf4_w2_le_K_of_hypothesis_4_2_sec9 h42'
  refine ⟨⟨hsemi, _hHall, _hcyc1, _hW1card, _hcyc2, _hW2card,
    _hcent, _hW1, hW2, _hW, _hodd⟩, hKnorm, ?_, le_rfl, ?_, ?_⟩
  · exact hW2K
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hxk⟩
    exact ⟨(Subgroup.mem_inf.mp hxk.1).1, by simpa using hxk.2⟩
  · intro x hx
    exact hx

private theorem pf4_hypothesis_4_6_mf_quotient_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ)
    (h92 : hypothesis_9_2_statement M MF U W1 W2 q)
    (hKnormal : (K.subgroupOf M).Normal) :
    letI : (K.subgroupOf M).Normal := hKnormal
    let qM : M →* M ⧸ K.subgroupOf M :=
      QuotientGroup.mk' (K.subgroupOf M)
    let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
      ((ambientDerivedSubgroup M).subgroupOf M).map qM
    let W1bar : Subgroup (M ⧸ K.subgroupOf M) :=
      (W1.subgroupOf M).map qM
    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
      (W2.subgroupOf M).map qM
    let Wbar : Subgroup (M ⧸ K.subgroupOf M) :=
      ((W1 ⊔ W2).subgroupOf M).map qM
    let Hbar : Subgroup (M ⧸ K.subgroupOf M) :=
      (MF.subgroupOf M).map qM
    Section4.hypothesis_4_2_statement Kbar W1bar W2bar Wbar →
      Section4Scratch.hypothesis_4_6_statement Kbar W1bar W2bar Wbar Hbar
        ({x : M ⧸ K.subgroupOf M | x ∈ Kbar ∧ x ≠ 1}) := by
  classical
  intro qM Kbar W1bar W2bar Wbar Hbar h42q
  have hMFnormalM : (MF.subgroupOf M).Normal := by
    rcases h92.mf.1 with ⟨_hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
    exact hMFnormalM
  have hHbarNormal : Hbar.Normal := by
    simpa [Hbar, qM] using
      (hMFnormalM.map qM (QuotientGroup.mk'_surjective (K.subgroupOf M)))
  have hW2MF : W2 ≤ MF := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
        _hFittingLeD, hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
    exact hW2le.trans inf_le_left
  have hMFD : MF ≤ ambientDerivedSubgroup M :=
    MF_le_ambientDerived_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hW2barHbar : W2bar ≤ Hbar := by
    intro x hx
    rcases hx with ⟨y, hyW2, hxy⟩
    refine ⟨y, ?_, hxy⟩
    have hyW2G : ((y : M) : G) ∈ W2 := by
      simpa [Subgroup.mem_subgroupOf] using hyW2
    simpa [Subgroup.mem_subgroupOf] using hW2MF hyW2G
  have hHbarKbar : Hbar ≤ Kbar := by
    intro x hx
    rcases hx with ⟨y, hyMF, hxy⟩
    refine ⟨y, ?_, hxy⟩
    have hyMFG : ((y : M) : G) ∈ MF := by
      simpa [Subgroup.mem_subgroupOf] using hyMF
    simpa [Subgroup.mem_subgroupOf] using hMFD hyMFG
  refine ⟨h42q, hHbarNormal, hW2barHbar, hHbarKbar, ?_, ?_⟩
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨_h, hxcentral⟩
    exact ⟨(Subgroup.mem_inf.mp hxcentral.1).1, by simpa using hxcentral.2⟩
  · intro x hx
    exact hx


private theorem quotientInflatedCharacter_irreducible_sec9
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [Z.Normal]
    {θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    (hθbar : Section1.IsIrreducibleCharacterOnGroup θbar) :
    Section1.IsIrreducibleCharacterOnGroup
      (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h)) := by
  classical
  rcases hθbar with ⟨n, ρ, hρirr, hθeq⟩
  let qH : H →* H.map (QuotientGroup.mk' Z) := (QuotientGroup.mk' Z).subgroupMap H
  refine ⟨n, ρ.comp qH, ?_, ?_⟩
  · exact Section6.representation_isIrreducible_comp_surjective ρ qH
      (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' Z) H) hρirr
  · ext h
    simp [qH, hθeq, Representation.character]

private theorem quotientInflatedCharacter_subgroupInKernel_sec9
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [Z.Normal]
    (θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))) :
    Section1.subgroupInKernel'
      (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h))
      (Z.subgroupOf H) := by
  classical
  intro z
  let qH : H →* H.map (QuotientGroup.mk' Z) := (QuotientGroup.mk' Z).subgroupMap H
  have hzq : qH z = 1 := by
    apply Subtype.ext
    change QuotientGroup.mk' Z ((z : H) : L) = 1
    exact (QuotientGroup.eq_one_iff (N := Z) (x := ((z : H) : L))).2 z.2
  change θbar (qH z) = θbar (qH 1)
  rw [hzq]
  rfl

private theorem quotientInflatedCharacter_not_subgroupInKernel_of_map_sec9
    {L : Type u} [Group L] [Finite L]
    {H N Z : Subgroup L} [Z.Normal]
    (hHN : H ≤ N)
    {θbar : Section1.ClassFunction (N.map (QuotientGroup.mk' Z))}
    (hnot : ¬ Section1.subgroupInKernel' θbar
      ((H.map (QuotientGroup.mk' Z)).subgroupOf (N.map (QuotientGroup.mk' Z)))) :
    ¬ Section1.subgroupInKernel'
      (fun n : N => θbar (((QuotientGroup.mk' Z).subgroupMap N) n))
      (H.subgroupOf N) := by
  classical
  intro hker
  apply hnot
  intro a
  have haH : ((a : N.map (QuotientGroup.mk' Z)) : L ⧸ Z) ∈
      H.map (QuotientGroup.mk' Z) := by
    exact a.2
  rcases haH with ⟨h, hhH, hha⟩
  let n : N := ⟨h, hHN hhH⟩
  have hnH : n ∈ H.subgroupOf N := by
    simpa [n, Subgroup.mem_subgroupOf] using hhH
  have hq : ((QuotientGroup.mk' Z).subgroupMap N) n =
      (a : N.map (QuotientGroup.mk' Z)) := by
    ext
    exact hha
  calc
    θbar a = θbar (((QuotientGroup.mk' Z).subgroupMap N) n) := by rw [hq]
    _ = Section1.degree
        (fun n : N => θbar (((QuotientGroup.mk' Z).subgroupMap N) n)) :=
          hker ⟨n, hnH⟩
    _ = Section1.degree θbar := by simp [Section1.degree]

private theorem quotientInducedCF_eq_of_inducedCF_eq_sec9
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [H.Normal] [Z.Normal]
    {θ η : Section1.ClassFunction H}
    (h : Section1.inducedCF H θ = Section1.inducedCF H η) :
    Section1.quotientInducedCF H Z θ = Section1.quotientInducedCF H Z η := by
  classical
  ext q
  simp [Section1.quotientInducedCF, h]

private theorem quotientInducedCF_inflated_eq_inducedCF_sec9
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [H.Normal] [Z.Normal]
    (hZH : Z ≤ H)
    {θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    (hθbar : Section1.IsIrreducibleCharacterOnGroup θbar) :
    Section1.quotientInducedCF H Z
      (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h)) =
        Section1.inducedCF (H.map (QuotientGroup.mk' Z)) θbar := by
  classical
  let qH : H →* H.map (QuotientGroup.mk' Z) :=
    (QuotientGroup.mk' Z).subgroupMap H
  rcases hθbar with ⟨n, ρ, _hρirr, hθeq⟩
  let θrep : Representation ℂ H (Fin n → ℂ) := ρ.comp qH
  have hθrep_char :
      θrep.character = fun h : H => θbar (qH h) := by
    ext h
    simp [θrep, qH, hθeq, Representation.character]
  have hker : Section1.subgroupInKernel' θrep.character (Z.subgroupOf H) := by
    rw [hθrep_char]
    exact quotientInflatedCharacter_subgroupInKernel_sec9 θbar
  have hkerRep : Section1.subgroupInRepresentationKernel θrep (Z.subgroupOf H) :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel θrep
      (Z.subgroupOf H)).mp hker
  have hthetaQuot_eq : Section1.quotientThetaCharacter H Z θrep = θbar := by
    ext y
    rcases Section1.quotientImageSubgroup_exists_preimage H Z y with ⟨h, hy⟩
    let hmem : ((h : L) : L ⧸ Z) ∈ Section1.quotientImageSubgroup H Z :=
      ⟨(h : L), h.2, rfl⟩
    have hy' : y = ⟨((h : L) : L ⧸ Z), hmem⟩ := by
      ext
      exact hy.symm
    rw [hy']
    calc
      Section1.quotientThetaCharacter H Z θrep ⟨((h : L) : L ⧸ Z), hmem⟩ =
          θrep.character h := by
            exact Section1.quotientThetaCharacter_mk H Z θrep hkerRep h hmem
      _ = θbar (qH h) := by rw [hθrep_char]
      _ = θbar ⟨((h : L) : L ⧸ Z), hmem⟩ := by rfl
  calc
    Section1.quotientInducedCF H Z
        (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h)) =
        Section1.quotientInducedCF H Z θrep.character := by
          rw [hθrep_char]
    _ = Section1.inducedCF (Section1.quotientImageSubgroup H Z)
          (Section1.quotientThetaCharacter H Z θrep) := by
          exact Section1.proposition_1_6_b_classFunction H Z hZH θrep hker
    _ = Section1.inducedCF (H.map (QuotientGroup.mk' Z)) θbar := by
          simp [Section1.quotientImageSubgroup, hthetaQuot_eq]

private theorem quotientInflatedInducedCF_not_irreducible_of_quotient_sec9
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [H.Normal] [Z.Normal]
    (hZH : Z ≤ H)
    {θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    (hθbar : Section1.IsIrreducibleCharacterOnGroup θbar)
    (hquotRed : ¬ Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF (H.map (QuotientGroup.mk' Z)) θbar)) :
    ¬ Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF H
        (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h))) := by
  classical
  intro horig
  let qH : H →* H.map (QuotientGroup.mk' Z) :=
    (QuotientGroup.mk' Z).subgroupMap H
  rcases hθbar with ⟨m, θρ, hθρirr, hθeq⟩
  let θrep : Representation ℂ H (Fin m → ℂ) := θρ.comp qH
  have hθrep_char :
      θrep.character = fun h : H => θbar (qH h) := by
    ext h
    simp [θrep, qH, hθeq, Representation.character]
  have hθker : Section1.subgroupInKernel' θrep.character (Z.subgroupOf H) := by
    rw [hθrep_char]
    exact quotientInflatedCharacter_subgroupInKernel_sec9 θbar
  have hindKer : Section1.subgroupInKernel'
      (Section1.inducedCF H θrep.character) Z :=
    (Section1.proposition_1_6_a H Z hZH θrep).mp hθker
  have hindKer' : Section1.subgroupInKernel'
      (Section1.inducedCF H (fun h : H => θbar (qH h))) Z := by
    simpa [hθrep_char] using hindKer
  rcases horig with ⟨n, ρ, hρirr, hρeq⟩
  have hρkerCF : Section1.subgroupInKernel' ρ.character Z := by
    simpa [← hρeq, qH] using hindKer'
  have hρkerRep : Section1.subgroupInRepresentationKernel ρ Z :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ Z).mp hρkerCF
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  let ρq : Representation ℂ (L ⧸ Z) (Fin n → ℂ) :=
    Section1.quotientRepresentationOfKernelSubgroup ρ Z hρkerRep
  have hcomp_eq : ρq.comp q = ρ := by
    apply MonoidHom.ext
    intro g
    exact Section1.quotientRepresentationOfKernelSubgroup_mk ρ Z hρkerRep g
  have hρqirr : Representation.IsIrreducible ρq := by
    apply Section6.representation_isIrreducible_of_comp_surjective ρq q
      (QuotientGroup.mk'_surjective Z)
    simpa [hcomp_eq] using hρirr
  have hquotIrr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.quotientInducedCF H Z (fun h : H => θbar (qH h))) := by
    refine ⟨n, ρq, hρqirr, ?_⟩
    symm
    ext y
    rcases QuotientGroup.mk'_surjective Z y with ⟨g, rfl⟩
    calc
      ρq.character (QuotientGroup.mk' Z g) = ρ.character g := by
        simpa [ρq, Representation.character] using
          congrArg (LinearMap.trace ℂ (Fin n → ℂ))
            (Section1.quotientRepresentationOfKernelSubgroup_mk ρ Z hρkerRep g)
      _ = Section1.inducedCF H (fun h : H => θbar (qH h)) g := by
        change ρ.character g =
          Section1.inducedCF H
            (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h)) g
        exact (congrFun hρeq g).symm
      _ = Section1.quotientInducedCF H Z (fun h : H => θbar (qH h))
            (QuotientGroup.mk' Z g) := by
        rw [← hθrep_char]
        exact (Section1.quotientInducedCF_mk H Z hZH θrep
          ((Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel θrep
            (Z.subgroupOf H)).mp hθker) g).symm
  have hqeq := quotientInducedCF_inflated_eq_inducedCF_sec9
    (H := H) (Z := Z) hZH (θbar := θbar) ⟨m, θρ, hθρirr, hθeq⟩
  have hquotIrr' : Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF (H.map (QuotientGroup.mk' Z)) θbar) := by
    simpa [qH, hqeq] using hquotIrr
  exact hquotRed hquotIrr'

private theorem quotientInflatedInducedCF_irreducible_of_quotient_sec9
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [H.Normal] [Z.Normal]
    (hZH : Z ≤ H)
    {θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    (hθbar : Section1.IsIrreducibleCharacterOnGroup θbar)
    (hquotIrr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF (H.map (QuotientGroup.mk' Z)) θbar)) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF H
        (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h))) := by
  classical
  let qH : H →* H.map (QuotientGroup.mk' Z) :=
    (QuotientGroup.mk' Z).subgroupMap H
  rcases hθbar with ⟨m, θρ, hθρirr, hθeq⟩
  let θrep : Representation ℂ H (Fin m → ℂ) := θρ.comp qH
  have hθrep_char :
      θrep.character = fun h : H => θbar (qH h) := by
    ext h
    simp [θrep, qH, hθeq, Representation.character]
  have hθker : Section1.subgroupInKernel' θrep.character (Z.subgroupOf H) := by
    rw [hθrep_char]
    exact quotientInflatedCharacter_subgroupInKernel_sec9 θbar
  have hqeq := quotientInducedCF_inflated_eq_inducedCF_sec9
    (H := H) (Z := Z) hZH (θbar := θbar) ⟨m, θρ, hθρirr, hθeq⟩
  have hquotIrr' : Section1.IsIrreducibleCharacterOnGroup
      (Section1.quotientInducedCF H Z (fun h : H => θbar (qH h))) := by
    simpa [qH, hqeq] using hquotIrr
  rcases hquotIrr' with ⟨n, ρq, hρqirr, hρqeq⟩
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  let ρorig : Representation ℂ L (Fin n → ℂ) := ρq.comp q
  refine ⟨n, ρorig, ?_, ?_⟩
  · exact Section6.representation_isIrreducible_comp_surjective ρq q
      (QuotientGroup.mk'_surjective Z) hρqirr
  · ext g
    calc
      Section1.inducedCF H (fun h : H => θbar (qH h)) g =
          Section1.quotientInducedCF H Z (fun h : H => θbar (qH h)) (q g) := by
            rw [← hθrep_char]
            exact (Section1.quotientInducedCF_mk H Z hZH θrep
              ((Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel θrep
                (Z.subgroupOf H)).mp hθker) g).symm
      _ = ρq.character (q g) := by
            exact congrFun hρqeq (q g)
      _ = ρorig.character g := by
            simp [ρorig, q, Representation.character]

private theorem exists_quotient_character_of_subgroupInKernel_sec9
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [Z.Normal]
    {θ : Section1.ClassFunction H}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθker : Section1.subgroupInKernel' θ (Z.subgroupOf H)) :
    ∃ θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z)),
      Section1.IsIrreducibleCharacterOnGroup θbar ∧
        θ = fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h) := by
  classical
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  have hkerRep : Section1.subgroupInRepresentationKernel ρ (Z.subgroupOf H) := by
    apply (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ
      (Z.subgroupOf H)).mp
    simpa [hθeq] using hθker
  let θbarRep : Representation ℂ (Section1.quotientImageSubgroup H Z) (Fin n → ℂ) :=
    Section1.quotientThetaRepresentation H Z ρ hkerRep
  have hθbar_irr : Representation.IsIrreducible θbarRep := by
    let qH0 : H →* H ⧸ Z.subgroupOf H := QuotientGroup.mk' (Z.subgroupOf H)
    let ρqH : Representation ℂ (H ⧸ Z.subgroupOf H) (Fin n → ℂ) :=
      Section1.quotientRepresentationOfKernelSubgroup ρ (Z.subgroupOf H) hkerRep
    have hρqH_comp : ρqH.comp qH0 = ρ := by
      apply MonoidHom.ext
      intro h
      exact Section1.quotientRepresentationOfKernelSubgroup_mk ρ
        (Z.subgroupOf H) hkerRep h
    have hρqH_irr : Representation.IsIrreducible ρqH := by
      apply Section6.representation_isIrreducible_of_comp_surjective ρqH qH0
        (QuotientGroup.mk'_surjective (Z.subgroupOf H))
      simpa [hρqH_comp] using hρirr
    let e : H ⧸ Z.subgroupOf H ≃* Section1.quotientImageSubgroup H Z :=
      quotientSubgroupRangeEquiv H Z
    have hsurj : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
    change Representation.IsIrreducible (ρqH.comp e.symm.toMonoidHom)
    exact Section6.representation_isIrreducible_comp_surjective ρqH
      e.symm.toMonoidHom hsurj hρqH_irr
  let θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z)) := by
    simpa [Section1.quotientImageSubgroup] using θbarRep.character
  have hθbar_irr' : Section1.IsIrreducibleCharacterOnGroup θbar := by
    unfold Section1.IsIrreducibleCharacterOnGroup
    exact ⟨n, θbarRep, hθbar_irr, rfl⟩
  refine ⟨θbar, hθbar_irr', ?_⟩
  ext h
  let qH : H →* H.map (QuotientGroup.mk' Z) := (QuotientGroup.mk' Z).subgroupMap H
  let hmem : ((h : L) : L ⧸ Z) ∈ Section1.quotientImageSubgroup H Z :=
    ⟨(h : L), h.2, rfl⟩
  calc
    θ h = ρ.character h := by rw [hθeq]
    _ = θbarRep.character ⟨((h : L) : L ⧸ Z), hmem⟩ := by
          exact (Section1.quotientThetaRepresentation_character_mk H Z ρ hkerRep h hmem).symm
    _ = θbar (qH h) := by rfl

private theorem theorem_9_nb_redM_pf4_nonbase_not_MF_kernel_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ)
    (h92 : hypothesis_9_2_statement M MF U W1 W2 q)
    [hKnormal : (K.subgroupOf M).Normal]
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 j : J}
    {ω : I → J → Section1.ClassFunction
      (((W1 ⊔ W2).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M)))}
    {σ : Section1.ClassFunction
      (((W1 ⊔ W2).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))) →ₗ[ℂ]
        Section1.ClassFunction (M ⧸ K.subgroupOf M)}
    {piChar : I → J → Section1.ClassFunction (M ⧸ K.subgroupOf M)}
    {xChar : J → Section1.ClassFunction
      (((ambientDerivedSubgroup M).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M)))}
    {deltaSign : J → ℂ}
    (h42q : Section4.hypothesis_4_2_statement
      (((ambientDerivedSubgroup M).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M)))
      ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      (((W1 ⊔ W2).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))))
    (hω : Section3.notation_3_3_statement
      ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      (((W1 ⊔ W2).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))) I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      (((W1 ⊔ W2).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))) I J i0 j0 ω σ piChar
      deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement
      ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      (((W1 ⊔ W2).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))) I J piChar deltaSign ω)
    (h45a : Section4Scratch.theorem_4_5_a_statement
      (((ambientDerivedSubgroup M).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))) piChar xChar)
    (hj : j ∈ Finset.univ.erase j0) :
    ¬ Section1.subgroupInKernel'
      (fun h : (ambientDerivedSubgroup M).subgroupOf M =>
        xChar j (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap
          ((ambientDerivedSubgroup M).subgroupOf M)) h))
      ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) := by
  classical
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let Nsub : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let Kbar : Subgroup (M ⧸ K.subgroupOf M) := Nsub.map qM
  let W1bar : Subgroup (M ⧸ K.subgroupOf M) := (W1.subgroupOf M).map qM
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  let Wbar : Subgroup (M ⧸ K.subgroupOf M) := ((W1 ⊔ W2).subgroupOf M).map qM
  let Hbar : Subgroup (M ⧸ K.subgroupOf M) := (MF.subgroupOf M).map qM
  have hj_ne : j ≠ j0 := (Finset.mem_erase.mp hj).1
  have h46 :
      Section4Scratch.hypothesis_4_6_statement Kbar W1bar W2bar Wbar Hbar
        ({x : M ⧸ K.subgroupOf M | x ∈ Kbar ∧ x ≠ 1}) := by
    simpa [qM, Kbar, W1bar, W2bar, Wbar, Hbar, Nsub] using
      pf4_hypothesis_4_6_mf_quotient_sec9 M MF U W1 W2 K q h92
        (inferInstance : (K.subgroupOf M).Normal) h42q
  have h47 : Section4Scratch.theorem_4_7_statement Kbar Hbar
      ({x : M ⧸ K.subgroupOf M | x ∈ Kbar ∧ x ≠ 1}) :=
    Section4Scratch.theorem_4_7 Kbar W1bar W2bar Wbar Hbar
      ({x : M ⧸ K.subgroupOf M | x ∈ Kbar ∧ x ≠ 1}) h46
  have hnonkerBar :
      ¬ Section1.subgroupInKernel' (xChar j) (Hbar.subgroupOf Kbar) := by
    have hnonbase :
        Section4Scratch.theorem_4_7_nonbase_column_statement
          Kbar Hbar ({x : M ⧸ K.subgroupOf M | x ∈ Kbar ∧ x ≠ 1})
          j0 piChar xChar := by
      exact Section4Scratch.theorem_4_7_nonbase_column
        Kbar W1bar W2bar Wbar Hbar
        ({x : M ⧸ K.subgroupOf M | x ∈ Kbar ∧ x ≠ 1})
        i0 j0 ω σ piChar xChar deltaSign h46 h45a hω h43b h43c h47
    exact (hnonbase j hj_ne).1
  have hMFD : MF.subgroupOf M ≤ Nsub := by
    intro x hx
    have hxMF : ((x : M) : G) ∈ MF := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxD : ((x : M) : G) ∈ ambientDerivedSubgroup M :=
      MF_le_ambientDerived_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92 hxMF
    simpa [Nsub, Subgroup.mem_subgroupOf] using hxD
  simpa [qM, Nsub, Kbar, Hbar] using
    quotientInflatedCharacter_not_subgroupInKernel_of_map_sec9
      (H := MF.subgroupOf M) (N := Nsub) (Z := K.subgroupOf M)
      hMFD hnonkerBar

private theorem pf4_reducible_kernelInducedFamily_member_is_nonbase_inflated_column_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF K : Subgroup G)
    [hKnormal : (K.subgroupOf M).Normal]
    (S : Finset (Section1.ClassFunction M))
    (hKD : K ≤ ambientDerivedSubgroup M)
    (hS : kernelInducedFamily M (ambientDerivedSubgroup M) MF K S)
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    {i0 : I} {j0 : J}
    {piChar : I → J → Section1.ClassFunction (M ⧸ K.subgroupOf M)}
    {xChar : J → Section1.ClassFunction
      (((ambientDerivedSubgroup M).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M)))}
    (h45a : Section4Scratch.theorem_4_5_a_statement
      (((ambientDerivedSubgroup M).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))) piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement
      (((ambientDerivedSubgroup M).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))) piChar xChar)
    (hpiBase : piChar i0 j0 =
      Section1.principalCharacter (M ⧸ K.subgroupOf M)) :
    ∀ χ : Section1.ClassFunction M,
      χ ∈ S →
        ¬ Section1.IsIrreducibleCharacterOnGroup χ →
          ∃ j : J, j ∈ Finset.univ.erase j0 ∧
            χ = Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
              (fun h : (ambientDerivedSubgroup M).subgroupOf M =>
                xChar j (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap
                  ((ambientDerivedSubgroup M).subgroupOf M)) h)) := by
  classical
  intro χ hχS hχred
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let Nsub : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let Kbar : Subgroup (M ⧸ K.subgroupOf M) := Nsub.map qM
  have hKN : K.subgroupOf M ≤ Nsub := by
    intro k hk
    change (k : G) ∈ ambientDerivedSubgroup M
    exact hKD hk
  have hNnormal : Nsub.Normal := by
    simpa [Nsub] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Nsub.Normal := hNnormal
  rcases hS with ⟨_hKNfam, _hMFNfam, hmemS⟩
  rcases (hmemS χ).mp hχS with ⟨θ, hθirr, hθnotMF, hθkerK, hχeq⟩
  rcases exists_quotient_character_of_subgroupInKernel_sec9
      (H := Nsub) (Z := K.subgroupOf M) hθirr hθkerK with
    ⟨θbar, hθbarirr, hθeq⟩
  have hθbar_mem : θbar ∈ Set.range xChar := by
    by_contra hθbar_not
    have hquotIrr :
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.inducedCF Kbar θbar) :=
      (h45b.1 θbar hθbarirr hθbar_not).1
    have horigIrr :
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.inducedCF Nsub
            (fun h : Nsub => θbar (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap
              Nsub) h))) :=
      quotientInflatedInducedCF_irreducible_of_quotient_sec9
        (H := Nsub) (Z := K.subgroupOf M) hKN hθbarirr
        (by simpa [Kbar, Nsub, qM] using hquotIrr)
    have hχirr : Section1.IsIrreducibleCharacterOnGroup χ := by
      rw [hχeq, hθeq]
      simpa [Nsub, qM] using horigIrr
    exact hχred hχirr
  rcases hθbar_mem with ⟨j, hθbar_eq⟩
  have hj_ne : j ≠ j0 := by
    intro hj
    have hxbase : xChar j0 = Section1.principalCharacter Kbar := by
      rw [← h45a.1 i0 j0, hpiBase]
      ext y
      simp [Section1.subgroupRestriction, Section1.principalCharacter]
    have hθbar_principal : θbar = Section1.principalCharacter Kbar := by
      rw [← hθbar_eq, hj, hxbase]
    have hθMFker :
        Section1.subgroupInKernel' θ
          ((MF.subgroupOf M).subgroupOf Nsub) := by
      rw [hθeq, hθbar_principal]
      intro m
      simp [Section1.degree, Section1.principalCharacter]
    exact hθnotMF hθMFker
  refine ⟨j, ?_, ?_⟩
  · simp [Finset.mem_erase, hj_ne]
  · calc
      χ = Section1.inducedCF Nsub θ := hχeq
      _ = Section1.inducedCF Nsub
          (fun h : Nsub =>
            θbar (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap Nsub) h)) := by
            rw [hθeq]
      _ = Section1.inducedCF Nsub
          (fun h : Nsub =>
            xChar j (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap Nsub) h)) := by
            rw [hθbar_eq]

private theorem theorem_9_nb_redM_pf4_column_lower_transport_to_kernelInduced_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((ambientDerivedSubgroup M).subgroupOf M).map qM
                    let W1bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W1.subgroupOf M).map qM
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    let Wbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((W1 ⊔ W2).subgroupOf M).map qM
                    Section4.hypothesis_4_2_statement Kbar W1bar W2bar Wbar →
                      Nat.card W2bar = p →
                        nbRedMPF4QuotientColumnData_sec9 Kbar W1bar W2bar Wbar p →
                          nbRedMQuotientLowerTransportData_sec9 M K W2bar p S := by
  classical
  intro h92 _hH0MF _hpprime _hpData hKnormal hKD _hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  dsimp
  intro h42q _hW2bar_card hpf4
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let Nsub : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let Kbar : Subgroup (M ⧸ K.subgroupOf M) := Nsub.map qM
  let W1bar : Subgroup (M ⧸ K.subgroupOf M) := (W1.subgroupOf M).map qM
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  let Wbar : Subgroup (M ⧸ K.subgroupOf M) := ((W1 ⊔ W2).subgroupOf M).map qM
  rcases hpf4 with
    ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
      i0, j0, ω, hω, σ, piChar, deltaSign, xChar, h43b, h43c, h45a,
      _h45b, _hdeltaBase, _hpiBase, hpiColumnInj, hnonbaseCard⟩
  letI : Fintype I := instFintypeI
  letI : Fintype J := instFintypeJ
  letI : DecidableEq I := instDecidableEqI
  letI : DecidableEq J := instDecidableEqJ
  let ι : Type u := {j : J // j ∈ Finset.univ.erase j0}
  letI : Fintype ι := inferInstance
  letI : DecidableEq ι := inferInstance
  let θ : ι → Section1.ClassFunction Nsub := fun j h =>
    xChar j.1 (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap Nsub) h)
  let μ : ι → Section1.ClassFunction M := fun j =>
    Section1.inducedCF Nsub (θ j)
  have hKN : K.subgroupOf M ≤ Nsub := by
    intro k hk
    change (k : G) ∈ ambientDerivedSubgroup M
    exact hKD hk
  have hNnormal : Nsub.Normal := by
    simpa [Nsub] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Nsub.Normal := hNnormal
  have h46 :
      Section4Scratch.hypothesis_4_6_statement
        Kbar W1bar W2bar Wbar Kbar
        ({x : M ⧸ K.subgroupOf M | x ∈ Kbar ∧ x ≠ 1}) := by
    exact pf4_hypothesis_4_6_self_of_hypothesis_4_2_sec9 h42q
  have hθirr : ∀ j : ι, Section1.IsIrreducibleCharacterOnGroup (θ j) := by
    intro j
    simpa [θ, Nsub, Kbar, qM] using
      quotientInflatedCharacter_irreducible_sec9
        (H := Nsub) (Z := K.subgroupOf M) (θbar := xChar j.1) (h45a.2.1 j.1)
  have hθker : ∀ j : ι,
      Section1.subgroupInKernel' (θ j) ((K.subgroupOf M).subgroupOf Nsub) := by
    intro j
    simpa [θ, Nsub, Kbar, qM] using
      quotientInflatedCharacter_subgroupInKernel_sec9
        (H := Nsub) (Z := K.subgroupOf M) (xChar j.1)
  have hθnonker : ∀ j : ι,
      ¬ Section1.subgroupInKernel' (θ j)
        ((MF.subgroupOf M).subgroupOf Nsub) := by
    intro j
    simpa [θ, Nsub, Kbar, qM] using
      theorem_9_nb_redM_pf4_nonbase_not_MF_kernel_source_core_sec9
        (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) (K := K)
        (q := q) h92 (i0 := i0) (j0 := j0) (j := j.1) (ω := ω) (σ := σ)
        (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
        h42q hω h43b h43c h45a j.2
  have hquotRed : ∀ j : ι,
      ¬ Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF Kbar (xChar j.1)) := by
    intro j hjirr
    have hpiRed :
        ¬ Section1.IsIrreducibleCharacterOnGroup
          (Section4Scratch.piColumn piChar j.1) :=
      Section5.piColumn_not_irreducible_pf53 h46 hω h43b j.1
    exact hpiRed (by simpa [← h45a.2.2 j.1] using hjirr)
  have hμred : ∀ j : ι, ¬ Section1.IsIrreducibleCharacterOnGroup (μ j) := by
    intro j
    simpa [μ, θ, Nsub, Kbar, qM] using
      quotientInflatedInducedCF_not_irreducible_of_quotient_sec9
        (H := Nsub) (Z := K.subgroupOf M) hKN (h45a.2.1 j.1) (hquotRed j)
  rcases hS with ⟨_hKNfam, _hMFNfam, hmemS⟩
  have hμmem : ∀ j : ι, μ j ∈ S := by
    intro j
    rw [hmemS (μ j)]
    exact ⟨θ j, hθirr j, hθnonker j, hθker j, rfl⟩
  refine ⟨ι, inferInstance, inferInstance, μ, ?_, ?_, ?_⟩
  · intro j k hjk
    have hqeq :
        Section1.quotientInducedCF Nsub (K.subgroupOf M) (θ j) =
          Section1.quotientInducedCF Nsub (K.subgroupOf M) (θ k) :=
      quotientInducedCF_eq_of_inducedCF_eq_sec9
        (H := Nsub) (Z := K.subgroupOf M) (θ := θ j) (η := θ k) (by
          simpa [μ] using hjk)
    have hjeq :
        Section1.inducedCF Kbar (xChar j.1) =
          Section1.inducedCF Kbar (xChar k.1) := by
      have hjq := quotientInducedCF_inflated_eq_inducedCF_sec9
        (H := Nsub) (Z := K.subgroupOf M) hKN (θbar := xChar j.1) (h45a.2.1 j.1)
      have hkq := quotientInducedCF_inflated_eq_inducedCF_sec9
        (H := Nsub) (Z := K.subgroupOf M) hKN (θbar := xChar k.1) (h45a.2.1 k.1)
      simpa [θ, Nsub, Kbar, qM, hjq, hkq] using hqeq
    have hcolumn :
        Section4Scratch.piColumn piChar j.1 =
          Section4Scratch.piColumn piChar k.1 := by
      calc
        Section4Scratch.piColumn piChar j.1 =
            Section1.inducedCF Kbar (xChar j.1) := (h45a.2.2 j.1).symm
        _ = Section1.inducedCF Kbar (xChar k.1) := hjeq
        _ = Section4Scratch.piColumn piChar k.1 := h45a.2.2 k.1
    exact Subtype.ext (hpiColumnInj hcolumn)
  · simpa [ι] using hnonbaseCard
  · intro j
    exact ⟨hμmem j, hμred j⟩

private theorem theorem_9_nb_redM_pf4_column_reducible_filter_card_le_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((ambientDerivedSubgroup M).subgroupOf M).map qM
                    let W1bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W1.subgroupOf M).map qM
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    let Wbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((W1 ⊔ W2).subgroupOf M).map qM
                    Section4.hypothesis_4_2_statement Kbar W1bar W2bar Wbar →
                      Nat.card W2bar = p →
                        nbRedMPF4QuotientColumnData_sec9 Kbar W1bar W2bar Wbar p →
                          (reducibleCharacterFilter_sec9 M S).card ≤ p - 1 := by
  classical
  intro _h92 _hH0MF _hpprime _hpData hKnormal hKD _hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  dsimp
  intro _h42q _hW2bar_card hpf4
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let Nsub : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let Kbar : Subgroup (M ⧸ K.subgroupOf M) := Nsub.map qM
  rcases hpf4 with
    ⟨I, J, instFintypeI, instFintypeJ, _instDecidableEqI, instDecidableEqJ,
      i0, j0, _ω, _hω, _σ, piChar, _deltaSign, xChar, _h43b, _h43c, h45a,
      h45b, _hdeltaBase, hpiBase, _hpiColumnInj, hnonbaseCard⟩
  letI : Fintype I := instFintypeI
  letI : Fintype J := instFintypeJ
  letI : DecidableEq J := instDecidableEqJ
  let Red : Finset (Section1.ClassFunction M) := reducibleCharacterFilter_sec9 M S
  let ρ : Type u := {χ : Section1.ClassFunction M // χ ∈ Red}
  letI : Fintype ρ := Finset.Subtype.fintype Red
  let ι : Type u := {j : J // j ∈ Finset.univ.erase j0}
  letI : Fintype ι := Finset.Subtype.fintype (Finset.univ.erase j0)
  have hclass :
      ∀ χ : ρ, ∃ j : ι,
        (χ : Section1.ClassFunction M) =
          Section1.inducedCF Nsub
            (fun h : Nsub =>
              xChar j.1 (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap
                Nsub) h)) := by
    intro χ
    have hχpair :
        (χ : Section1.ClassFunction M) ∈ S ∧
          ¬ Section1.IsIrreducibleCharacterOnGroup (χ : Section1.ClassFunction M) := by
      have hχRed : (χ : Section1.ClassFunction M) ∈ Red := χ.2
      have hχfilter :
          (χ : Section1.ClassFunction M) ∈ reducibleCharacterFilter_sec9 M S := by
        simp [Red] at hχRed ⊢
      exact Finset.mem_filter.mp hχfilter
    rcases pf4_reducible_kernelInducedFamily_member_is_nonbase_inflated_column_sec9
        M MF K S hKD hS
        (i0 := i0) (j0 := j0) (piChar := piChar) (xChar := xChar)
        h45a h45b hpiBase χ hχpair.1 hχpair.2 with
      ⟨j, hj, hχeq⟩
    exact ⟨⟨j, hj⟩, by simpa [Nsub, qM, Kbar] using hχeq⟩
  let f : ρ → ι := fun χ => Classical.choose (hclass χ)
  have hf : Function.Injective f := by
    intro χ ψ hχψ
    apply Subtype.ext
    have hχspec := Classical.choose_spec (hclass χ)
    have hψspec := Classical.choose_spec (hclass ψ)
    calc
      (χ : Section1.ClassFunction M) =
          Section1.inducedCF Nsub
            (fun h : Nsub =>
              xChar (f χ).1 (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap
                Nsub) h)) := hχspec
      _ = Section1.inducedCF Nsub
            (fun h : Nsub =>
              xChar (f ψ).1 (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap
                Nsub) h)) := by rw [hχψ]
      _ = (ψ : Section1.ClassFunction M) := hψspec.symm
  have hcardRedSubtype : Fintype.card ρ = Red.card :=
    Fintype.card_of_subtype Red (fun _ => Iff.rfl)
  have hcardNonbaseSubtype : Fintype.card ι = (Finset.univ.erase j0).card :=
    Fintype.card_of_subtype (Finset.univ.erase j0) (fun _ => Iff.rfl)
  calc
    (reducibleCharacterFilter_sec9 M S).card = Fintype.card ρ := by
      simpa [Red] using hcardRedSubtype.symm
    _ ≤ Fintype.card ι := Fintype.card_le_of_injective f hf
    _ = p - 1 := by
      rw [hcardNonbaseSubtype, hnonbaseCard]

private theorem theorem_9_nb_redM_pf4_column_reducible_subset_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((ambientDerivedSubgroup M).subgroupOf M).map qM
                    let W1bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W1.subgroupOf M).map qM
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    let Wbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((W1 ⊔ W2).subgroupOf M).map qM
                    Section4.hypothesis_4_2_statement Kbar W1bar W2bar Wbar →
                      Nat.card W2bar = p →
                        nbRedMPF4QuotientColumnData_sec9 Kbar W1bar W2bar Wbar p →
                          ∀ R : Finset (Section1.ClassFunction M),
                            R.card = p - 1 →
                              (∀ χ : Section1.ClassFunction M,
                                χ ∈ R →
                                  χ ∈ S ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ) →
                                ∀ χ : Section1.ClassFunction M,
                                  χ ∈ S →
                                    ¬ Section1.IsIrreducibleCharacterOnGroup χ →
                                      χ ∈ R := by
  classical
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  dsimp
  intro h42q hW2bar_card hpf4 R hRcard hRmem χ hχS hχred
  let Red : Finset (Section1.ClassFunction M) := reducibleCharacterFilter_sec9 M S
  have hRsubRed : R ⊆ Red := by
    intro ψ hψR
    have hψ := hRmem ψ hψR
    simpa [Red, reducibleCharacterFilter_sec9] using hψ
  have hRedCardLe : Red.card ≤ p - 1 := by
    simpa [Red] using
      theorem_9_nb_redM_pf4_column_reducible_filter_card_le_sec9
        M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD hKinf
        hS h42q hW2bar_card hpf4
  have hRedCardLeR : Red.card ≤ R.card := by
    simpa [hRcard] using hRedCardLe
  have hR_eq_Red : R = Red :=
    Finset.eq_of_subset_of_card_le hRsubRed hRedCardLeR
  have hχRed : χ ∈ Red := by
    simp [Red, reducibleCharacterFilter_sec9, hχS, hχred]
  simpa [hR_eq_Red] using hχRed

private theorem theorem_9_nb_redM_pf4_column_exhaust_transport_to_kernelInduced_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((ambientDerivedSubgroup M).subgroupOf M).map qM
                    let W1bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W1.subgroupOf M).map qM
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    let Wbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((W1 ⊔ W2).subgroupOf M).map qM
                    Section4.hypothesis_4_2_statement Kbar W1bar W2bar Wbar →
                      Nat.card W2bar = p →
                        nbRedMPF4QuotientColumnData_sec9 Kbar W1bar W2bar Wbar p →
                          nbRedMQuotientLowerTransportData_sec9 M K W2bar p S →
                            nbRedMQuotientTransportData_sec9 M K W2bar p S := by
  classical
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  dsimp
  intro h42q hW2bar_card hpf4 hlower
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
    ((ambientDerivedSubgroup M).subgroupOf M).map qM
  let W1bar : Subgroup (M ⧸ K.subgroupOf M) := (W1.subgroupOf M).map qM
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  let Wbar : Subgroup (M ⧸ K.subgroupOf M) := ((W1 ⊔ W2).subgroupOf M).map qM
  rcases hlower with ⟨ι, instFintype, instDecidableEq, μ, hμinj, hcard, hmem⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  let R : Finset (Section1.ClassFunction M) := Finset.univ.image μ
  have hRcard : R.card = p - 1 := by
    calc
      R.card = Fintype.card ι := by
        simpa [R] using
          (Finset.card_image_of_injective (Finset.univ : Finset ι) hμinj)
      _ = p - 1 := hcard
  have hRmem :
      ∀ χ : Section1.ClassFunction M,
        χ ∈ R →
          χ ∈ S ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
    intro χ hχ
    rcases Finset.mem_image.mp hχ with ⟨i, _hi, hχeq⟩
    simpa [hχeq.symm] using hmem i
  have hupper :
      ∀ χ : Section1.ClassFunction M,
        χ ∈ S →
          ¬ Section1.IsIrreducibleCharacterOnGroup χ →
            χ ∈ R :=
    theorem_9_nb_redM_pf4_column_reducible_subset_source_core_sec9
      M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD hKinf
      hS h42q hW2bar_card hpf4 R hRcard hRmem
  refine ⟨ι, instFintype, instDecidableEq, μ, hμinj, hcard, hmem, ?_⟩
  intro χ hχS hχred
  have hχR : χ ∈ R := hupper χ hχS hχred
  rcases Finset.mem_image.mp hχR with ⟨i, _hi, hχeq⟩
  exact ⟨i, hχeq⟩

private theorem theorem_9_nb_redM_pf4_column_transport_to_kernelInduced_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((ambientDerivedSubgroup M).subgroupOf M).map qM
                    let W1bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W1.subgroupOf M).map qM
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    let Wbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((W1 ⊔ W2).subgroupOf M).map qM
                    Section4.hypothesis_4_2_statement Kbar W1bar W2bar Wbar →
                      Nat.card W2bar = p →
                        nbRedMPF4QuotientColumnData_sec9 Kbar W1bar W2bar Wbar p →
                          nbRedMQuotientTransportData_sec9 M K W2bar p S := by
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  dsimp
  intro h42q hW2bar_card hpf4
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
    ((ambientDerivedSubgroup M).subgroupOf M).map qM
  let W1bar : Subgroup (M ⧸ K.subgroupOf M) := (W1.subgroupOf M).map qM
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  let Wbar : Subgroup (M ⧸ K.subgroupOf M) := ((W1 ⊔ W2).subgroupOf M).map qM
  have hlower : nbRedMQuotientLowerTransportData_sec9 M K W2bar p S :=
    theorem_9_nb_redM_pf4_column_lower_transport_to_kernelInduced_source_core_sec9
      M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD hKinf
      hS h42q hW2bar_card hpf4
  exact
    theorem_9_nb_redM_pf4_column_exhaust_transport_to_kernelInduced_source_core_sec9
      M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD hKinf
      hS h42q hW2bar_card hpf4 hlower

private theorem theorem_9_nb_redM_pf4_quotient_character_transport_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    Section4.hypothesis_4_2_statement
                      (((ambientDerivedSubgroup M).subgroupOf M).map
                        (QuotientGroup.mk' (K.subgroupOf M)))
                      ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
                      ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
                      (((W1 ⊔ W2).subgroupOf M).map
                        (QuotientGroup.mk' (K.subgroupOf M))) →
                      Nat.card
                        ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) = p →
                        nbRedMQuotientTransportData_sec9 M K
                          ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
                          p S := by
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS h42q hW2bar_card
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
    ((ambientDerivedSubgroup M).subgroupOf M).map qM
  let W1bar : Subgroup (M ⧸ K.subgroupOf M) := (W1.subgroupOf M).map qM
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  let Wbar : Subgroup (M ⧸ K.subgroupOf M) := ((W1 ⊔ W2).subgroupOf M).map qM
  have hpf4 : nbRedMPF4QuotientColumnData_sec9 Kbar W1bar W2bar Wbar p :=
    theorem_9_nb_redM_pf4_quotient_column_data_of_notation_sec9
      Kbar W1bar W2bar Wbar p h42q (by simpa [W2bar, qM] using hW2bar_card)
      (theorem_9_nb_redM_quotient_notation_3_3_source_core_sec9
        Kbar W1bar W2bar Wbar h42q)
  exact
    theorem_9_nb_redM_pf4_column_transport_to_kernelInduced_source_core_sec9
      M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD hKinf
      hS h42q (by simpa [W2bar, qM] using hW2bar_card) hpf4

private theorem theorem_9_nb_redM_primeTI_quotient_character_transport_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    IsCyclic W2bar →
                      Nat.card W2bar ≠ 1 →
                      nbRedMQuotientTransportData_sec9 M K W2bar p S := by
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  change
    IsCyclic ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) →
      Nat.card ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) ≠ 1 →
        nbRedMQuotientTransportData_sec9 M K
          ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) p S
  intro _hW2bar_cyclic _hW2bar_ne_one
  have h42q :
      Section4.hypothesis_4_2_statement
        (((ambientDerivedSubgroup M).subgroupOf M).map
          (QuotientGroup.mk' (K.subgroupOf M)))
        ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
        ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
        (((W1 ⊔ W2).subgroupOf M).map
          (QuotientGroup.mk' (K.subgroupOf M))) :=
    theorem_9_nb_redM_M_mod_K_hypothesis_4_2_sec9
      M MF U W1 W2 H0 K p q h92 hH0MF hpprime hpData hKnormal hKD hKinf
  have hW2bar_card :
      Nat.card ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) = p :=
    theorem_9_nb_redM_W2_map_mk_K_card_eq_source_core_sec9
      M MF U W1 W2 H0 K p q h92 hH0MF hpprime hpData hKnormal hKD hKinf
  exact
    theorem_9_nb_redM_pf4_quotient_character_transport_source_core_sec9
      M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD
      hKinf hS h42q hW2bar_card

private theorem theorem_9_nb_redM_quotient_character_transport_of_W2_card_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    Nat.card W2bar = p →
                      nbRedMQuotientTransportData_sec9 M K W2bar p S := by
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  change
    Nat.card ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) = p →
      nbRedMQuotientTransportData_sec9 M K
        ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) p S
  intro hW2bar_card
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  have hW2bar_cyclic : IsCyclic W2bar := by
    simpa [W2bar, qM] using
      theorem_9_nb_redM_W2_map_mk_K_isCyclic_source_core_sec9
        M MF U W1 W2 H0 K q h92 hKnormal
  have hW2bar_ne_one : Nat.card W2bar ≠ 1 :=
    natCard_ne_one_of_eq_prime_sec9 (α := W2bar) hpprime hW2bar_card
  exact
    theorem_9_nb_redM_primeTI_quotient_character_transport_source_core_sec9
      M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD
      hKinf hS hW2bar_cyclic hW2bar_ne_one

private theorem theorem_9_nb_redM_quotient_transport_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    nbRedMQuotientTransportData_sec9 M K W2bar p S := by
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  have hW2bar_card : Nat.card W2bar = p := by
    simpa [W2bar, qM] using
      theorem_9_nb_redM_W2_map_mk_K_card_eq_source_core_sec9
        M MF U W1 W2 H0 K p q h92 hH0MF hpprime hpData hKnormal hKD hKinf
  exact
    theorem_9_nb_redM_quotient_character_transport_of_W2_card_source_core_sec9
      M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD
      hKinf hS hW2bar_card

private theorem theorem_9_nb_redM_count_of_normal_le_inter_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (K.subgroupOf M).Normal →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    (reducibleCharacterFilter_sec9 M S).card = p - 1 := by
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  have htransport : nbRedMQuotientTransportData_sec9 M K W2bar p S :=
    theorem_9_nb_redM_quotient_transport_source_core_sec9 M MF U W1 W2 H0 K
      p q S h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  exact theorem_9_reducible_filter_card_of_transport_data_sec9
    (quotientReducibleFamilyTransportData_of_nbRedMQuotientTransportData_sec9
      (M := M) (K := K) (Wbar := W2bar) (p := p) (S := S) htransport)

private theorem theorem_9_H0C_le_ambientDerived_of_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        quotientCentralizerIn MF H0 U C →
          H0 ⊔ C ≤ ambientDerivedSubgroup M := by
  intro h92 hH0MF hC
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
      _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hH0D : H0 ≤ ambientDerivedSubgroup M :=
    hH0MF.trans (MF_le_ambientDerived_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92)
  have hCD : C ≤ ambientDerivedSubgroup M := hC.1.trans hUleD
  exact sup_le hH0D hCD

private theorem theorem_9_H0C_normal_M_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        quotientCentralizerIn MF H0 U C →
          Nat.Prime p →
            (∃ hp : Nat.Primes,
              hp.val = p ∧
                hoReductionData M MF U W2 H0 hp ∧
                  quotientChiefFactorData_9_6 M MF H0 W1 hp) →
              ((H0 ⊔ C).subgroupOf M).Normal := by
  intro h92 hH0MF hC _hpprime hpData
  rcases hpData with ⟨_hp, _hp_eq, hpDataCore, _h96⟩
  rcases hpDataCore with
    ⟨_hH0MF, hMF_le_M, hH0_normal_M, _hH0_normal_MF, _hH0lt,
      _helem, _htypeIIIIV⟩
  rcases h92.mf.1 with ⟨hMFleM92, hMFnormalM, _hMFnil, _hMFhall⟩
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, hcompMW1, hUleD,
      _hUnil, hW1normUInM, hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
      _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  let D : Subgroup G := ambientDerivedSubgroup M
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le (E := M)
  have hH0_le_M : H0 ≤ M := hH0MF.trans hMF_le_M
  have hC_le_M : C ≤ M := hC.1.trans (hUleD.trans hDleM)
  have hH0C_le_M : H0 ⊔ C ≤ M := sup_le hH0_le_M hC_le_M
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hH0C_le_M).2 ?_
  have hM_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_M).1 hH0_normal_M
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM92).1 hMFnormalM
  have hD_norm_MF : D ≤ Subgroup.normalizer (MF : Set G) :=
    hDleM.trans hM_norm_MF
  have hU_le_M : U ≤ M := hUleD.trans hDleM
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    hUleD.trans hD_norm_MF
  have hU_norm_C : U ≤ Subgroup.normalizer (C : Set G) :=
    quotientCentralizerIn_le_normalizer_of_le_normalizers_sec9
      (M := M) (MF := MF) (U := U) (H0 := H0) (N := U)
      hU_le_M Subgroup.le_normalizer hU_norm_MF hH0_le_M hH0_normal_M hC
  have hU_norm_H0C : U ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer_sec9 H0 C U
      (hU_le_M.trans hM_norm_H0) hU_norm_C
  have hMF_norm_H0C :
      MF ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) := by
    apply le_normalizer_sup_of_le_normalizer_left_commutator_right_sec9
    · exact hMF_le_M.trans hM_norm_H0
    · intro n hnMF b hbC
      exact (hC.2 b (hC.1 hbC)).mp hbC n hnMF
  have hMFU_norm_H0C :
      MF ⊔ U ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) :=
    sup_le hMF_norm_H0C hU_norm_H0C
  have hD_norm_H0C :
      D ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) := by
    have hD_eq : D = MF ⊔ U := by
      dsimp [D]
      exact hcompDU.2.2.1
    simpa [hD_eq] using hMFU_norm_H0C
  have hW1_le_M : W1 ≤ M := hW1hall.1
  have hW1_norm_U : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro w hw
    exact (mem_subgroupNormalizerIn.mp (hW1normUInM hw)).1
  have hW1_norm_C : W1 ≤ Subgroup.normalizer (C : Set G) :=
    quotientCentralizerIn_le_normalizer_of_le_normalizers_sec9
      (M := M) (MF := MF) (U := U) (H0 := H0) (N := W1)
      hW1_le_M hW1_norm_U (hW1_le_M.trans hM_norm_MF)
      hH0_le_M hH0_normal_M hC
  have hW1_norm_H0C :
      W1 ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer_sec9 H0 C W1
      (hW1_le_M.trans hM_norm_H0) hW1_norm_C
  have hDW1_norm_H0C :
      D ⊔ W1 ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) :=
    sup_le hD_norm_H0C hW1_norm_H0C
  have hM_eq : M = D ⊔ W1 := by
    dsimp [D]
    exact hcompMW1.2.2.1
  simpa [hM_eq] using hDW1_norm_H0C

public theorem theorem_9_H0C_inf_MF_eq_H0_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        quotientCentralizerIn MF H0 U C →
          Nat.Prime p →
            (∃ hp : Nat.Primes,
              hp.val = p ∧
                hoReductionData M MF U W2 H0 hp ∧
                  quotientChiefFactorData_9_6 M MF H0 W1 hp) →
              (H0 ⊔ C) ⊓ MF = H0 := by
  intro h92 hH0MF hC _hpprime hpData
  rcases hpData with ⟨_hp, _hp_eq, hpDataCore, _h96⟩
  rcases hpDataCore with
    ⟨_hH0MF, hMFM, hH0normalM, _hH0normalMF, _hH0ltMF, _helem,
      _htypeIIIIV⟩
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
      _hUnil, _hW1normU, hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
      _hFitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hH0M : H0 ≤ M := hH0MF.trans hMFM
  have hCM : C ≤ M :=
    hC.1.trans (hUleD.trans section12_ambientDerivedSubgroup_le)
  have hMFUdisj : Disjoint MF U := hcompDU.2.2.2
  apply le_antisymm
  · intro x hx
    let xM : M := ⟨x, hMFM hx.2⟩
    have hsubsup :
        (H0 ⊔ C).subgroupOf M = H0.subgroupOf M ⊔ C.subgroupOf M :=
      Subgroup.subgroupOf_sup hH0M hCM
    have hxSub : xM ∈ H0.subgroupOf M ⊔ C.subgroupOf M := by
      rw [← hsubsup]
      simpa [xM, Subgroup.mem_subgroupOf] using hx.1
    letI : (H0.subgroupOf M).Normal := hH0normalM
    rcases (Subgroup.mem_sup_of_normal_left
        (s := H0.subgroupOf M) (t := C.subgroupOf M) (x := xM)).1 hxSub with
      ⟨hM, hhH0M, cM, hcCM, hhcM⟩
    let h : G := hM
    let c : G := cM
    have hhH0 : h ∈ H0 := by
      simpa [h, Subgroup.mem_subgroupOf] using hhH0M
    have hcC : c ∈ C := by
      simpa [c, Subgroup.mem_subgroupOf] using hcCM
    have hhc : h * c = x := by
      simpa [h, c, xM] using congrArg Subtype.val hhcM
    have hx_eq : x = h * c := hhc.symm
    have hhMF : h ∈ MF := hH0MF hhH0
    have hcMF : c ∈ MF := by
      have hcalc : c = h⁻¹ * x := by
        rw [hx_eq]
        group
      rw [hcalc]
      exact MF.mul_mem (MF.inv_mem hhMF) hx.2
    have hcU : c ∈ U := hC.1 hcC
    have hcBot : c ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hMFUdisj) hcMF hcU
    have hc1 : c = 1 := by
      simpa using hcBot
    have hxH0 : x ∈ H0 := by
      rw [hx_eq, hc1, mul_one]
      exact hhH0
    exact hxH0
  · intro x hxH0
    exact ⟨Subgroup.mem_sup_left hxH0, hH0MF hxH0⟩

private theorem theorem_9_nb_redM_pair_count_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q : ℕ)
    (SH0 SH0C : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        quotientCentralizerIn MF H0 U C →
          Nat.Prime p →
            (∃ hp : Nat.Primes,
              hp.val = p ∧
                hoReductionData M MF U W2 H0 hp ∧
                  quotientChiefFactorData_9_6 M MF H0 W1 hp) →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
                kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
                  (reducibleCharacterFilter_sec9 M SH0).card = p - 1 ∧
                    (reducibleCharacterFilter_sec9 M SH0C).card = p - 1 := by
  intro h92 hH0MF hC hpprime hpData hSH0 hSH0C
  have hH0normalM : (H0.subgroupOf M).Normal := by
    rcases hpData with ⟨_hp, _hp_eq, hpDataCore, _h96⟩
    rcases hpDataCore with
      ⟨_hH0MF, _hMFM, hH0normalM, _hH0normalMF, _hH0ltMF,
        _helem, _htypeIIIIV⟩
    exact hH0normalM
  have hH0D : H0 ≤ ambientDerivedSubgroup M :=
    hH0MF.trans (MF_le_ambientDerived_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92)
  have hH0infMF : H0 ⊓ MF = H0 := inf_eq_left.mpr hH0MF
  have hSH0card :
      (reducibleCharacterFilter_sec9 M SH0).card = p - 1 :=
    theorem_9_nb_redM_count_of_normal_le_inter_source_core_sec9
      M MF U W1 W2 H0 H0 p q SH0 h92 hH0MF hpprime hpData
      hH0normalM hH0D hH0infMF hSH0
  have hH0CnormalM : ((H0 ⊔ C).subgroupOf M).Normal :=
    theorem_9_H0C_normal_M_source_core_sec9 M MF U W1 W2 H0 C p q
      h92 hH0MF hC hpprime hpData
  have hH0CD : H0 ⊔ C ≤ ambientDerivedSubgroup M :=
    theorem_9_H0C_le_ambientDerived_of_source_sec9 M MF U W1 W2 H0 C q
      h92 hH0MF hC
  have hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0 :=
    theorem_9_H0C_inf_MF_eq_H0_source_core_sec9 M MF U W1 W2 H0 C p q
      h92 hH0MF hC hpprime hpData
  have hSH0Ccard :
      (reducibleCharacterFilter_sec9 M SH0C).card = p - 1 :=
    theorem_9_nb_redM_count_of_normal_le_inter_source_core_sec9
      M MF U W1 W2 H0 (H0 ⊔ C) p q SH0C h92 hH0MF hpprime hpData
      hH0CnormalM hH0CD hH0CinfMF hSH0C
  exact ⟨hSH0card, hSH0Ccard⟩


public theorem theorem_9_reducible_filter_count_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q : ℕ)
    (SH0 SH0C : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        quotientCentralizerIn MF H0 U C →
          Nat.Prime p →
            (∃ hp : Nat.Primes,
              hp.val = p ∧
                hoReductionData M MF U W2 H0 hp ∧
                  quotientChiefFactorData_9_6 M MF H0 W1 hp) →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
                kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
                  ∃ R0 RC : Finset (Section1.ClassFunction M),
                    R0.card = p - 1 ∧
                      RC.card = p - 1 ∧
                      (∀ χ : Section1.ClassFunction M,
                        χ ∈ R0 ↔
                          χ ∈ SH0 ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ) ∧
                    ∀ χ : Section1.ClassFunction M,
                      χ ∈ RC ↔
                        χ ∈ SH0C ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
  classical
  intro h92 hH0MF hC hpprime hpData hSH0 hSH0C
  let R0 : Finset (Section1.ClassFunction M) :=
    reducibleCharacterFilter_sec9 M SH0
  let RC : Finset (Section1.ClassFunction M) :=
    reducibleCharacterFilter_sec9 M SH0C
  rcases theorem_9_nb_redM_pair_count_source_core_sec9
      M MF U W1 W2 H0 C p q SH0 SH0C h92 hH0MF hC hpprime hpData hSH0 hSH0C with
    ⟨hR0card, hRCcard⟩
  refine ⟨R0, RC, ?_, ?_, ?_, ?_⟩
  · simpa [R0] using hR0card
  · simpa [RC] using hRCcard
  · intro χ
    simp [R0, reducibleCharacterFilter_sec9]
  · intro χ
    simp [RC, reducibleCharacterFilter_sec9]

private theorem classFunction_eq_of_irreducible_scalarProduct_ne_zero_sec9
    {L : Type u} [Group L] [Finite L]
    {φ ψ : Section1.ClassFunction L}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hinner : Section1.scalarProduct L φ ψ ≠ 0) :
    φ = ψ := by
  by_contra hne
  have hzero :
      Section1.scalarProduct L φ ψ = 0 :=
    Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne hφ hψ hne
  exact hinner hzero

private theorem inducedCF_eq_of_irreducible_constituent_sec9
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {χ : Section1.ClassFunction L} {ψ : Section1.ClassFunction K}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hIndψ : Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF K ψ))
    (hinner :
      Section1.scalarProduct K ψ (Section1.subgroupRestriction K χ) ≠ 0) :
    χ = Section1.inducedCF K ψ := by
  have hχclass : Section1.IsClassFunction χ := by
    rcases hχ with ⟨_n, ρ, _hρirr, hχeq⟩
    intro x g
    rw [hχeq]
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  have hinnerInd :
      Section1.scalarProduct L (Section1.inducedCF K ψ) χ ≠ 0 := by
    rw [Section1.scalarProduct_inducedCF_left K ψ χ hχclass]
    exact hinner
  exact (classFunction_eq_of_irreducible_scalarProduct_ne_zero_sec9
    hIndψ hχ hinnerInd).symm

private theorem subgroupInKernel'_constituent_of_subgroupRestriction_kernel_sec9
    {L : Type u} [Group L] [Finite L]
    (K A : Subgroup L)
    {χ : Section1.ClassFunction L} {θ : Section1.ClassFunction K}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχker : Section1.subgroupInKernel' χ A)
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hinner :
      Section1.scalarProduct K θ (Section1.subgroupRestriction K χ) ≠ 0) :
    Section1.subgroupInKernel' θ (A.subgroupOf K) := by
  classical
  rcases hχirr with ⟨nχ, ρχ, _hρχirr, hχeq⟩
  rcases hθirr with ⟨nθ, ρθ, hρθirr, hθeq⟩
  let ρχK : Representation ℂ K (Fin nχ → ℂ) := ρχ.comp K.subtype
  have hres :
      Section1.subgroupRestriction K χ = ρχK.character := by
    ext k
    simp [ρχK, Section1.subgroupRestriction, hχeq, Representation.character]
  have hχkerChar : Section1.subgroupInKernel' ρχ.character A := by
    simpa [hχeq] using hχker
  have hχkerRep : Section1.subgroupInRepresentationKernel ρχ A :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      ρχ A).mp hχkerChar
  have hχKkerRep :
      Section1.subgroupInRepresentationKernel ρχK (A.subgroupOf K) := by
    intro a
    change ρχ ((a : K) : L) = 1
    exact hχkerRep ⟨((a : K) : L), by
      exact a.property⟩
  have hinnerSwap :
      Section1.scalarProduct K (Section1.subgroupRestriction K χ) θ ≠ 0 :=
    (Section1.scalarProduct_ne_zero_swap θ
      (Section1.subgroupRestriction K χ)).1 hinner
  have hinnerRep :
      Section1.scalarProduct K ρχK.character ρθ.character ≠ 0 := by
    simpa [hθeq, hres] using hinnerSwap
  have hfinrank_ne :
      (Module.finrank ℂ (Representation.IntertwiningMap ρθ ρχK) : ℂ) ≠ 0 := by
    simpa [Section1.scalarProduct_representation_char_eq_finrank ρθ ρχK]
      using hinnerRep
  have hfinrank_nat_ne :
      Module.finrank ℂ (Representation.IntertwiningMap ρθ ρχK) ≠ 0 := by
    intro hzero
    apply hfinrank_ne
    simp [hzero]
  have hfinrank_pos :
      0 < Module.finrank ℂ (Representation.IntertwiningMap ρθ ρχK) :=
    Nat.pos_of_ne_zero hfinrank_nat_ne
  rw [Module.finrank_pos_iff_exists_ne_zero] at hfinrank_pos
  rcases hfinrank_pos with ⟨f, hf⟩
  have hθkerRep :
      Section1.subgroupInRepresentationKernel ρθ (A.subgroupOf K) := by
    letI : Representation.IsIrreducible ρθ := hρθirr
    have hf_inj : Function.Injective f := by
      rcases (Representation.IsIrreducible.injective_or_eq_zero
          (ρ := ρθ) (σ := ρχK) f) with hinj | hzero
      · exact hinj
      · exact (hf hzero).elim
    intro a
    apply LinearMap.ext
    intro v
    apply hf_inj
    calc
      f (ρθ (a : K) v) = ρχK (a : K) (f v) := by
        exact Representation.IntertwiningMap.isIntertwining ρθ ρχK f (a : K) v
      _ = f v := by
        rw [hχKkerRep a]
        simp
  have hθkerChar : Section1.subgroupInKernel' ρθ.character (A.subgroupOf K) :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      ρθ (A.subgroupOf K)).mpr hθkerRep
  simpa [hθeq] using hθkerChar

private theorem constituent_not_subgroupInKernel'_of_subgroupRestriction_not_kernel_sec9
    {L : Type u} [Group L] [Finite L]
    (K A : Subgroup L) [K.Normal] [A.Normal] (hAK : A ≤ K)
    {χ : Section1.ClassFunction L} {θ : Section1.ClassFunction K}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχnotker : ¬ Section1.subgroupInKernel' χ A)
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hinner :
      Section1.scalarProduct K θ (Section1.subgroupRestriction K χ) ≠ 0) :
    ¬ Section1.subgroupInKernel' θ (A.subgroupOf K) := by
  classical
  intro hθker
  rcases hχirr with ⟨nχ, ρχ, hρχirr, hχeq⟩
  rcases hθirr with ⟨nθ, ρθ, _hρθirr, hθeq⟩
  let indρθ : Representation ℂ L (Representation.IndV K.subtype ρθ) :=
    Representation.ind K.subtype ρθ
  haveI : FiniteDimensional ℂ (Representation.IndV K.subtype ρθ) :=
    Representation.finiteDimensional_ind K ρθ
  have hIndCharKer :
      Section1.subgroupInKernel' (Section1.inducedCF K ρθ.character) A :=
    (Section1.proposition_1_6_a K A hAK ρθ).mp
      (by simpa [hθeq] using hθker)
  have hIndRepKer : Section1.subgroupInRepresentationKernel indρθ A :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      indρθ A).mp (by
        simpa [indρθ, Section1.inducedCF_eq_representation_character K ρθ]
          using hIndCharKer)
  have hχclass : Section1.IsClassFunction χ := by
    intro x g
    rw [hχeq]
    simpa [mul_assoc] using Representation.char_conj (ρ := ρχ) g x
  have hIndInner :
      Section1.scalarProduct L (Section1.inducedCF K θ) χ ≠ 0 := by
    rw [Section1.scalarProduct_inducedCF_left K θ χ hχclass]
    exact hinner
  have hIndInnerRep :
      Section1.scalarProduct L indρθ.character ρχ.character ≠ 0 := by
    simpa [indρθ, hχeq, hθeq,
      Section1.inducedCF_eq_representation_character K ρθ] using hIndInner
  have hfinrank_ne :
      (Module.finrank ℂ (Representation.IntertwiningMap ρχ indρθ) : ℂ) ≠ 0 := by
    simpa [Section1.scalarProduct_representation_char_eq_finrank ρχ indρθ]
      using hIndInnerRep
  have hfinrank_nat_ne :
      Module.finrank ℂ (Representation.IntertwiningMap ρχ indρθ) ≠ 0 := by
    intro hzero
    apply hfinrank_ne
    simp [hzero]
  have hfinrank_pos :
      0 < Module.finrank ℂ (Representation.IntertwiningMap ρχ indρθ) :=
    Nat.pos_of_ne_zero hfinrank_nat_ne
  rw [Module.finrank_pos_iff_exists_ne_zero] at hfinrank_pos
  rcases hfinrank_pos with ⟨f, hf⟩
  have hχRepKer : Section1.subgroupInRepresentationKernel ρχ A := by
    letI : Representation.IsIrreducible ρχ := hρχirr
    have hf_inj : Function.Injective f := by
      rcases (Representation.IsIrreducible.injective_or_eq_zero
          (ρ := ρχ) (σ := indρθ) f) with hinj | hzero
      · exact hinj
      · exact (hf hzero).elim
    intro a
    apply LinearMap.ext
    intro v
    apply hf_inj
    calc
      f (ρχ (a : L) v) = indρθ (a : L) (f v) := by
        exact Representation.IntertwiningMap.isIntertwining ρχ indρθ f (a : L) v
      _ = f v := by
        rw [hIndRepKer a]
        simp
  have hχkerChar : Section1.subgroupInKernel' ρχ.character A :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      ρχ A).mpr hχRepKer
  exact hχnotker (by simpa [hχeq] using hχkerChar)

private theorem exists_irreducible_constituent_of_subgroupRestriction_sec9
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ θ : Section1.ClassFunction K,
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        Section1.scalarProduct K θ (Section1.subgroupRestriction K χ) ≠ 0 := by
  rcases hχ with ⟨n, ρ, hρirr, hρchar⟩
  let ρK : Representation ℂ K (Fin n → ℂ) := ρ.comp K.subtype
  letI : Nontrivial (Fin n → ℂ) :=
    Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨φ, hφirr⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρK
  letI : Nontrivial φ.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial φ.toRepresentation
  let incl : Representation.RepMap φ.toRepresentation ρK := by
    refine Representation.RepMap.mk φ.toSubmodule.subtype ?_
    intro k
    ext v
    rfl
  have hincl_ne : incl ≠ 0 := by
    intro hzero
    obtain ⟨v, hv⟩ := exists_ne (0 : φ.toSubmodule)
    have hval : incl v = 0 := by
      simpa using
        congrArg (fun f : Representation.RepMap φ.toRepresentation ρK => f v)
          hzero
    have hsub : v = 0 := by
      apply Subtype.ext
      simpa [incl] using hval
    exact hv hsub
  have hinner_res :
      Section1.scalarProduct K ρK.character φ.toRepresentation.character ≠ 0 := by
    have hfinpos :
        0 < Module.finrank ℂ
          (Representation.IntertwiningMap φ.toRepresentation ρK) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      exact ⟨incl, hincl_ne⟩
    rw [Section1.scalarProduct_representation_char_eq_finrank]
    exact_mod_cast (Nat.ne_of_gt hfinpos)
  have hresChar :
      Section1.subgroupRestriction K χ = ρK.character := by
    ext k
    simp [ρK, Section1.subgroupRestriction, hρchar, Representation.character]
  refine ⟨φ.toRepresentation.character, ?_, ?_⟩
  · refine ⟨Module.finrank ℂ φ.toSubmodule,
      Section1.standardizeRepresentation φ.toRepresentation, ?_, ?_⟩
    · exact Section1.standardizeRepresentation_irreducible φ.toRepresentation hφirr
    · ext k
      symm
      exact Section1.standardizeRepresentation_character φ.toRepresentation k
  · have hinner_res' :
        Section1.scalarProduct K (Section1.subgroupRestriction K χ)
          φ.toRepresentation.character ≠ 0 := by
      simpa [hresChar] using hinner_res
    exact
      (Section1.scalarProduct_ne_zero_swap
        φ.toRepresentation.character (Section1.subgroupRestriction K χ)).2
        hinner_res'

private theorem exists_restriction_constituent_kernelD_sec9
    {L : Type u} [Group L] [Finite L]
    (K A B : Subgroup L) [K.Normal] [B.Normal] (hBK : B ≤ K)
    {χ : Section1.ClassFunction L}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχnotB : ¬ Section1.subgroupInKernel' χ B)
    (hχkerA : Section1.subgroupInKernel' χ A) :
    ∃ θ : Section1.ClassFunction K,
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        Section1.scalarProduct K θ (Section1.subgroupRestriction K χ) ≠ 0 ∧
          ¬ Section1.subgroupInKernel' θ (B.subgroupOf K) ∧
            Section1.subgroupInKernel' θ (A.subgroupOf K) := by
  classical
  rcases exists_irreducible_constituent_of_subgroupRestriction_sec9 K hχirr with
    ⟨θ, hθirr, hinner⟩
  have hθnotB :
      ¬ Section1.subgroupInKernel' θ (B.subgroupOf K) :=
    constituent_not_subgroupInKernel'_of_subgroupRestriction_not_kernel_sec9
      K B hBK hχirr hχnotB hθirr hinner
  have hθkerA : Section1.subgroupInKernel' θ (A.subgroupOf K) :=
    subgroupInKernel'_constituent_of_subgroupRestriction_kernel_sec9
      K A hχirr hχkerA hθirr hinner
  exact ⟨θ, hθirr, hinner, hθnotB, hθkerA⟩

public theorem theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)).Normal := by
  intro hcase
  let D : Subgroup G := ambientDerivedSubgroup M
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.mf.1 with ⟨hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
  have hMFD : MF ≤ D :=
    MF_le_ambientDerived_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  let K : Subgroup M := MF.subgroupOf M
  let Dsub : Subgroup M := D.subgroupOf M
  have hKD : K ≤ Dsub := by
    intro x hx
    have hxMF : ((x : M) : G) ∈ MF := by
      simpa [K, Subgroup.mem_subgroupOf] using hx
    have hxD : ((x : M) : G) ∈ D := hMFD hxMF
    simpa [Dsub, Subgroup.mem_subgroupOf] using hxD
  have hDsub_norm_K : Dsub ≤ Subgroup.normalizer (K : Set M) :=
    (show (⊤ : Subgroup M) ≤ Subgroup.normalizer (K : Set M) from
      Subgroup.le_normalizer_of_normal).trans' le_top
  have hKnormalD : (K.subgroupOf Dsub).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKD).2 hDsub_norm_K
  simpa [D, K, Dsub] using hKnormalD

private theorem theorem_9_8_exists_MF_restriction_constituent_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Section1.IsIrreducibleCharacterOnGroup θ →
        ¬ Section1.subgroupInKernel' θ
          ((MF.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)) →
        Section1.subgroupInKernel' θ
          ((H0.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)) →
          ∃ ψ : Section1.ClassFunction
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)),
            Section1.IsIrreducibleCharacterOnGroup ψ ∧
              Section1.scalarProduct
                ((MF.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M))
                ψ
                (Section1.subgroupRestriction
                  ((MF.subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)) θ) ≠ 0 ∧
                ¬ Section1.subgroupInKernel' ψ
                  (((MF.subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                      ((MF.subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M))) ∧
                  Section1.subgroupInKernel' ψ
                    (((H0.subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                        ((MF.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M))) := by
  classical
  intro hcase hθirr hθnotMF hθkerH0
  let D : Subgroup G := ambientDerivedSubgroup M
  let K : Subgroup (D.subgroupOf M) := (MF.subgroupOf M).subgroupOf (D.subgroupOf M)
  let A : Subgroup (D.subgroupOf M) := (H0.subgroupOf M).subgroupOf (D.subgroupOf M)
  have hKnormal : K.Normal := by
    simpa [D, K] using
      theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
        M MF U W1 W2 H0 C p q a hcase
  letI : K.Normal := hKnormal
  rcases exists_restriction_constituent_kernelD_sec9
      (L := D.subgroupOf M) K A K le_rfl hθirr
      (by simpa [D, K] using hθnotMF)
      (by simpa [D, A] using hθkerH0) with
    ⟨ψ, hψirr, hinner, hψnot, hψker⟩
  exact ⟨ψ, hψirr, by simpa [D, K] using hinner,
    by simpa [D, K] using hψnot, by simpa [D, K, A] using hψker⟩

private theorem theorem_9_8_clifford_inertia_inducing_constituent_source_core_sec9
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal]
    {θ : Section1.ClassFunction L} {ψ : Section1.ClassFunction K}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hψirr : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hinner :
      Section1.scalarProduct K ψ (Section1.subgroupRestriction K θ) ≠ 0) :
    ∃ η : Section1.ClassFunction (Section1.inertiaSubgroup K ψ),
      Section1.IsIrreducibleCharacterOnGroup η ∧
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.inducedCF (Section1.inertiaSubgroup K ψ) η) ∧
        Section1.scalarProduct (Section1.inertiaSubgroup K ψ) η
          (Section1.subgroupRestriction (Section1.inertiaSubgroup K ψ) θ) ≠ 0 := by
  classical
  have hψclass : Section1.IsClassFunction ψ :=
    Section1.isCharacter_isClassFunction ψ
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hψirr)
  have hψbook : Section1.IsBookIrreducibleCharacter ψ :=
    Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hψirr
  let T : Subgroup L := Section1.inertiaSubgroup K ψ
  let Ksub : Subgroup T := K.subgroupOf T
  have hKleT : K ≤ T :=
    Section1.proposition_1_7_inertia_contains_H K ψ hψclass
  have hsubBook : Section1.IsBookIrreducibleCharacter
      (Section1.subgroupOfClassFunction (T := T) ψ) := by
    simpa [T] using
      Section1.isBookIrreducibleCharacter_subgroupOfClassFunction_of_inertia
        K ψ hψclass hψbook
  have hindChar : Section1.IsCharacter
      (Section1.inducedCF Ksub (Section1.subgroupOfClassFunction (T := T) ψ)) :=
    Section1.isCharacter_inducedCF_of_isCharacter Ksub
      (Section1.subgroupOfClassFunction (T := T) ψ) hsubBook.1
  have hindNe :
      Section1.inducedCF Ksub (Section1.subgroupOfClassFunction (T := T) ψ) ≠ 0 := by
    intro hzero
    have hdeg_zero :
        Section1.degree
          (Section1.inducedCF Ksub (Section1.subgroupOfClassFunction (T := T) ψ)) = 0 := by
      rw [hzero]
      rfl
    have hdeg_formula :=
      Section1.degree_inducedToSubgroup K T ψ
    have hindex_ne : ((Subgroup.index Ksub : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := Ksub))
    have hψdeg_ne : Section1.degree ψ ≠ 0 :=
      Section1.degree_ne_zero_of_isBookIrreducibleCharacter ψ hψbook
    have hprod_ne :
        (Subgroup.index Ksub : ℂ) * Section1.degree ψ ≠ 0 :=
      mul_ne_zero hindex_ne hψdeg_ne
    exact hprod_ne (hdeg_formula.symm.trans hdeg_zero)
  rcases Section1.exists_positive_irreducible_decomposition_of_character
      (Section1.inducedCF Ksub (Section1.subgroupOfClassFunction (T := T) ψ))
      hindChar hindNe with
    ⟨ι, hι, hιdec, e, ηfam, i0, hepos, hηbook, hηpair, hdecompT⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := hιdec
  let χfam : ι → Section1.ClassFunction L :=
    fun i => Section1.inducedCF T (ηfam i)
  have hχdef : ∀ i : ι, χfam i = Section1.inducedCF T (ηfam i) := by
    intro i
    rfl
  rcases Section1.proposition_1_7_a K ψ hψclass hψbook e ηfam χfam
      hepos hηbook hηpair (by simpa [T, Ksub] using hdecompT) hχdef with
    ⟨_hχpair, hχbook, hdecompL⟩
  have hθclass : Section1.IsClassFunction θ :=
    Section1.isCharacter_isClassFunction θ
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
  have hweighted_inner :
      Section1.scalarProduct L
          (Section1.weightedFamilySum (fun i : ι => (e i : ℂ)) χfam) θ ≠ 0 := by
    rw [← hdecompL]
    rw [Section1.scalarProduct_inducedCF_left K ψ θ hθclass]
    exact hinner
  have hsum_inner :
      (@Finset.sum ι ℂ _ (@Finset.univ ι (Fintype.ofFinite ι)) fun i =>
        (e i : ℂ) *
          Section1.scalarProduct T (ηfam i)
            (Section1.subgroupRestriction T θ)) ≠ 0 := by
    intro hzero
    apply hweighted_inner
    calc
      Section1.scalarProduct L
          (Section1.weightedFamilySum (fun i : ι => (e i : ℂ)) χfam) θ =
          @Finset.sum ι ℂ _ (@Finset.univ ι (Fintype.ofFinite ι)) fun i =>
            (e i : ℂ) * Section1.scalarProduct L (χfam i) θ := by
            exact Section1.scalarProduct_weightedFamilySum_left
              (fun i : ι => (e i : ℂ)) χfam θ
      _ = @Finset.sum ι ℂ _ (@Finset.univ ι (Fintype.ofFinite ι)) fun i =>
            (e i : ℂ) *
            Section1.scalarProduct T (ηfam i)
              (Section1.subgroupRestriction T θ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hχdef i]
            rw [Section1.scalarProduct_inducedCF_left T (ηfam i) θ hθclass]
      _ = 0 := hzero
  have hex_inner :
      ∃ i : ι,
        Section1.scalarProduct T (ηfam i)
          (Section1.subgroupRestriction T θ) ≠ 0 := by
    by_contra hnone
    apply hsum_inner
    apply Finset.sum_eq_zero
    intro i _hi
    have hi : Section1.scalarProduct T (ηfam i)
        (Section1.subgroupRestriction T θ) = 0 := by
      by_contra hne
      exact hnone ⟨i, hne⟩
    rw [hi]
    simp
  rcases hex_inner with ⟨i, hi⟩
  exact ⟨ηfam i,
    Section1.isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (ηfam i) (hηbook i),
    Section1.isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (χfam i) (hχbook i),
    by simpa [T] using hi⟩


private def theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9
    {G : Type u} [Group G] [Finite G]
    (M U : Subgroup G) :
    ((U.subgroupOf M).subgroupOf
      ((ambientDerivedSubgroup M).subgroupOf M)) →* U where
  toFun x :=
    ⟨(((x : (ambientDerivedSubgroup M).subgroupOf M) : M) : G), by
      have hxUM :
          ((x : (ambientDerivedSubgroup M).subgroupOf M) : M) ∈ U.subgroupOf M :=
        Subgroup.mem_subgroupOf.mp x.property
      exact Subgroup.mem_subgroupOf.mp hxUM⟩
  map_one' := by
    ext
    rfl
  map_mul' x y := by
    ext
    rfl

public theorem theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal :
        ((MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal) →
        letI : ((MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
        Section2.IsInternalSemidirectProduct
          (⊤ : Subgroup ((ambientDerivedSubgroup M).subgroupOf M))
          ((MF.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M))
          ((U.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)) := by
  intro h92 hKnormal
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  let K : Subgroup (D.subgroupOf M) := (MF.subgroupOf M).subgroupOf (D.subgroupOf M)
  let W : Subgroup (D.subgroupOf M) := (U.subgroupOf M).subgroupOf (D.subgroupOf M)
  letI : K.Normal := by
    simpa [D, K] using hKnormal
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨hhallD, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hFittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hhallD with ⟨hDleM, _hDHall⟩
  rcases hcompD with ⟨_hMFleD', hUleD, hD_eq, hMFUdisj⟩
  have hMFleM : MF ≤ M := hMFleD.trans hDleM
  have hUleM : U ≤ M := hUleD.trans hDleM
  have hMFsubD : MF.subgroupOf M ≤ D.subgroupOf M := by
    intro x hx
    exact hMFleD (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hUsubD : U.subgroupOf M ≤ D.subgroupOf M := by
    intro x hx
    exact hUleD (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hsupM :
      (MF.subgroupOf M) ⊔ (U.subgroupOf M) = D.subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup (A := MF) (A' := U) (B := M) hMFleM hUleM]
    simp [D, hD_eq]
  have hdisj : Disjoint K W := by
    rw [disjoint_iff]
    apply le_antisymm
    · intro x hx
      have hxMFU : (((x : D.subgroupOf M) : M) : G) ∈ MF ⊓ U := by
        exact ⟨by
            simpa [D, K, Subgroup.mem_subgroupOf] using hx.1,
          by
            simpa [D, W, Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (((x : D.subgroupOf M) : M) : G) ∈ (⊥ : Subgroup G) := by
        exact hMFUdisj.le_bot hxMFU
      ext
      simpa using hxBot
    · exact bot_le
  have hsupTop : K ⊔ W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := MF.subgroupOf M) (A' := U.subgroupOf M)
      (B := D.subgroupOf M) hMFsubD hUsubD]
    rw [hsupM]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  exact internalSemidirectProduct_top_of_normal_isComplement'_sec9
    (isComplement'_of_disjoint_sup_eq_top_of_normal K W hdisj hsupTop)

private theorem exists_component_not_le_ker_of_iSup_eq_top_sec9
    {Q : Type u} {A : Type w} [Group Q] [Group A]
    {ι : Sort v} (H : ι → Subgroup Q) (χ : Q →* A)
    (hSup : iSup H = ⊤) (hχ : χ ≠ 1) :
    ∃ i, ¬ H i ≤ χ.ker := by
  classical
  by_contra hnone
  apply hχ
  ext x
  have htop_le : (⊤ : Subgroup Q) ≤ χ.ker := by
    rw [← hSup]
    exact iSup_le fun i => by
      intro y hy
      by_contra hyker
      exact hnone ⟨i, fun hle => hyker (hle hy)⟩
  have hxker : x ∈ χ.ker := htop_le (Subgroup.mem_top x)
  simpa [MonoidHom.mem_ker] using hxker

private theorem injective_on_prime_card_subgroup_of_not_le_ker_sec9
    {Q : Type u} {A : Type w} [Group Q] [Finite Q] [Group A]
    (χ : Q →* A) {P : Subgroup Q} {p : ℕ}
    (hcard : Nat.card P = p) (hp : Nat.Prime p) (hP : ¬ P ≤ χ.ker) :
    Function.Injective fun x : P => χ (x : Q) := by
  classical
  let χP : P →* A := χ.comp P.subtype
  haveI : Fact (Nat.Prime (Nat.card P)) := ⟨by simpa [hcard] using hp⟩
  have hker_ne_top : χP.ker ≠ ⊤ := by
    intro htop
    apply hP
    intro y hy
    let yP : P := ⟨y, hy⟩
    have hykerP : yP ∈ χP.ker := by
      rw [htop]
      exact Subgroup.mem_top yP
    change χ y = 1
    simpa [χP, yP, MonoidHom.mem_ker] using hykerP
  have hker_bot : χP.ker = ⊥ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card χP.ker with hbot | htop
    · exact hbot
    · exact False.elim (hker_ne_top htop)
  intro x y hxy
  have hdiv : x / y ∈ χP.ker := by
    change χ ((x / y : P) : Q) = 1
    simp [div_eq_mul_inv, hxy]
  have hbotmem : x / y ∈ (⊥ : Subgroup P) := by
    simpa [hker_bot] using hdiv
  have hdivone : x / y = 1 := by
    simpa using (Subgroup.mem_bot.mp hbotmem)
  exact div_eq_one.mp hdivone

private noncomputable def pullbackClassFunctionOfSubgroupOfEquiv_sec9
    {G : Type u} [Group G] {H T : Subgroup G} (hHT : H ≤ T)
    (θ : Section1.ClassFunction (H.subgroupOf T)) :
    Section1.ClassFunction H :=
  fun h => θ ((Subgroup.subgroupOfEquivOfLe hHT).symm h)

private theorem subgroupOfClassFunction_pullbackClassFunctionOfSubgroupOfEquiv_sec9
    {G : Type u} [Group G] {H T : Subgroup G} (hHT : H ≤ T)
    (θ : Section1.ClassFunction (H.subgroupOf T)) :
    Section1.subgroupOfClassFunction
        (T := T) (pullbackClassFunctionOfSubgroupOfEquiv_sec9 hHT θ) = θ := by
  ext h
  simp [pullbackClassFunctionOfSubgroupOfEquiv_sec9, Section1.subgroupOfClassFunction,
    Subgroup.subgroupOfEquivOfLe]

private theorem isIrreducible_pullbackClassFunctionOfSubgroupOfEquiv_sec9
    {G : Type u} [Group G] {H T : Subgroup G} [Finite H] [Finite T]
    (hHT : H ≤ T)
    {θ : Section1.ClassFunction (H.subgroupOf T)}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ) :
    Section1.IsIrreducibleCharacterOnGroup
      (pullbackClassFunctionOfSubgroupOfEquiv_sec9 hHT θ) := by
  classical
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  let e : H.subgroupOf T ≃* H := Subgroup.subgroupOfEquivOfLe hHT
  let ρH : Representation ℂ H (Fin n → ℂ) := ρ.comp e.symm.toMonoidHom
  refine ⟨n, ρH, ?_, ?_⟩
  · exact Section6.representation_isIrreducible_comp_surjective
      ρ e.symm.toMonoidHom e.symm.surjective hρirr
  · ext h
    simp [ρH, e, pullbackClassFunctionOfSubgroupOfEquiv_sec9, hθeq,
      Representation.character, Subgroup.subgroupOfEquivOfLe]

private theorem degree_pullbackClassFunctionOfSubgroupOfEquiv_sec9
    {G : Type u} [Group G] {H T : Subgroup G} (hHT : H ≤ T)
    (θ : Section1.ClassFunction (H.subgroupOf T)) :
    Section1.degree (pullbackClassFunctionOfSubgroupOfEquiv_sec9 hHT θ) =
      Section1.degree θ := by
  change θ ((Subgroup.subgroupOfEquivOfLe hHT).symm 1) = θ 1
  congr 1

private theorem degree_eq_one_of_irreducible_kernel_quotient_commutative_sec9
    {G : Type u} [Group G] [Finite G]
    (H T : Subgroup G) [(H.subgroupOf T).Normal]
    {θ : Section1.ClassFunction T}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθker : Section1.subgroupInKernel' θ (H.subgroupOf T))
    (hcomm : IsMulCommutative (T ⧸ H.subgroupOf T)) :
    Section1.degree θ = 1 := by
  classical
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  let q : T →* T ⧸ H.subgroupOf T := QuotientGroup.mk' (H.subgroupOf T)
  have hθkerρ : Section1.subgroupInKernel' ρ.character (H.subgroupOf T) := by
    simpa [hθeq] using hθker
  have hker : Section1.subgroupInRepresentationKernel ρ (H.subgroupOf T) :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ
      (H.subgroupOf T)).mp hθkerρ
  let ρq : Representation ℂ (T ⧸ H.subgroupOf T) (Fin n → ℂ) :=
    Section1.quotientRepresentationOfKernelSubgroup ρ (H.subgroupOf T) hker
  have hcomp_eq : ρq.comp q = ρ := by
    apply MonoidHom.ext
    intro t
    exact Section1.quotientRepresentationOfKernelSubgroup_mk ρ
      (H.subgroupOf T) hker t
  have hρqirr : Representation.IsIrreducible ρq := by
    apply Section6.representation_isIrreducible_of_comp_surjective ρq q
      (QuotientGroup.mk'_surjective (H.subgroupOf T))
    simpa [hcomp_eq] using hρirr
  haveI : IsMulCommutative (T ⧸ H.subgroupOf T) := hcomm
  have hn : n = 1 := by
    haveI : Representation.IsIrreducible ρq := hρqirr
    simpa using
      (Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := ρq))
  rw [hθeq, Section1.degree_representation_character]
  simp [hn]

private theorem theorem_9_8_nonprincipal_MF_constituent_quotient_linear_character_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (hMFleM : MF ≤ M)
    (hMFsubD : MF.subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M)
    (ψ : Section1.ClassFunction
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Section1.IsIrreducibleCharacterOnGroup ψ →
        ¬ Section1.subgroupInKernel' ψ
          (((MF.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M))) →
        Section1.subgroupInKernel' ψ
          (((H0.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M))) →
          ∃ χ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ,
            χ ≠ 1 ∧
              pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFleM
                (pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFsubD ψ) =
                Section1.quotientCharacterInflation H0 MF χ := by
  classical
  intro hcase hψirr hψnotMF hψkerH0
  let D : Subgroup G := ambientDerivedSubgroup M
  let K : Subgroup (D.subgroupOf M) := (MF.subgroupOf M).subgroupOf (D.subgroupOf M)
  let θM : Section1.ClassFunction (MF.subgroupOf M) :=
    pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFsubD ψ
  let θ : Section1.ClassFunction MF :=
    pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFleM θM
  have hθirr : Section1.IsIrreducibleCharacterOnGroup θ := by
    exact isIrreducible_pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFleM
      (isIrreducible_pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFsubD hψirr)
  have hθkerH0 : Section1.subgroupInKernel' θ (H0.subgroupOf MF) := by
    intro z
    have hzMF : ((z : MF) : G) ∈ MF := (z : MF).property
    have hzH0 : ((z : MF) : G) ∈ H0 := by
      exact (z : H0.subgroupOf MF).property
    let zM : M := ⟨(z : G), hMFleM hzMF⟩
    let zD : D.subgroupOf M := ⟨zM, by
      exact hMFsubD (by
        simp [zM, Subgroup.mem_subgroupOf])⟩
    let zK : K := ⟨zD, by
      change (zD : M) ∈ MF.subgroupOf M
      simp [zD, zM, Subgroup.mem_subgroupOf]⟩
    let zA :
        ((H0.subgroupOf M).subgroupOf (D.subgroupOf M)).subgroupOf K :=
      ⟨zK, by
        change (zK : D.subgroupOf M) ∈
          (H0.subgroupOf M).subgroupOf (D.subgroupOf M)
        change (zD : M) ∈ H0.subgroupOf M
        simpa [zD, zM, Subgroup.mem_subgroupOf] using hzH0⟩
    have hzψ := hψkerH0 zA
    have hdegθ :
        Section1.degree θ = Section1.degree ψ := by
      calc
        Section1.degree θ = Section1.degree θM := by
          exact degree_pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFleM θM
        _ = Section1.degree ψ := by
          exact degree_pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFsubD ψ
    calc
      θ z = ψ zK := by
        simp [θ, θM, zK, zD, zM, pullbackClassFunctionOfSubgroupOfEquiv_sec9,
          Subgroup.subgroupOfEquivOfLe]
      _ = Section1.degree ψ := hzψ
      _ = Section1.degree θ := hdegθ.symm
  have hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF) := by
    rcases case_9_7_a_hoReductionData_sec9 hcase with ⟨hp, _hpval, hpData⟩
    rcases hpData with
      ⟨_hH0MF, _hMFM, _hH0normalM, _hH0normalMF, _hH0ltMF, hElem, _hrest⟩
    rcases hElem with ⟨hnormal, hbarElem⟩
    letI : (H0.subgroupOf MF).Normal := hnormal
    letI : IsElementaryAbelian hp.val (MF ⧸ H0.subgroupOf MF) := hbarElem
    infer_instance
  have hθdeg : Section1.degree θ = 1 :=
    degree_eq_one_of_irreducible_kernel_quotient_commutative_sec9
      H0 MF hθirr hθkerH0 hcomm
  rcases Section1.exists_quotientLinearCharacter_of_irreducible_degree_one_kernel
      H0 MF hθirr hθkerH0 hθdeg with
    ⟨χ, hθχ⟩
  have hχne : χ ≠ 1 := by
    intro hχone
    apply hψnotMF
    intro z
    let zD : D.subgroupOf M := (z : K)
    let zM : M := zD
    let zMF : MF := ⟨(zM : G), by
      change zM ∈ MF.subgroupOf M
      exact (z : K).property⟩
    have hθtop : θ zMF = Section1.degree θ := by
      rw [hθχ, hχone]
      simp [Section1.quotientCharacterInflation, Section1.degree]
    have hdegθ :
        Section1.degree θ = Section1.degree ψ := by
      calc
        Section1.degree θ = Section1.degree θM := by
          exact degree_pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFleM θM
        _ = Section1.degree ψ := by
          exact degree_pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFsubD ψ
    calc
      ψ (z : K) = θ zMF := by
        simp [θ, θM, zMF, zD, zM, pullbackClassFunctionOfSubgroupOfEquiv_sec9,
          Subgroup.subgroupOfEquivOfLe]
      _ = Section1.degree θ := hθtop
      _ = Section1.degree ψ := hdegθ
  exact ⟨χ, hχne, hθχ⟩

private theorem theorem_9_8_semidirect_index_eq_inf_complement_index_sec9
    {L : Type u} [Group L] [Finite L]
    (K W T : Subgroup L) [K.Normal]
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) K W)
    (hKT : K ≤ T) :
    T.index = ((W ⊓ T : Subgroup L).subgroupOf W).index := by
  classical
  have hcompTop : (K.subgroupOf (⊤ : Subgroup L)).IsComplement'
      (W.subgroupOf (⊤ : Subgroup L)) :=
    Section2.internalSemidirectProduct_isComplement hsemi
  have hcardL : Nat.card L = Nat.card K * Nat.card W := by
    have hmul := hcompTop.card_mul
    calc
      Nat.card L = Nat.card (⊤ : Subgroup L) := (Subgroup.card_top (G := L)).symm
      _ = Nat.card (K.subgroupOf (⊤ : Subgroup L)) *
            Nat.card (W.subgroupOf (⊤ : Subgroup L)) := hmul.symm
      _ = Nat.card K * Nat.card W := by
        rw [natCard_subgroupOf_eq K (⊤ : Subgroup L) le_top,
          natCard_subgroupOf_eq W (⊤ : Subgroup L) le_top]
  let WT : Subgroup L := W ⊓ T
  let WTsubT : Subgroup T := WT.subgroupOf T
  let WTsubW : Subgroup W := WT.subgroupOf W
  have hWT_le_T : WT ≤ T := by simp [WT]
  have hWT_le_W : WT ≤ W := by simp [WT]
  have hKsubT_comp : (K.subgroupOf T).IsComplement' WTsubT := by
    have hdisj : Disjoint (K.subgroupOf T) WTsubT := by
      rw [disjoint_iff]
      apply le_antisymm
      · intro x hx
        have hxInf : ((x : T) : L) ∈ K ⊓ W := by
          exact ⟨by simpa [Subgroup.mem_subgroupOf] using hx.1,
            by simpa [WTsubT, WT, Subgroup.mem_subgroupOf] using hx.2.1⟩
        have hxBot : ((x : T) : L) ∈ (⊥ : Subgroup L) := by
          simpa [hsemi.inf_eq_bot] using hxInf
        ext
        simpa using hxBot
      · exact bot_le
    have hsupTop : K.subgroupOf T ⊔ WTsubT = ⊤ := by
      apply le_antisymm
      · exact le_top
      · intro x _hx
        have hxT : (x : L) ∈ T := x.property
        have hxTop : (x : L) ∈ (⊤ : Subgroup L) := by simp
        rcases hsemi.mul_surjective (x : L) hxTop with ⟨k, hkK, w, hwW, hxkw⟩
        have hkT : k ∈ T := hKT hkK
        have hkwT : k * w ∈ T := by
          rw [← hxkw]
          exact hxT
        have hwT : w ∈ T := by
          have hleft : k⁻¹ * (k * w) ∈ T := T.mul_mem (T.inv_mem hkT) hkwT
          simpa [mul_assoc] using hleft
        have hwWT : w ∈ WT := by
          simpa [WT] using (show w ∈ W ⊓ T from ⟨hwW, hwT⟩)
        let kT : T := ⟨k, hkT⟩
        let wT : T := ⟨w, hwT⟩
        have hkTmem : kT ∈ K.subgroupOf T := by
          simpa [kT, Subgroup.mem_subgroupOf] using hkK
        have hwTmem : wT ∈ WTsubT := by
          change ((wT : T) : L) ∈ WT
          simpa [wT] using hwWT
        have hx_eq : x = kT * wT := by
          ext
          simpa [kT, wT] using hxkw
        rw [hx_eq]
        exact Subgroup.mul_mem_sup hkTmem hwTmem
    letI : (K.subgroupOf T).Normal :=
      Subgroup.Normal.subgroupOf (inferInstance : K.Normal) T
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (K.subgroupOf T) WTsubT hdisj hsupTop
  have hcardT : Nat.card T = Nat.card K * Nat.card WT := by
    have hmul := hKsubT_comp.card_mul
    calc
      Nat.card T = Nat.card (K.subgroupOf T) * Nat.card WTsubT := hmul.symm
      _ = Nat.card K * Nat.card WT := by
        rw [natCard_subgroupOf_eq K T hKT,
          natCard_subgroupOf_eq WT T hWT_le_T]
  have hTmul : Nat.card T * T.index = Nat.card L := Subgroup.card_mul_index T
  have hWsubmul : Nat.card WT * WTsubW.index = Nat.card W := by
    have hmul := Subgroup.card_mul_index (H := WTsubW)
    simpa [WTsubW, natCard_subgroupOf_eq WT W hWT_le_W] using hmul
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hcancel : Nat.card WT * T.index = Nat.card W := by
    apply Nat.mul_left_cancel hKpos
    calc
      Nat.card K * (Nat.card WT * T.index)
          = Nat.card T * T.index := by rw [hcardT, Nat.mul_assoc]
      _ = Nat.card L := hTmul
      _ = Nat.card K * Nat.card W := hcardL
  have hidx : T.index = WTsubW.index := by
    exact Nat.mul_left_cancel (Nat.card_pos (α := WT)) (by
      calc
        Nat.card WT * T.index = Nat.card W := hcancel
        _ = Nat.card WT * WTsubW.index := hWsubmul.symm)
  simpa [WT, WTsubW] using hidx

private theorem theorem_9_8_index_dvd_of_semidirect_factor_kernel_sec9
    {L : Type u} [Group L] [Finite L]
    {A : Type v} [Group A]
    (K W T : Subgroup L) [K.Normal]
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) K W)
    (hKT : K ≤ T)
    (f : W →* A) (a : ℕ)
    (hcard : Nat.card f.range = a)
    (hWTker : ((W ⊓ T : Subgroup L).subgroupOf W) ≤ f.ker) :
    a ∣ T.index := by
  have hTindex : T.index = ((W ⊓ T : Subgroup L).subgroupOf W).index :=
    theorem_9_8_semidirect_index_eq_inf_complement_index_sec9 K W T hsemi hKT
  have hfindex : f.ker.index = a := by
    rw [Subgroup.index_ker, hcard]
  exact hfindex ▸ (hTindex ▸ Subgroup.index_dvd_of_le hWTker)

private theorem
    theorem_9_8_nonprincipal_MF_quotient_linear_component_centralized_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    (ψ : Section1.ClassFunction
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (hnormalH0 : (H0.subgroupOf MF).Normal) →
        letI : (H0.subgroupOf MF).Normal := hnormalH0
        (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF)) →
          (∀ i, Nat.card (H i) = p) →
            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) →
              iSupIndep H →
                iSup H = ⊤ →
                  (∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a) →
                    (hKnormal :
                      ((MF.subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M)).Normal) →
                      letI : ((MF.subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
                      (hMFleM : MF ≤ M) →
                      (hMFsubD :
                        MF.subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M) →
                      (χ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ) →
                        (i : Fin q) →
                          ¬ H i ≤ χ.ker →
                            pullbackClassFunctionOfSubgroupOfEquiv_sec9
                              hMFleM
                              (pullbackClassFunctionOfSubgroupOfEquiv_sec9
                                hMFsubD ψ) =
                                Section1.quotientCharacterInflation H0 MF χ →
                              ∀ hnormalC : (C.subgroupOf U).Normal,
                                letI : (C.subgroupOf U).Normal := hnormalC
                                ∀ x : (U.subgroupOf M).subgroupOf
                                    ((ambientDerivedSubgroup M).subgroupOf M),
                                  (x : (ambientDerivedSubgroup M).subgroupOf M) ∈
                                      Section1.inertiaSubgroup
                                        ((MF.subgroupOf M).subgroupOf
                                          ((ambientDerivedSubgroup M).subgroupOf M)) ψ →
                                    ∀ u : U,
                                      QuotientGroup.mk' (C.subgroupOf U) u =
                                        QuotientGroup.mk' (C.subgroupOf U)
                                          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x) →
                                        quotientSubgroupCentralizedByElement MF H0 (H i) (u : G) := by
  classical
  intro hcase hnormalH0 H hcard _hnorm _hindep _hSup hfac
    hKnormal hMFleM hMFsubD χ i hiχ hψχ hnormalC x hxT u hu
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : ((MF.subgroupOf M).subgroupOf
      ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
  letI : (C.subgroupOf U).Normal := hnormalC
  rcases hfac i with ⟨hnormalCfac, ρ, _hcyc, _hρcard, haction, hker⟩
  letI : (C.subgroupOf U).Normal := hnormalCfac
  have hχinj :
      Function.Injective fun y : H i => χ (y : MF ⧸ H0.subgroupOf MF) :=
    injective_on_prime_card_subgroup_of_not_le_ker_sec9 χ (hcard i)
      (case_9_7_a_p_prime_sec9 hcase) hiχ
  have hcoset_toU :
      QuotientGroup.mk' (C.subgroupOf U)
          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x) =
        QuotientGroup.mk' (C.subgroupOf U) u := hu.symm
  have hρ_eq :
      ρ (QuotientGroup.mk' (C.subgroupOf U) u) =
        ρ (QuotientGroup.mk' (C.subgroupOf U)
          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x)) := by
    rw [hu]
  have hxKernel :
      ρ (QuotientGroup.mk' (C.subgroupOf U)
          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x)) = 1 := by
    ext y
    rcases y with ⟨y, hyH⟩
    have hsubeq :
        (ρ (QuotientGroup.mk' (C.subgroupOf U)
          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x))
            ⟨y, hyH⟩ : H i) =
          (1 : MulAut (H i)) ⟨y, hyH⟩ := by
      apply hχinj
      change
        χ ((ρ (QuotientGroup.mk' (C.subgroupOf U)
          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x))
            ⟨y, hyH⟩ : H i) : MF ⧸ H0.subgroupOf MF) =
          χ ((1 : MulAut (H i)) ⟨y, hyH⟩ : H i)
      let xU : U := theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x
      revert hyH
      refine QuotientGroup.induction_on y ?_
      intro h hyH'
      rcases haction (QuotientGroup.mk' (C.subgroupOf U) xU) xU rfl with
        ⟨hconjMF, hρ_apply⟩
      let D : Subgroup G := ambientDerivedSubgroup M
      let K : Subgroup (D.subgroupOf M) :=
        (MF.subgroupOf M).subgroupOf (D.subgroupOf M)
      let hM : M := ⟨(h : G), hMFleM h.property⟩
      let hD : D.subgroupOf M := ⟨hM, by
        exact hMFsubD (by
          simp [hM, Subgroup.mem_subgroupOf])⟩
      let hK : K := ⟨hD, by
        change (hD : M) ∈ MF.subgroupOf M
        simp [hD, hM, Subgroup.mem_subgroupOf]⟩
      let hConj : MF := ⟨(xU : G)⁻¹ * (h : G) * (xU : G), hconjMF h⟩
      let hConjM : M := ⟨(hConj : G), hMFleM hConj.property⟩
      let hConjD : D.subgroupOf M := ⟨hConjM, by
        exact hMFsubD (by
          simpa [hConjM, hConj, Subgroup.mem_subgroupOf] using hConj.property)⟩
      let hConjK : K := ⟨hConjD, by
        change (hConjD : M) ∈ MF.subgroupOf M
        simpa [hConjD, hConjM, hConj, Subgroup.mem_subgroupOf] using hConj.property⟩
      have hρ_val :
          ((ρ (QuotientGroup.mk' (C.subgroupOf U) xU))
            ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hyH'⟩ :
              MF ⧸ H0.subgroupOf MF) =
            QuotientGroup.mk' (H0.subgroupOf MF) hConj := by
        simpa [xU, hConj] using hρ_apply h hyH'
      have hxInvT :
          ((x : (ambientDerivedSubgroup M).subgroupOf M)⁻¹) ∈
            Section1.inertiaSubgroup K ψ := by
        exact (Section1.inertiaSubgroup K ψ).inv_mem hxT
      have hψ_conj : ψ hConjK = ψ hK := by
        have hxInvEq :
            Section1.conjugateOnNormal K ψ
                ((x : (ambientDerivedSubgroup M).subgroupOf M)⁻¹) = ψ :=
          by
            change
              Section1.conjugateOnNormal K ψ
                  ((x : (ambientDerivedSubgroup M).subgroupOf M)⁻¹) = ψ at hxInvT
            exact hxInvT
        have hraw := congrArg (fun θ => θ hK) hxInvEq
        have hsame :
            (⟨((x : (ambientDerivedSubgroup M).subgroupOf M)⁻¹ *
                  (hK : D.subgroupOf M) *
                  ((x : (ambientDerivedSubgroup M).subgroupOf M)⁻¹)⁻¹),
                hKnormal.conj_mem (hK : D.subgroupOf M) hK.property
                  ((x : (ambientDerivedSubgroup M).subgroupOf M)⁻¹)⟩ : K) =
              hConjK := by
          ext
          simp [D, hK, hD, hM, hConjK, hConjD, hConjM, hConj, xU,
            theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9, mul_assoc]
        change
          ψ (⟨((x : D.subgroupOf M)⁻¹) * (hK : D.subgroupOf M) *
                ((x : D.subgroupOf M)⁻¹)⁻¹,
              hKnormal.conj_mem (hK : D.subgroupOf M) hK.property
                ((x : D.subgroupOf M)⁻¹)⟩ : K) = ψ hK at hraw
        rw [hsame] at hraw
        exact hraw
      have hχ_h :
          ψ hK = (χ (QuotientGroup.mk' (H0.subgroupOf MF) h) : ℂ) := by
        have heval := congrArg (fun θ => θ h) hψχ
        simpa [pullbackClassFunctionOfSubgroupOfEquiv_sec9,
          Section1.quotientCharacterInflation, Subgroup.subgroupOfEquivOfLe,
          hK, hD, hM] using heval
      have hχ_conj :
          ψ hConjK = (χ (QuotientGroup.mk' (H0.subgroupOf MF) hConj) : ℂ) := by
        have heval := congrArg (fun θ => θ hConj) hψχ
        simpa [pullbackClassFunctionOfSubgroupOfEquiv_sec9,
          Section1.quotientCharacterInflation, Subgroup.subgroupOfEquivOfLe,
          hConjK, hConjD, hConjM] using heval
      apply Units.ext
      calc
        (χ ((ρ (QuotientGroup.mk' (C.subgroupOf U) xU))
              ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hyH'⟩ :
                MF ⧸ H0.subgroupOf MF) : ℂ)
            = (χ (QuotientGroup.mk' (H0.subgroupOf MF) hConj) : ℂ) := by
              rw [hρ_val]
        _ = ψ hConjK := hχ_conj.symm
        _ = ψ hK := hψ_conj
        _ = (χ (QuotientGroup.mk' (H0.subgroupOf MF) h) : ℂ) := hχ_h
    exact congrArg Subtype.val hsubeq
  have huKernel : ρ (QuotientGroup.mk' (C.subgroupOf U) u) = 1 := by
    rw [hρ_eq, hxKernel]
  exact (hker (QuotientGroup.mk' (C.subgroupOf U) u)).mp huKernel u rfl


/-- Variant of
`theorem_9_8_nonprincipal_MF_quotient_linear_component_centralized_source_sec9`
for situations where the chosen component family is already fixed.  The
component-orbit package is not used by the centralizer calculation itself. -/
public theorem
    theorem_9_8_nonprincipal_MF_quotient_linear_component_centralized_noOrbit_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    (ψ : Section1.ClassFunction
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (hnormalH0 : (H0.subgroupOf MF).Normal) →
        letI : (H0.subgroupOf MF).Normal := hnormalH0
        (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF)) →
          (∀ i, Nat.card (H i) = p) →
            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) →
              iSupIndep H →
                iSup H = ⊤ →
                  (∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a) →
                    (hKnormal :
                      ((MF.subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M)).Normal) →
                      letI : ((MF.subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
                      (χ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ) →
                        (i : Fin q) →
                          ¬ H i ≤ χ.ker →
                            (∀ h :
                                (MF.subgroupOf M).subgroupOf
                                  ((ambientDerivedSubgroup M).subgroupOf M),
                              ψ h =
                                (χ (QuotientGroup.mk' (H0.subgroupOf MF)
                                  ⟨(((h :
                                    (ambientDerivedSubgroup M).subgroupOf M) :
                                      M) : G), by
                                    have hh :
                                        ((h :
                                          (ambientDerivedSubgroup M).subgroupOf M) :
                                            M) ∈ MF.subgroupOf M := h.property
                                    simpa [Subgroup.mem_subgroupOf] using hh⟩) :
                                  ℂ)) →
                              ∀ hnormalC : (C.subgroupOf U).Normal,
                                letI : (C.subgroupOf U).Normal := hnormalC
                                ∀ x : (U.subgroupOf M).subgroupOf
                                    ((ambientDerivedSubgroup M).subgroupOf M),
                                  (x : (ambientDerivedSubgroup M).subgroupOf M) ∈
                                      Section1.inertiaSubgroup
                                        ((MF.subgroupOf M).subgroupOf
                                          ((ambientDerivedSubgroup M).subgroupOf M)) ψ →
                                    quotientSubgroupCentralizedByElement MF H0 (H i)
                                      (((x :
                                        (ambientDerivedSubgroup M).subgroupOf M) :
                                          M) : G) := by
  classical
  intro hcase hnormalH0 H hcard hnorm hindep hSup hfac hKnormal
    χ i hiχ hψχ hnormalC x hxT
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : ((MF.subgroupOf M).subgroupOf
      ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
  letI : (C.subgroupOf U).Normal := hnormalC
  have hMFleM : MF ≤ M := case_9_7_a_MF_le_M_sec9 hcase
  have hMFsubD :
      MF.subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M := by
    intro y hy
    exact MF_le_ambientDerived_of_hypothesis_9_2_sec9 M MF U W1 W2 q
      hcase.1 (by simpa [Subgroup.mem_subgroupOf] using hy)
  have hψχ_core :
      pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFleM
        (pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFsubD ψ) =
        Section1.quotientCharacterInflation H0 MF χ := by
    ext h
    let hM : M := Subgroup.inclusion hMFleM h
    let hB :
        (MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M) :=
      ⟨Subgroup.inclusion hMFsubD ⟨hM, by
        change (hM : G) ∈ MF
        exact h.property⟩, by
          change ((Subgroup.inclusion hMFsubD ⟨hM, by
            change (hM : G) ∈ MF
            exact h.property⟩ :
              (ambientDerivedSubgroup M).subgroupOf M) : M) ∈ MF.subgroupOf M
          change (hM : G) ∈ MF
          exact h.property⟩
    have hToMF :
        (Subgroup.subgroupOfEquivOfLe hMFleM)
            ((Subgroup.subgroupOfEquivOfLe hMFsubD) hB) = h := by
      apply Subtype.ext
      rfl
    change ψ hB = (χ (QuotientGroup.mk' (H0.subgroupOf MF) h) : ℂ)
    rw [← hToMF]
    exact hψχ hB
  let u : U := ⟨(((x :
      (ambientDerivedSubgroup M).subgroupOf M) : M) : G), by
    have hxUM :
        ((x : (ambientDerivedSubgroup M).subgroupOf M) : M) ∈ U.subgroupOf M :=
      Subgroup.mem_subgroupOf.mp x.property
    simpa [Subgroup.mem_subgroupOf] using hxUM⟩
  have hquot :
      QuotientGroup.mk' (C.subgroupOf U) u =
        QuotientGroup.mk' (C.subgroupOf U)
          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x) := by
    rfl
  simpa [u] using
    theorem_9_8_nonprincipal_MF_quotient_linear_component_centralized_source_core_sec9
      M MF U W1 W2 H0 C p q a ψ hcase hnormalH0 H hcard hnorm hindep
      hSup hfac hKnormal hMFleM hMFsubD χ i hiχ hψχ_core
      hnormalC x hxT u hquot

private theorem
    theorem_9_8_nonprincipal_MF_constituent_component_centralized_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    (ψ : Section1.ClassFunction
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (hnormalH0 : (H0.subgroupOf MF).Normal) →
        letI : (H0.subgroupOf MF).Normal := hnormalH0
        (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF)) →
          (∀ i, Nat.card (H i) = p) →
            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) →
              iSupIndep H →
                iSup H = ⊤ →
                  (∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a) →
                    (∃ hqpos : 0 < q,
                      ∀ i : Fin q,
                        ∃ w : W1,
                          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩)
                            (H i) (w : G)) →
                      (hKnormal :
                        ((MF.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)).Normal) →
                        letI : ((MF.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
                        Section1.IsIrreducibleCharacterOnGroup ψ →
                          ¬ Section1.subgroupInKernel' ψ
                            (((MF.subgroupOf M).subgroupOf
                              ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                                ((MF.subgroupOf M).subgroupOf
                                  ((ambientDerivedSubgroup M).subgroupOf M))) →
                          Section1.subgroupInKernel' ψ
                            (((H0.subgroupOf M).subgroupOf
                              ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                                ((MF.subgroupOf M).subgroupOf
                                  ((ambientDerivedSubgroup M).subgroupOf M))) →
                            ∃ i : Fin q,
                              ∀ hnormalC : (C.subgroupOf U).Normal,
                                letI : (C.subgroupOf U).Normal := hnormalC
                                ∀ x : (U.subgroupOf M).subgroupOf
                                    ((ambientDerivedSubgroup M).subgroupOf M),
                                  (x : (ambientDerivedSubgroup M).subgroupOf M) ∈
                                      Section1.inertiaSubgroup
                                        ((MF.subgroupOf M).subgroupOf
                                          ((ambientDerivedSubgroup M).subgroupOf M)) ψ →
                                    ∀ u : U,
                                      QuotientGroup.mk' (C.subgroupOf U) u =
                                        QuotientGroup.mk' (C.subgroupOf U)
                                          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x) →
                                        quotientSubgroupCentralizedByElement MF H0 (H i) (u : G) := by
  classical
  intro hcase hnormalH0 H hcard hnorm hindep hSup hfac horbit hKnormal
    hψirr hψnotMF hψkerH0
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  have hMFleM : MF ≤ M := case_9_7_a_MF_le_M_sec9 hcase
  have hMFsubD : MF.subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M := by
    intro x hx
    exact MF_le_ambientDerived_of_hypothesis_9_2_sec9 M MF U W1 W2 q hcase.1
      (by simpa [Subgroup.mem_subgroupOf] using hx)
  rcases theorem_9_8_nonprincipal_MF_constituent_quotient_linear_character_sec9
      M MF U W1 W2 H0 C p q a hMFleM hMFsubD ψ hcase hψirr hψnotMF
      hψkerH0 with
    ⟨χ, hχne, hψχ⟩
  rcases exists_component_not_le_ker_of_iSup_eq_top_sec9
      (Q := MF ⧸ H0.subgroupOf MF) (A := ℂˣ) H χ hSup hχne with
    ⟨i, hiχ⟩
  refine ⟨i, ?_⟩
  exact theorem_9_8_nonprincipal_MF_quotient_linear_component_centralized_source_core_sec9
    M MF U W1 W2 H0 C p q a ψ hcase hnormalH0 H hcard hnorm hindep hSup
    hfac hKnormal hMFleM hMFsubD χ i hiχ hψχ

private theorem theorem_9_8_nonprincipal_MF_constituent_component_factor_kernel_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    (ψ : Section1.ClassFunction
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (hKnormal :
        ((MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal) →
        letI : ((MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
        Section1.IsIrreducibleCharacterOnGroup ψ →
          ¬ Section1.subgroupInKernel' ψ
            (((MF.subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                ((MF.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M))) →
          Section1.subgroupInKernel' ψ
            (((H0.subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                ((MF.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M))) →
            ∃ hnormalH0 : (H0.subgroupOf MF).Normal,
              letI : (H0.subgroupOf MF).Normal := hnormalH0
              ∃ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                ∃ hnormalC : (C.subgroupOf U).Normal,
                  letI : (C.subgroupOf U).Normal := hnormalC
                  ∃ ρ : (U ⧸ C.subgroupOf U) →* MulAut Q,
                    Nat.card ρ.range = a ∧
                      ∀ x : (U.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M),
                        (x : (ambientDerivedSubgroup M).subgroupOf M) ∈
                            Section1.inertiaSubgroup
                              ((MF.subgroupOf M).subgroupOf
                                ((ambientDerivedSubgroup M).subgroupOf M)) ψ →
                          ρ (QuotientGroup.mk' (C.subgroupOf U)
                            (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x)) = 1 := by
  intro hcase hKnormal hψirr hψnotMF hψkerH0
  rcases case_9_7_a_component_decomposition_sec9 hcase with
    ⟨hnormalH0, H, hcard, hnorm, hindep, hSup, hfac, horbit⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  rcases
      theorem_9_8_nonprincipal_MF_constituent_component_centralized_source_core_sec9
        M MF U W1 W2 H0 C p q a ψ hcase hnormalH0 H hcard hnorm hindep
        hSup hfac horbit hKnormal hψirr hψnotMF hψkerH0 with
    ⟨i, hcentralized⟩
  rcases hfac i with ⟨hnormalC, ρ, _hcyc, hρcard, _haction, hker⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  refine ⟨hnormalH0, H i, hnormalC, ρ, hρcard, ?_⟩
  intro x hxT
  exact (hker (QuotientGroup.mk' (C.subgroupOf U)
      (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x))).mpr
    (by
      intro u hu
      exact hcentralized hnormalC x hxT u hu)

private theorem theorem_9_8_nonprincipal_MF_constituent_inertia_index_dvd_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    (ψ : Section1.ClassFunction
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (hKnormal :
        ((MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal) →
        letI : ((MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
        Section1.IsIrreducibleCharacterOnGroup ψ →
          ¬ Section1.subgroupInKernel' ψ
            (((MF.subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                ((MF.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M))) →
          Section1.subgroupInKernel' ψ
            (((H0.subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                ((MF.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M))) →
            a ∣ (Section1.inertiaSubgroup
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) ψ).index := by
  classical
  intro hcase hKnormal hψirr hψnotMF hψkerH0
  let D : Subgroup G := ambientDerivedSubgroup M
  let L : Type u := D.subgroupOf M
  let K : Subgroup L := (MF.subgroupOf M).subgroupOf (D.subgroupOf M)
  let W : Subgroup L := (U.subgroupOf M).subgroupOf (D.subgroupOf M)
  let T : Subgroup L := Section1.inertiaSubgroup K ψ
  have hKnormal' : K.Normal := by
    simpa [D, L, K] using hKnormal
  letI : K.Normal := hKnormal'
  rcases theorem_9_8_nonprincipal_MF_constituent_component_factor_kernel_source_core_sec9
      M MF U W1 W2 H0 C p q a ψ hcase
      (by simpa [D, L, K] using hKnormal') hψirr hψnotMF hψkerH0 with
    ⟨hnormalH0, Q, hnormalC, ρ, hρcard, hρkerT⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  let toU : W →* U := theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U
  let f : W →* ρ.range :=
    ρ.rangeRestrict.comp ((QuotientGroup.mk' (C.subgroupOf U)).comp toU)
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q := hcase.1
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨hhallD, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hFittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hhallD with ⟨hDleM, _hDHall⟩
  rcases hcompD with ⟨_hMFleD, hUleD, _hD_eq, _hMFUdisj⟩
  have hUleM : U ≤ M := hUleD.trans hDleM
  have htoU_surj : Function.Surjective toU := by
    intro u0
    let uM : M := ⟨(u0 : G), hUleM u0.property⟩
    let uD : D.subgroupOf M :=
      ⟨uM, by
        simpa [D, Subgroup.mem_subgroupOf, uM] using hUleD u0.property⟩
    let uW : W :=
      ⟨uD, by
        change (uD : M) ∈ U.subgroupOf M
        simp [uD, uM, Subgroup.mem_subgroupOf]⟩
    exact ⟨uW, by
      ext
      rfl⟩
  have hfrange_top : f.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u0, rfl⟩
    rcases htoU_surj u0 with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    ext
    simp [f, toU, hw]
  have hfrange_card : Nat.card f.range = a := by
    rw [hfrange_top]
    simpa using hρcard
  have hKT : K ≤ T :=
    Section1.proposition_1_7_inertia_contains_H K ψ
      (Section1.isCharacter_isClassFunction ψ
        (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hψirr))
  have hWTker : ((W ⊓ T : Subgroup L).subgroupOf W) ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    change ρ.rangeRestrict
        ((QuotientGroup.mk' (C.subgroupOf U)) (toU x)) = 1
    have hxT : (x : L) ∈ T := by
      exact hx.2
    have hρone : ρ ((QuotientGroup.mk' (C.subgroupOf U)) (toU x)) = 1 :=
      hρkerT x (by simpa [D, L, K, T] using hxT)
    exact Subtype.ext (by simpa using hρone)
  have hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) K W := by
    simpa [D, L, K, W] using
      theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
        M MF U W1 W2 q h92 hKnormal
  simpa [D, L, K, W, T] using
    theorem_9_8_index_dvd_of_semidirect_factor_kernel_sec9
      K W T hsemi hKT f a hfrange_card hWTker

private theorem theorem_9_8_nonprincipal_book_constituent_inertia_witness_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M))
    (ψ : Section1.ClassFunction
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          Section1.IsIrreducibleCharacterOnGroup θ →
            Section1.IsIrreducibleCharacterOnGroup ψ →
              Section1.scalarProduct
                ((MF.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M))
                ψ
                (Section1.subgroupRestriction
                  ((MF.subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)) θ) ≠ 0 →
              ¬ Section1.subgroupInKernel' ψ
                (((MF.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                    ((MF.subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M))) →
              Section1.subgroupInKernel' ψ
                (((H0.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                    ((MF.subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M))) →
                ∃ T : Subgroup ((ambientDerivedSubgroup M).subgroupOf M),
                  ∃ η : Section1.ClassFunction T,
                    Section1.IsIrreducibleCharacterOnGroup η ∧
                      Section1.IsIrreducibleCharacterOnGroup
                        (Section1.inducedCF T η) ∧
                      Section1.scalarProduct T η
                        (Section1.subgroupRestriction T θ) ≠ 0 ∧
                      a ∣ T.index := by
  intro hcase _hBarU _hUprime hθirr hψirr hψinner hψnotMF hψkerH0
  let D : Subgroup G := ambientDerivedSubgroup M
  let K : Subgroup (D.subgroupOf M) := (MF.subgroupOf M).subgroupOf (D.subgroupOf M)
  have hKnormal : K.Normal := by
    simpa [D, K] using
      theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
        M MF U W1 W2 H0 C p q a hcase
  letI : K.Normal := hKnormal
  let T : Subgroup (D.subgroupOf M) := Section1.inertiaSubgroup K ψ
  rcases theorem_9_8_clifford_inertia_inducing_constituent_source_core_sec9
      K hθirr hψirr (by simpa [D, K] using hψinner) with
    ⟨η, hηirr, hIndηirr, hηinner⟩
  have hindex : a ∣ T.index := by
    simpa [D, K, T] using
      theorem_9_8_nonprincipal_MF_constituent_inertia_index_dvd_source_core_sec9
        M MF U W1 W2 H0 C p q a ψ hcase
        (by simpa [D, K] using hKnormal) hψirr hψnotMF hψkerH0
  exact ⟨T, η, hηirr, hIndηirr, by simpa [D, K, T] using hηinner, hindex⟩

private theorem theorem_9_8_nonprincipal_book_constituent_inertia_divisibility_data_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          Section1.IsIrreducibleCharacterOnGroup θ →
            ¬ Section1.subgroupInKernel' θ
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
            Section1.subgroupInKernel' θ
              ((H0.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
              ∃ T : Subgroup ((ambientDerivedSubgroup M).subgroupOf M),
                ∃ η : Section1.ClassFunction T,
                  Section1.IsIrreducibleCharacterOnGroup η ∧
                    θ = Section1.inducedCF T η ∧
                      a ∣ T.index := by
  intro hcase hBarU hUprime hθirr hθnotMF hθkerH0
  rcases theorem_9_8_exists_MF_restriction_constituent_sec9
      M MF U W1 W2 H0 C p q a θ hcase hθirr hθnotMF hθkerH0 with
    ⟨ψ, hψirr, hψinner, hψnotMF, hψkerH0⟩
  rcases theorem_9_8_nonprincipal_book_constituent_inertia_witness_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u θ ψ hcase hBarU hUprime
      hθirr hψirr hψinner hψnotMF hψkerH0 with
    ⟨T, η, hηirr, hIndηirr, hηinner, hindex⟩
  exact ⟨T, η, hηirr,
    inducedCF_eq_of_irreducible_constituent_sec9 T hθirr hIndηirr hηinner,
    hindex⟩

private theorem theorem_9_8_witness_constituent_degree_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          Section1.IsIrreducibleCharacterOnGroup θ →
            ¬ Section1.subgroupInKernel' θ
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
            Section1.subgroupInKernel' θ
              ((H0.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
              characterDegreeDivisibleBy a θ := by
  intro hcase hBarU hUprime hθirr hθnot hθker
  rcases theorem_9_8_nonprincipal_book_constituent_inertia_divisibility_data_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u θ hcase hBarU hUprime hθirr hθnot
      hθker with
    ⟨T, η, hηirr, hθeq, hindex⟩
  exact characterDegreeDivisibleBy_inducedCF_of_index_dvd_sec9 T a θ η
    hηirr hθeq hindex

private theorem theorem_9_8_degree_divisibility_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                (∀ χ : Section1.ClassFunction M, χ ∈ SH0 →
                  characterDegreeDivisibleBy a χ) ∧
                ∀ χ : Section1.ClassFunction M, χ ∈ SH0 →
                  ∀ θ : Section1.ClassFunction
                      ((ambientDerivedSubgroup M).subgroupOf M),
                    Section1.IsIrreducibleCharacterOnGroup θ →
                      ¬ Section1.subgroupInKernel' θ
                        ((MF.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) →
                      Section1.subgroupInKernel' θ
                        ((H0.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) →
                      χ = Section1.inducedCF
                        ((ambientDerivedSubgroup M).subgroupOf M) θ →
                        characterDegreeDivisibleBy a θ := by
  intro hcase hBarU hUprime hSH0 _hSH0C _hSH0U
  have hwitness :
      ∀ χ : Section1.ClassFunction M, χ ∈ SH0 →
        ∀ θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
          Section1.IsIrreducibleCharacterOnGroup θ →
            ¬ Section1.subgroupInKernel' θ
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
            Section1.subgroupInKernel' θ
              ((H0.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
            χ = Section1.inducedCF
              ((ambientDerivedSubgroup M).subgroupOf M) θ →
              characterDegreeDivisibleBy a θ := by
    intro _χ _hχ θ hθirr hθnot hθker _hχeq
    exact theorem_9_8_witness_constituent_degree_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u θ hcase hBarU hUprime hθirr hθnot hθker
  constructor
  · intro χ hχ
    rcases hSH0 with ⟨_hH0le, _hMFle, hmem⟩
    rcases (hmem χ).mp hχ with ⟨θ, hθirr, hθnot, hθker, hχeq⟩
    exact characterDegreeDivisibleBy_inducedCF_of_constituent_sec9
      ((ambientDerivedSubgroup M).subgroupOf M) a χ θ
      (hwitness χ hχ θ hθirr hθnot hθker hχeq) hχeq
  · exact hwitness


public def H0CLinearCandidateXmuDmuData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) : Prop :=
  ∃ ι : Type u, ∃ instFintype : Fintype ι, ∃ instDecidableEq : DecidableEq ι,
    letI : Fintype ι := instFintype
    letI : DecidableEq ι := instDecidableEq
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
    let HCD : Subgroup Dm := HCm.subgroupOf Dm
    let H0CD : Subgroup Dm := ((H0 ⊔ C).subgroupOf M).subgroupOf Dm
    let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
    ∃ θ : ι → Section1.ClassFunction Dm,
      ∃ ψ : ι → Section1.ClassFunction HCm,
        Function.Injective θ ∧
          u * Fintype.card ι = (p - 1) ^ q ∧
          (∀ i : ι,
            Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
              ¬ Section1.subgroupInKernel' (θ i) MFD ∧
              Section1.subgroupInKernel' (θ i) H0CD ∧
              Section1.IsIrreducibleCharacterOnGroup (ψ i) ∧
              Section1.degree (ψ i) = (1 : ℂ) ∧
              θ i =
                Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))) ∧
          ∃ Xmu : Finset ι,
            Xmu.card = p - 1 ∧
              (∀ i : ι, i ∈ Xmu →
                Section1.inducedCF Dm (θ i) ∈ reducibleCharacterFilter_sec9 M SH0C) ∧
              (∀ χ : Section1.ClassFunction M,
                χ ∈ reducibleCharacterFilter_sec9 M SH0C →
                  ∃ i : ι, i ∈ Xmu ∧ χ = Section1.inducedCF Dm (θ i)) ∧
              ∀ i : ι, i ∈ Xmu →
                ∀ j : ι, j ∉ Xmu →
                  Section1.inducedCF Dm (θ i) ≠ Section1.inducedCF Dm (θ j)

@[expose] public def H0CLinearCandidateXmuResidualData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) : Prop :=
  ∃ μ : Type u, ∃ instFintype : Fintype μ, ∃ instDecidableEq : DecidableEq μ,
    letI : Fintype μ := instFintype
    letI : DecidableEq μ := instDecidableEq
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let hDnormal : Dm.Normal := by
      simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
    letI : Dm.Normal := hDnormal
    let H0CD : Subgroup Dm := ((H0 ⊔ C).subgroupOf M).subgroupOf Dm
    let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
    ∃ θ : μ → Section1.ClassFunction Dm,
      Fintype.card μ = p - 1 ∧
        Function.Injective (fun i : μ => Section1.inducedCF Dm (θ i)) ∧
          (∀ i : μ,
            Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
              ¬ Section1.subgroupInKernel' (θ i) MFD ∧
              Section1.subgroupInKernel' (θ i) H0CD ∧
              Section1.inertiaSubgroup Dm (θ i) = ⊤ ∧
              Section1.inducedCF Dm (θ i) ∈
                reducibleCharacterFilter_sec9 M SH0C) ∧
          ∀ χ : Section1.ClassFunction M,
            χ ∈ reducibleCharacterFilter_sec9 M SH0C →
              ∃ i : μ, χ = Section1.inducedCF Dm (θ i)

private def H0CLinearCandidateXmuFinalImageData_sec9
    {G : Type u} [Group G] [Finite G]
    (M _MF _H0 _C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) : Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  ∃ Xmu : Finset ι,
    Xmu.card = p - 1 ∧
      (∀ i : ι, i ∈ Xmu →
        Section1.inducedCF Dm (θ i) ∈ reducibleCharacterFilter_sec9 M SH0C) ∧
      (∀ χ : Section1.ClassFunction M,
        χ ∈ reducibleCharacterFilter_sec9 M SH0C →
          ∃ i : ι, i ∈ Xmu ∧ χ = Section1.inducedCF Dm (θ i)) ∧
      ∀ i : ι, i ∈ Xmu →
        ∀ j : ι, j ∉ Xmu →
          Section1.inducedCF Dm (θ i) ≠ Section1.inducedCF Dm (θ j)


private theorem quotientBarUCardinality_pos_sec9
    {G : Type u} [Group G] [Finite G]
    (U C : Subgroup G) (u : ℕ) :
    quotientBarUCardinality U C u →
      0 < u := by
  intro hBarU
  rcases hBarU with ⟨_hCU, hnormal, hcard⟩
  letI : (C.subgroupOf U).Normal := hnormal
  rw [← hcard]
  exact Nat.card_pos

private theorem card_eq_div_of_left_mul_card_eq_sec9
    {u n m : ℕ} :
    0 < u →
      u * n = m →
        n = m / u := by
  intro hu hmul
  rw [← hmul]
  exact (Nat.mul_div_right n hu).symm

private theorem card_eq_mul_card_of_fiber_card_sec9
    {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (n : ℕ)
    (hfiber : ∀ b : β, Fintype.card {a : α // f a = b} = n) :
    Fintype.card α = n * Fintype.card β := by
  classical
  let e : α ≃ Σ b : β, {a : α // f a = b} :=
    { toFun := fun a => ⟨f a, ⟨a, rfl⟩⟩
      invFun := fun p => p.2.1
      left_inv := by
        intro a
        rfl
      right_inv := by
        intro p
        rcases p with ⟨b, a, ha⟩
        dsimp at ha ⊢
        subst ha
        rfl }
  calc
    Fintype.card α = Fintype.card (Σ b : β, {a : α // f a = b}) :=
      Fintype.card_congr e
    _ = ∑ b : β, Fintype.card {a : α // f a = b} := Fintype.card_sigma
    _ = ∑ _b : β, n := by simp [hfiber]
    _ = n * Fintype.card β := by simp [Nat.mul_comm]

private theorem freeAction_orbitQuotient_fiber_natCard_sec9
    {A : Type u} {κ : Type v} [Group A] [Finite A] [MulAction A κ] [Finite κ]
    (hstab : ∀ x : κ, MulAction.stabilizer A x = ⊥) :
    ∀ q : Quotient (MulAction.orbitRel A κ),
      Nat.card {x : κ // (Quotient.mk'' x : Quotient (MulAction.orbitRel A κ)) = q} =
        Nat.card A := by
  classical
  intro q
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype κ := Fintype.ofFinite κ
  let f : A → {x : κ // (Quotient.mk'' x : Quotient (MulAction.orbitRel A κ)) = q} :=
    fun a => ⟨a • Quotient.out q, by
      calc
        (Quotient.mk'' (a • Quotient.out q) :
            Quotient (MulAction.orbitRel A κ)) =
            Quotient.mk'' (Quotient.out q) := by
              exact Quotient.sound ((MulAction.orbitRel_apply).2 (MulAction.mem_orbit _ _))
        _ = q := Quotient.out_eq' q⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    have hsmul : a • Quotient.out q = b • Quotient.out q := by
      exact congrArg
        (fun x : {x : κ // (Quotient.mk'' x : Quotient (MulAction.orbitRel A κ)) = q} =>
          (x : κ)) hab
    have hstabmem : a⁻¹ * b ∈ MulAction.stabilizer A (Quotient.out q) := by
      rw [MulAction.mem_stabilizer_iff]
      calc
        (a⁻¹ * b) • Quotient.out q = a⁻¹ • (b • Quotient.out q) := by rw [mul_smul]
        _ = a⁻¹ • (a • Quotient.out q) := by rw [hsmul]
        _ = Quotient.out q := by rw [inv_smul_smul]
    have hbot : a⁻¹ * b ∈ (⊥ : Subgroup A) := by
      simpa [hstab (Quotient.out q)] using hstabmem
    have hab1 : a⁻¹ * b = 1 := by simpa using hbot
    exact inv_mul_eq_one.mp hab1
  have hf_surj : Function.Surjective f := by
    intro x
    have hxq : (Quotient.mk'' (x : κ) : Quotient (MulAction.orbitRel A κ)) =
        Quotient.mk'' (Quotient.out q) := by
      exact x.property.trans (Quotient.out_eq' q).symm
    have hrel : MulAction.orbitRel A κ (x : κ) (Quotient.out q) :=
      Quotient.exact hxq
    have hmem : (x : κ) ∈ MulAction.orbit A (Quotient.out q) := by
      exact (MulAction.orbitRel_apply).1 hrel
    rcases MulAction.mem_orbit_iff.mp hmem with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    ext
    exact ha
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm

private theorem theorem_9_8_Ftheta_raw_choice_card_sec9
    (p q : ℕ) :
    Fintype.card (ULift.{u, 0} (Fin q → Fin (p - 1))) = (p - 1) ^ q := by
  rw [Fintype.card_ulift]
  simp

private theorem theorem_9_8_H0C_linear_candidate_count_ne_arithmetic_core_sec9
    {p q u : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp_even_sub_one : Even (p - 1)) (huodd : Odd u)
    (hdiv : u ∣ (p - 1) ^ (q - 1)) :
    ((p - 1) ^ q) / u ≠ p - 1 := by
  intro hcount
  let b := p - 1
  let e := q - 1
  have hb_pos : 0 < b := by
    dsimp [b]
    exact Nat.sub_pos_of_lt hp.one_lt
  have hq_pos : 0 < q := Nat.Prime.pos hq
  have hq_eq : q = e + 1 := by
    dsimp [e]
    exact (Nat.sub_add_cancel hq_pos).symm
  have hbe_dvd_bq : u ∣ b ^ q := by
    rcases hdiv with ⟨t, ht⟩
    refine ⟨t * b, ?_⟩
    dsimp [b, e] at ht ⊢
    rw [hq_eq]
    calc
      (p - 1) ^ (e + 1) = (p - 1) ^ e * (p - 1) := by rw [pow_succ]
      _ = (u * t) * (p - 1) := by rw [ht]
      _ = u * (t * (p - 1)) := by ac_rfl
  have hm_eq : b ^ q = u * b :=
    Nat.eq_mul_of_div_eq_right hbe_dvd_bq (by simpa [b] using hcount)
  rcases hdiv with ⟨t, ht⟩
  have hm_eq2 : b ^ q = u * (t * b) := by
    rw [hq_eq]
    calc
      b ^ (e + 1) = b ^ e * b := by rw [pow_succ]
      _ = (u * t) * b := by rw [ht]
      _ = u * (t * b) := by ac_rfl
  have ht_cancel : b = t * b := by
    have hu_pos : 0 < u := Nat.pos_of_ne_zero (fun hu0 => by simp [hu0] at huodd)
    exact Nat.mul_left_cancel hu_pos (by simpa [hm_eq] using hm_eq2)
  have ht_one : t = 1 :=
    Nat.mul_right_cancel hb_pos (by simpa [Nat.mul_comm] using ht_cancel.symm)
  have hu_eq : u = b ^ e := by
    rw [ht_one, Nat.mul_one] at ht
    exact ht.symm
  have hb_even : Even b := by
    simpa [b] using hp_even_sub_one
  have he_pos : 0 < e := by
    dsimp [e]
    exact Nat.sub_pos_of_lt hq.one_lt
  have hbe_even : Even (b ^ e) :=
    Even.pow_of_ne_zero hb_even (Nat.ne_of_gt he_pos)
  have hu_even : Even u := by
    simpa [hu_eq] using hbe_even
  exact (Nat.not_odd_iff_even.mpr hu_even) huodd

private theorem theorem_9_8_H0C_linear_candidate_count_ne_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        ((p - 1) ^ q) / u ≠ p - 1 := by
  intro hcase hBarU
  have hqprime : Nat.Prime q := case_9_7_a_q_prime_sec9 hcase
  have hcard : Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q :=
    case_9_7_a_quotient_cardinality_sec9 hcase
  have hUodd : Odd (Nat.card U) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card U)
  have huodd : Odd u := by
    rcases hBarU with ⟨_hCU, hnormal, hbarCard⟩
    letI : (C.subgroupOf U).Normal := hnormal
    have hquot_dvd : Nat.card (U ⧸ C.subgroupOf U) ∣ Nat.card U :=
      Subgroup.card_quotient_dvd_card (C.subgroupOf U)
    have hquot_odd : Odd (Nat.card (U ⧸ C.subgroupOf U)) :=
      Odd.of_dvd_nat hUodd hquot_dvd
    simpa [hbarCard] using hquot_odd
  have hpprime : Nat.Prime p := case_9_7_a_p_prime_sec9 hcase
  have hp_dvd_quot : p ∣ Nat.card (MF ⧸ H0.subgroupOf MF) := by
    simpa [hcard] using dvd_pow_self p (Nat.pos_iff_ne_zero.mp hqprime.pos)
  have hp_dvd_G : p ∣ Nat.card G := by
    exact hp_dvd_quot.trans <|
      (Subgroup.card_quotient_dvd_card (H0.subgroupOf MF)).trans
        (Subgroup.card_subgroup_dvd_card MF)
  have hp_ne_two : p ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  have hp_even_sub_one : Even (p - 1) :=
    hpprime.even_sub_one hp_ne_two
  have hdiv : u ∣ (p - 1) ^ (q - 1) :=
    theorem_9_7_case_a_barU_card_dvd_p_minus_one_pow_sec9 M MF U W1 W2 H0 C p q a u
      hcase hBarU
  exact theorem_9_8_H0C_linear_candidate_count_ne_arithmetic_core_sec9
    hpprime hqprime hp_even_sub_one huodd hdiv

private noncomputable def piLinearCharacter_sec9
    {ι : Type v} [Fintype ι]
    (H : ι → Type u) [∀ i, Group (H i)]
    (χ : ∀ i, H i →* ℂˣ) : ((i : ι) → H i) →* ℂˣ where
  toFun x := ∏ i, χ i (x i)
  map_one' := by simp
  map_mul' x := by
    intro y
    simp [Finset.prod_mul_distrib]

private theorem piLinearCharacter_mulSingle_sec9
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (H : ι → Type u) [∀ i, Group (H i)]
    (χ : ∀ i, H i →* ℂˣ) (i : ι) (x : H i) :
    piLinearCharacter_sec9 H χ (Pi.mulSingle i x) = χ i x := by
  change (∏ j, χ j (Pi.mulSingle i x j)) = χ i x
  have hfun : (fun j => χ j (Pi.mulSingle i x j)) = Pi.mulSingle i (χ i x) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Pi.mulSingle_eq_of_ne hji]
  rw [hfun]
  simp

private noncomputable def finiteInternalProductMulEquiv_sec9
    {ι : Type v} [Fintype ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤) :
    ((i : ι) → H i) ≃* G := by
  classical
  let φ : ((i : ι) → H i) →* G := Subgroup.noncommPiCoprod (H := H) hcomm
  have hφinj : Function.Injective φ :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep (H := H) (hcomm := hcomm) hind
  have hφrange : φ.range = ⊤ := by
    calc
      φ.range = iSup H := by
        simpa [φ] using Subgroup.noncommPiCoprod_range (H := H) (hcomm := hcomm)
      _ = ⊤ := hsup
  have hφsurj : Function.Surjective φ := by
    intro g
    have hg : g ∈ φ.range := by
      rw [hφrange]
      trivial
    rcases hg with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  exact MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩

private theorem finiteInternalProductMulEquiv_apply_mulSingle_sec9
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤)
    (i : ι) (x : H i) :
    finiteInternalProductMulEquiv_sec9 H hcomm hind hsup (Pi.mulSingle i x) = x := by
  change (finiteInternalProductMulEquiv_sec9 H hcomm hind hsup).toMonoidHom
    (Pi.mulSingle i x) = x
  simp [finiteInternalProductMulEquiv_sec9, Subgroup.noncommPiCoprod_mulSingle]

set_option maxHeartbeats 800000 in
private theorem theorem_9_8_iSup_split_base_internalDirectProduct_sec9
    {ι : Type v} {G : Type u} [Group G] [IsMulCommutative G]
    (H : ι → Subgroup G) (b : ι)
    (hind : iSupIndep H) (hsup : iSup H = ⊤) :
    let Hrest : Subgroup G := ⨆ i, ⨆ _ : i ≠ b, H i
    Section2.IsInternalDirectProduct (⊤ : Subgroup G) Hrest (H b) := by
  classical
  let Hrest : Subgroup G := ⨆ i, ⨆ _ : i ≠ b, H i
  have hinf : Hrest ⊓ H b = ⊥ := by
    change (⨆ i, ⨆ _ : i ≠ b, H i) ⊓ H b = ⊥
    exact disjoint_iff.mp ((iSupIndep_def.mp hind b).symm)
  have hmul : ∀ c ∈ (⊤ : Subgroup G), ∃ h ∈ Hrest, ∃ k ∈ H b, c = h * k := by
    intro c _hc
    have hcTop : c ∈ iSup H := by
      rw [hsup]
      trivial
    have hle : iSup H ≤ Hrest ⊔ H b := by
      refine iSup_le ?_
      intro i
      by_cases hib : i = b
      · subst i
        exact le_sup_right
      · have hi_le_Hrest : H i ≤ Hrest :=
          le_iSup_of_le i (le_iSup_of_le hib le_rfl)
        exact hi_le_Hrest.trans le_sup_left
    have hcSup : c ∈ Hrest ⊔ H b := hle hcTop
    rcases (Subgroup.mem_sup_of_normal_left (s := Hrest) (t := H b) (x := c)).1
        hcSup with
      ⟨h, hh, k, hk, hhk⟩
    exact ⟨h, hh, k, hk, hhk.symm⟩
  exact
    { left_le := le_top
      right_le := le_top
      commute := by
        intro h _hh k _hk
        exact mul_comm h k
      inf_eq_bot := hinf
      mul_surjective := hmul }

private theorem internalDirectProduct_comap_mulEquiv_top_sec9
    {A B : Type u} [Group A] [Group B]
    (e : A ≃* B) {H K : Subgroup B}
    (h : Section2.IsInternalDirectProduct (⊤ : Subgroup B) H K) :
    Section2.IsInternalDirectProduct (⊤ : Subgroup A)
      (H.comap e.toMonoidHom) (K.comap e.toMonoidHom) := by
  refine
    { left_le := ?_
      right_le := ?_
      commute := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro a _ha
    trivial
  · intro a _ha
    trivial
  · intro a ha b hb
    apply e.injective
    rw [map_mul, map_mul]
    exact h.commute (e a) ha (e b) hb
  · ext a
    constructor
    · intro ha
      have hea : e a ∈ H ⊓ K := ⟨ha.1, ha.2⟩
      have hebot : e a ∈ (⊥ : Subgroup B) := by
        simpa [h.inf_eq_bot] using hea
      have heq : e a = 1 := by
        simpa using hebot
      have haeq : a = 1 := by
        apply e.injective
        simpa using heq
      simp [haeq]
    · intro ha
      have haeq : a = 1 := by simpa using ha
      simp [haeq]
  · intro a _ha
    rcases h.mul_surjective (e a) (by trivial) with ⟨h0, hh0, k0, hk0, heq⟩
    refine ⟨e.symm h0, ?_, e.symm k0, ?_, ?_⟩
    · simpa using hh0
    · simpa using hk0
    · apply e.injective
      simpa [map_mul] using heq

private theorem internalDirectProduct_map_subtype_top_sec9
    {G : Type u} [Group G] {C : Subgroup G} {H K : Subgroup C}
    (h : Section2.IsInternalDirectProduct (⊤ : Subgroup C) H K) :
    Section2.IsInternalDirectProduct C (H.map C.subtype) (K.map C.subtype) := by
  refine
    { left_le := ?_
      right_le := ?_
      commute := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro x hx
    rcases hx with ⟨h0, _hh0, rfl⟩
    exact h0.property
  · intro x hx
    rcases hx with ⟨k0, _hk0, rfl⟩
    exact k0.property
  · intro x hx y hy
    rcases hx with ⟨h0, hh0, rfl⟩
    rcases hy with ⟨k0, hk0, rfl⟩
    exact congrArg Subtype.val (h.commute h0 hh0 k0 hk0)
  · apply le_antisymm
    · intro x hx
      rcases hx.1 with ⟨h0, hh0, hhx⟩
      rcases hx.2 with ⟨k0, hk0, hkx⟩
      have hhk : h0 = k0 := by
        apply Subtype.ext
        exact hhx.trans hkx.symm
      have h0inf : h0 ∈ H ⊓ K := by
        exact ⟨hh0, by simpa [hhk] using hk0⟩
      have h0bot : h0 ∈ (⊥ : Subgroup C) := by
        simpa [h.inf_eq_bot] using h0inf
      have h0one : h0 = 1 := by
        simpa using h0bot
      have hxone : x = 1 := by
        rw [← hhx]
        exact congrArg Subtype.val h0one
      simp [hxone]
    · exact bot_le
  · intro c hc
    rcases h.mul_surjective ⟨c, hc⟩ (by trivial) with ⟨h0, hh0, k0, hk0, hprod⟩
    refine ⟨(h0 : C), ⟨h0, hh0, rfl⟩, (k0 : C), ⟨k0, hk0, rfl⟩, ?_⟩
    exact congrArg Subtype.val hprod

private theorem internalDirectProduct_sup_of_commute_inf_eq_bot_sec9
    {G : Type u} [Group G] (H K : Subgroup G)
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    (hinf : H ⊓ K = ⊥) :
    Section2.IsInternalDirectProduct (H ⊔ K) H K := by
  classical
  refine
    { left_le := le_sup_left
      right_le := le_sup_right
      commute := hcomm
      inf_eq_bot := hinf
      mul_surjective := ?_ }
  intro c hc
  have hH_norm_K : H ≤ Subgroup.normalizer (K : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      have hkh : h * k * h⁻¹ = k := by
        calc
          h * k * h⁻¹ = k * h * h⁻¹ := by
            rw [hcomm h hh k hk]
          _ = k := by simp [mul_assoc]
      simpa [hkh] using hk
    · intro hk
      have hhk : k = h⁻¹ * (h * k * h⁻¹) * h := by
        group
      have hback : h⁻¹ * (h * k * h⁻¹) * h = h * k * h⁻¹ := by
        calc
          h⁻¹ * (h * k * h⁻¹) * h =
              (h * k * h⁻¹) * h⁻¹ * h := by
                rw [hcomm h⁻¹ (H.inv_mem hh) (h * k * h⁻¹) hk]
          _ = h * k * h⁻¹ := by simp [mul_assoc]
      rw [hhk, hback]
      exact hk
  let HS : Subgroup ↥(H ⊔ K) := H.subgroupOf (H ⊔ K)
  let KS : Subgroup ↥(H ⊔ K) := K.subgroupOf (H ⊔ K)
  have hKS_normal : KS.Normal := by
    simpa [KS] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := H) (N := K) hH_norm_K)
  letI : KS.Normal := hKS_normal
  have hHSKS_top : HS ⊔ KS = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := H) (A' := K) (B := H ⊔ K)
      le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  have hcTop : (⟨c, hc⟩ : ↥(H ⊔ K)) ∈ HS ⊔ KS := by
    rw [hHSKS_top]
    trivial
  rcases (Subgroup.mem_sup_of_normal_right (s := HS) (t := KS)
      (x := (⟨c, hc⟩ : ↥(H ⊔ K)))).1 hcTop with
    ⟨h0, hh0, k0, hk0, hprod⟩
  refine ⟨(h0 : G), ?_, (k0 : G), ?_, ?_⟩
  · simpa [HS, Subgroup.mem_subgroupOf] using hh0
  · simpa [KS, Subgroup.mem_subgroupOf] using hk0
  · exact (congrArg Subtype.val hprod).symm

private noncomputable def finiteInternalProductMulAut_sec9
    {ι : Type v} [Fintype ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤)
    (α : ∀ i, MulAut (H i)) : MulAut G :=
  (finiteInternalProductMulEquiv_sec9 H hcomm hind hsup).symm.trans
    ((MulEquiv.piCongrRight fun i => (α i : H i ≃* H i)).trans
      (finiteInternalProductMulEquiv_sec9 H hcomm hind hsup))

private theorem finiteInternalProductMulAut_apply_mulSingle_sec9
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤)
    (α : ∀ i, MulAut (H i)) (i : ι) (x : H i) :
    finiteInternalProductMulAut_sec9 H hcomm hind hsup α
        (finiteInternalProductMulEquiv_sec9 H hcomm hind hsup (Pi.mulSingle i x)) =
      finiteInternalProductMulEquiv_sec9 H hcomm hind hsup (Pi.mulSingle i (α i x)) := by
  have hpi :
      (MulEquiv.piCongrRight fun i => (α i : H i ≃* H i)) (Pi.mulSingle i x) =
        Pi.mulSingle i (α i x) := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [Pi.mulSingle, hji]
  simp [finiteInternalProductMulAut_sec9, hpi]

private noncomputable def finiteInternalProductLinearCharacter_sec9
    {ι : Type v} [Fintype ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤)
    (χ : ∀ i, H i →* ℂˣ) : G →* ℂˣ :=
  (piLinearCharacter_sec9 (fun i => H i) χ).comp
    (finiteInternalProductMulEquiv_sec9 H hcomm hind hsup).symm.toMonoidHom

private theorem finiteInternalProductLinearCharacter_comp_mulSingle_sec9
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤)
    (χ : ∀ i, H i →* ℂˣ) (i : ι) :
    (finiteInternalProductLinearCharacter_sec9 H hcomm hind hsup χ).comp
      ((finiteInternalProductMulEquiv_sec9 H hcomm hind hsup).toMonoidHom.comp
        (MonoidHom.mulSingle (fun i => H i) i)) = χ i := by
  ext x
  simp [finiteInternalProductLinearCharacter_sec9, piLinearCharacter_mulSingle_sec9]


public theorem monoidHom_ext_of_iSup_eq_top_sec9
    {ι : Sort v} {G : Type u} {A : Type w}
    [Group G] [Group A]
    (H : ι → Subgroup G)
    (hsup : iSup H = ⊤)
    (f g : G →* A)
    (hfg : ∀ i, ∀ x : H i, f x = g x) :
    f = g := by
  let E : Subgroup G :=
    { carrier := {x | f x = g x}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change f (x * y) = g (x * y)
        rw [map_mul, map_mul, hx, hy]
      inv_mem' := by
        intro x hx
        change f x⁻¹ = g x⁻¹
        rw [map_inv, map_inv, hx] }
  apply MonoidHom.ext
  intro x
  have htop : (⊤ : Subgroup G) ≤ E := by
    rw [← hsup]
    exact iSup_le fun i x hx => hfg i ⟨x, hx⟩
  exact htop (Subgroup.mem_top x)

private theorem finiteInternalProductLinearCharacter_apply_subgroup_sec9
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤)
    (χ : ∀ i, H i →* ℂˣ) (i : ι) (x : H i) :
    finiteInternalProductLinearCharacter_sec9 H hcomm hind hsup χ x = χ i x := by
  have hcomp :=
    congrFun
      (congrArg DFunLike.coe
        (finiteInternalProductLinearCharacter_comp_mulSingle_sec9
          H hcomm hind hsup χ i)) x
  simpa [MonoidHom.comp_apply,
    finiteInternalProductMulEquiv_apply_mulSingle_sec9 H hcomm hind hsup i x]
    using hcomp

private theorem finiteInternalProductLinearCharacter_comp_mulAut_sec9
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤)
    (χ : ∀ i, H i →* ℂˣ) (α : ∀ i, MulAut (H i)) :
    finiteInternalProductLinearCharacter_sec9 H hcomm hind hsup
        (fun i => (χ i).comp (α i).symm.toMonoidHom) =
      (finiteInternalProductLinearCharacter_sec9 H hcomm hind hsup χ).comp
        (finiteInternalProductMulAut_sec9 H hcomm hind hsup α).symm.toMonoidHom := by
  ext y
  simp [finiteInternalProductLinearCharacter_sec9, finiteInternalProductMulAut_sec9,
    piLinearCharacter_sec9]

public theorem internalSemidirectProduct_mul_unique_sec9
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K)
    {h₁ h₂ k₁ k₂ : G}
    (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H)
    (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (hmul : h₁ * k₁ = h₂ * k₂) :
    h₁ = h₂ ∧ k₁ = k₂ := by
  have hleft_eq_right : h₂⁻¹ * h₁ = k₂ * k₁⁻¹ := by
    calc
      h₂⁻¹ * h₁ = h₂⁻¹ * (h₁ * k₁) * k₁⁻¹ := by
        simp [mul_assoc]
      _ = h₂⁻¹ * (h₂ * k₂) * k₁⁻¹ := by
        rw [hmul]
      _ = k₂ * k₁⁻¹ := by
        simp
  have hmemH : h₂⁻¹ * h₁ ∈ H :=
    H.mul_mem (H.inv_mem hh₂) hh₁
  have hmemK : h₂⁻¹ * h₁ ∈ K := by
    rw [hleft_eq_right]
    exact K.mul_mem hk₂ (K.inv_mem hk₁)
  have hbot : h₂⁻¹ * h₁ ∈ (⊥ : Subgroup G) := by
    have hinf : h₂⁻¹ * h₁ ∈ H ⊓ K :=
      Subgroup.mem_inf.mpr ⟨hmemH, hmemK⟩
    simpa [h.inf_eq_bot] using hinf
  have hh_eq_one : h₂⁻¹ * h₁ = 1 := by
    simpa using hbot
  have hh : h₁ = h₂ := by
    calc
      h₁ = h₂ * (h₂⁻¹ * h₁) := by
        simp
      _ = h₂ := by
        simp [hh_eq_one]
  have hk : k₁ = k₂ := by
    have hmul' := congrArg (fun z : G => h₂⁻¹ * z) hmul
    simpa [hh, mul_assoc] using hmul'
  exact ⟨hh, hk⟩

private noncomputable def internalSemidirectLeftComponent_sec9
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K) (c : C) : H := by
  classical
  let hs := h.mul_surjective (c : G) c.2
  exact ⟨Classical.choose hs, (Classical.choose_spec hs).1⟩

private noncomputable def internalSemidirectRightComponent_sec9
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K) (c : C) : K := by
  classical
  let hs := h.mul_surjective (c : G) c.2
  let hk := (Classical.choose_spec hs).2
  exact ⟨Classical.choose hk, (Classical.choose_spec hk).1⟩

private theorem internalSemidirectLeft_mul_rightComponent_sec9
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K) (c : C) :
    (internalSemidirectLeftComponent_sec9 h c : G) *
        (internalSemidirectRightComponent_sec9 h c : G) = c := by
  classical
  dsimp [internalSemidirectLeftComponent_sec9, internalSemidirectRightComponent_sec9]
  let hs := h.mul_surjective (c : G) c.2
  let hk := (Classical.choose_spec hs).2
  exact (Classical.choose_spec hk).2.symm

private theorem internalSemidirectRightComponent_of_mul_sec9
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K)
    {h₀ k₀ : G} (hh₀ : h₀ ∈ H) (hk₀ : k₀ ∈ K) :
    internalSemidirectRightComponent_sec9 h
        ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩ =
      ⟨k₀, hk₀⟩ := by
  apply Subtype.ext
  have hdec :=
    internalSemidirectLeft_mul_rightComponent_sec9 h
      ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩
  exact
    (internalSemidirectProduct_mul_unique_sec9 h
      (internalSemidirectLeftComponent_sec9 h
        ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩).2
      hh₀
      (internalSemidirectRightComponent_sec9 h
        ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩).2
      hk₀ hdec).2

private noncomputable def internalSemidirectRightProjection_sec9
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K) : C →* K where
  toFun := internalSemidirectRightComponent_sec9 h
  map_one' := by
    apply Subtype.ext
    have hdec := internalSemidirectLeft_mul_rightComponent_sec9 h (1 : C)
    exact
      (internalSemidirectProduct_mul_unique_sec9 h
        (internalSemidirectLeftComponent_sec9 h (1 : C)).2 H.one_mem
        (internalSemidirectRightComponent_sec9 h (1 : C)).2 K.one_mem
        (by simpa using hdec)).2
  map_mul' := by
    intro c d
    apply Subtype.ext
    let lc := internalSemidirectLeftComponent_sec9 h c
    let rc := internalSemidirectRightComponent_sec9 h c
    let ld := internalSemidirectLeftComponent_sec9 h d
    let rd := internalSemidirectRightComponent_sec9 h d
    have hdec_c : (lc : G) * (rc : G) = (c : G) :=
      internalSemidirectLeft_mul_rightComponent_sec9 h c
    have hdec_d : (ld : G) * (rd : G) = (d : G) :=
      internalSemidirectLeft_mul_rightComponent_sec9 h d
    have hleft_mem : (lc : G) * Section2.conjBy (rc : G) (ld : G) ∈ H :=
      H.mul_mem lc.2 (h.right_normalizes_left (rc : G) rc.2 (ld : G) ld.2)
    have hright_mem : (rc : G) * (rd : G) ∈ K :=
      K.mul_mem rc.2 rd.2
    have hprod :
        ((lc : G) * Section2.conjBy (rc : G) (ld : G)) * ((rc : G) * (rd : G)) =
          ((c : G) * (d : G)) := by
      calc
        ((lc : G) * Section2.conjBy (rc : G) (ld : G)) * ((rc : G) * (rd : G)) =
            ((lc : G) * (rc : G)) * ((ld : G) * (rd : G)) := by
              simp [Section2.conjBy, mul_assoc]
        _ = (c : G) * (d : G) := by
              rw [hdec_c, hdec_d]
    have hdec_cd :=
      internalSemidirectLeft_mul_rightComponent_sec9 h (c * d)
    exact
      (internalSemidirectProduct_mul_unique_sec9 h
        (internalSemidirectLeftComponent_sec9 h (c * d)).2 hleft_mem
        (internalSemidirectRightComponent_sec9 h (c * d)).2 hright_mem
        (by simpa [hprod] using hdec_cd)).2

private noncomputable def internalSemidirectRightProjectionTop_sec9
    {G : Type u} [Group G] {H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct (⊤ : Subgroup G) H K) :
    G →* K :=
  (internalSemidirectRightProjection_sec9 h).comp
    (Subgroup.topEquiv.symm.toMonoidHom : G →* (⊤ : Subgroup G))

private noncomputable def semidirectProductOfInternalDirectProductLinearCharacter_sec9
    {G : Type u} [Group G] {N W1 W2 W : Subgroup G}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup G) N W)
    (hprod : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) : G →* ℂˣ :=
  (Section3.internalDirectProductLinearCharacter hprod χ η).comp
    (internalSemidirectRightProjectionTop_sec9 hsemi)

private theorem internalSemidirectRightProjectionTop_apply_right_sec9
    {G : Type u} [Group G] {N W : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct (⊤ : Subgroup G) N W) (w : W) :
    internalSemidirectRightProjectionTop_sec9 h (w : G) = w := by
  apply Subtype.ext
  change
    (internalSemidirectRightComponent_sec9 h
        ⟨(w : G), Subgroup.mem_top (w : G)⟩ : G) = (w : G)
  have hright :=
    internalSemidirectRightComponent_of_mul_sec9 h
      (h₀ := (1 : G)) (k₀ := (w : G)) N.one_mem w.2
  simpa using congrArg Subtype.val hright

private theorem internalSemidirectRightProjectionTop_apply_left_sec9
    {G : Type u} [Group G] {N W : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct (⊤ : Subgroup G) N W) (n : N) :
    internalSemidirectRightProjectionTop_sec9 h (n : G) = 1 := by
  apply Subtype.ext
  change
    (internalSemidirectRightComponent_sec9 h
        ⟨(n : G), Subgroup.mem_top (n : G)⟩ : G) = (1 : G)
  have hright :=
    internalSemidirectRightComponent_of_mul_sec9 h
      (h₀ := (n : G)) (k₀ := (1 : G)) n.2 W.one_mem
  simpa using congrArg Subtype.val hright

private theorem semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
    {G : Type u} [Group G] {N W1 W2 W : Subgroup G}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup G) N W)
    (hprod : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) :
    (semidirectProductOfInternalDirectProductLinearCharacter_sec9 hsemi hprod χ η).comp
      W1.subtype = χ := by
  ext w
  have hproj :
      internalSemidirectRightProjectionTop_sec9 hsemi (w : G) =
        (⟨(w : G), hprod.left_le w.2⟩ : W) := by
    simpa using
      internalSemidirectRightProjectionTop_apply_right_sec9 hsemi
        (⟨(w : G), hprod.left_le w.2⟩ : W)
  calc
    (semidirectProductOfInternalDirectProductLinearCharacter_sec9 hsemi hprod χ η
        ((W1.subtype) w) : ℂ) =
        (Section3.internalDirectProductLinearCharacter hprod χ η
          (⟨(w : G), hprod.left_le w.2⟩ : W) : ℂ) := by
          simp [semidirectProductOfInternalDirectProductLinearCharacter_sec9, hproj]
    _ = (χ w : ℂ) := by
          have hcomp :
              ((Section3.internalDirectProductLinearCharacter hprod χ η)
                (Section3.internalDirectProductMulEquiv hprod
                  ((MonoidHom.inl W1 W2) w)) : ℂ) = (χ w : ℂ) := by
            simpa [MonoidHom.comp_apply] using
              congrArg (fun z : ℂˣ => (z : ℂ))
                (congrArg (fun f : W1 →* ℂˣ => f w)
                  (Section3.internalDirectProductLinearCharacter_comp_left hprod χ η))
          have happ :
              ((Section3.internalDirectProductLinearCharacter hprod χ η)
                (Section3.internalDirectProductMulEquiv hprod
                  ((MonoidHom.inl W1 W2) w)) : ℂ) =
                (Section3.internalDirectProductLinearCharacter hprod χ η
                  (⟨(w : G), hprod.left_le w.2⟩ : W) : ℂ) := by
            simpa using congrArg
              (fun z : W =>
                (Section3.internalDirectProductLinearCharacter hprod χ η z : ℂ))
              (Section3.internalDirectProductMulEquiv_apply_inl hprod w)
          exact happ.symm.trans hcomp

private theorem semidirectProductOfInternalDirectProductLinearCharacter_comp_right_sec9
    {G : Type u} [Group G] {N W1 W2 W : Subgroup G}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup G) N W)
    (hprod : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) :
    (semidirectProductOfInternalDirectProductLinearCharacter_sec9 hsemi hprod χ η).comp
      W2.subtype = η := by
  ext w
  have hproj :
      internalSemidirectRightProjectionTop_sec9 hsemi (w : G) =
        (⟨(w : G), hprod.right_le w.2⟩ : W) := by
    simpa using
      internalSemidirectRightProjectionTop_apply_right_sec9 hsemi
        (⟨(w : G), hprod.right_le w.2⟩ : W)
  calc
    (semidirectProductOfInternalDirectProductLinearCharacter_sec9 hsemi hprod χ η
        ((W2.subtype) w) : ℂ) =
        (Section3.internalDirectProductLinearCharacter hprod χ η
          (⟨(w : G), hprod.right_le w.2⟩ : W) : ℂ) := by
          simp [semidirectProductOfInternalDirectProductLinearCharacter_sec9, hproj]
    _ = (η w : ℂ) := by
          have hcomp :
              ((Section3.internalDirectProductLinearCharacter hprod χ η)
                (Section3.internalDirectProductMulEquiv hprod
                  ((MonoidHom.inr W1 W2) w)) : ℂ) = (η w : ℂ) := by
            simpa [MonoidHom.comp_apply] using
              congrArg (fun z : ℂˣ => (z : ℂ))
                (congrArg (fun f : W2 →* ℂˣ => f w)
                  (Section3.internalDirectProductLinearCharacter_comp_right hprod χ η))
          have happ :
              ((Section3.internalDirectProductLinearCharacter hprod χ η)
                (Section3.internalDirectProductMulEquiv hprod
                  ((MonoidHom.inr W1 W2) w)) : ℂ) =
                (Section3.internalDirectProductLinearCharacter hprod χ η
                  (⟨(w : G), hprod.right_le w.2⟩ : W) : ℂ) := by
            simpa using congrArg
              (fun z : W =>
                (Section3.internalDirectProductLinearCharacter hprod χ η z : ℂ))
              (Section3.internalDirectProductMulEquiv_apply_inr hprod w)
          exact happ.symm.trans hcomp


@[reducible] private noncomputable def linearCharacterMulAction_sec9
    {A : Type v} {Q : Type u} [Group A] [Group Q]
    (ρ : A →* MulAut Q) :
    MulAction A (Q →* ℂˣ) := by
  classical
  let F : A →* Function.End (Q →* ℂˣ) :=
    { toFun := fun a χ => χ.comp (ρ a).symm.toMonoidHom
      map_one' := by
        funext χ
        apply MonoidHom.ext
        intro x
        rw [map_one]
        change χ ((1 : MulAut Q).symm x) = χ x
        rfl
      map_mul' := by
        intro a b
        funext χ
        apply MonoidHom.ext
        intro x
        rw [map_mul]
        rfl }
  exact MulAction.ofEndHom F

private theorem linearCharacterMulAction_spec_sec9
    {A : Type v} {Q : Type u} [Group A] [Group Q]
    (ρ : A →* MulAut Q) (a : A) (χ : Q →* ℂˣ) :
    letI : MulAction A (Q →* ℂˣ) := linearCharacterMulAction_sec9 ρ
    a • χ = χ.comp (ρ a).symm.toMonoidHom := by
  rfl

private noncomputable def mulAutHomInvOfCommDomain_sec9
    {A : Type v} {Q : Type u} [Group A] [IsMulCommutative A] [Group Q]
    (φ : A →* MulAut Q) : A →* MulAut Q where
  toFun a := (φ a).symm
  map_one' := by
    ext x
    rw [map_one]
    rfl
  map_mul' := by
    intro a b
    ext x
    apply (φ (a * b)).injective
    simp only [MulEquiv.apply_symm_apply]
    have hcomm : φ (a * b) = φ (b * a) := by
      exact congrArg φ (mul_comm a b)
    rw [hcomm, map_mul]
    simp

private theorem kernelQuotientConjQuotientAction_sec9
    {G : Type u} {A : Type v} [Group G] [Group A]
    (f : G →* A) (N : Subgroup G) [N.Normal] :
    let K : Subgroup G := f.ker
    let Hsub : Subgroup K := N.subgroupOf K
    letI : K.Normal := inferInstance
    letI : Hsub.Normal := inferInstance
    letI : MulDistribMulAction G K :=
      MulDistribMulAction.compHom K ConjAct.toConjAct.toMonoidHom
    MulAction.QuotientAction G Hsub := by
  classical
  let K : Subgroup G := f.ker
  let Hsub : Subgroup K := N.subgroupOf K
  letI : K.Normal := inferInstance
  letI : Hsub.Normal := inferInstance
  letI : MulDistribMulAction G K :=
    MulDistribMulAction.compHom K ConjAct.toConjAct.toMonoidHom
  refine ⟨?_⟩
  intro g a a' h
  change ((g • a)⁻¹ * (g • a') : K) ∈ Hsub
  change ((((g • a)⁻¹ * (g • a') : K) : G)) ∈ N
  have hN : (((a⁻¹ * a' : K) : G)) ∈ N := by
    simpa [Hsub, Subgroup.mem_subgroupOf] using h
  have hgN := (inferInstance : N.Normal).conj_mem (((a⁻¹ * a' : K) : G)) hN g
  convert hgN using 1
  change ((g • a : K) : G)⁻¹ * ((g • a' : K) : G) =
    g * (((a⁻¹ * a' : K) : G)) * g⁻¹
  change ((ConjAct.toConjAct g • a : K) : G)⁻¹ *
      ((ConjAct.toConjAct g • a' : K) : G) =
    g * (((a⁻¹ * a' : K) : G)) * g⁻¹
  rw [ConjAct.Subgroup.val_conj_smul, ConjAct.Subgroup.val_conj_smul]
  simp [ConjAct.toConjAct_smul]
  group

@[reducible] private noncomputable def kernelQuotientConjMulDistribMulAction_sec9
    {G : Type u} {A : Type v} [Group G] [Group A]
    (f : G →* A) (N : Subgroup G) [N.Normal] :
    let K : Subgroup G := f.ker
    let Hsub : Subgroup K := N.subgroupOf K
    letI : K.Normal := inferInstance
    letI : Hsub.Normal := inferInstance
    MulDistribMulAction G (K ⧸ Hsub) := by
  classical
  let K : Subgroup G := f.ker
  let Hsub : Subgroup K := N.subgroupOf K
  letI : K.Normal := inferInstance
  letI : Hsub.Normal := inferInstance
  letI : MulDistribMulAction G K :=
    MulDistribMulAction.compHom K ConjAct.toConjAct.toMonoidHom
  letI : MulAction.QuotientAction G Hsub :=
    kernelQuotientConjQuotientAction_sec9 f N
  exact
    { (inferInstance : MulAction G (K ⧸ Hsub)) with
      smul_mul := by
        intro g q r
        refine Quotient.inductionOn₂' q r ?_
        intro x y
        change g • (((x * y : K) : K ⧸ Hsub)) =
          (((g • x : K) : K ⧸ Hsub)) * (((g • y : K) : K ⧸ Hsub))
        rw [MulAction.Quotient.smul_coe]
        change (((g • (x * y) : K) : K ⧸ Hsub)) =
          ((((g • x) * (g • y) : K) : K ⧸ Hsub))
        rw [smul_mul']
      smul_one := by
        intro g
        change g • (((1 : K) : K ⧸ Hsub)) = (((1 : K) : K ⧸ Hsub))
        rw [MulAction.Quotient.smul_coe]
        simp }

private noncomputable def kernelQuotientConjHomFromDomain_sec9
    {G : Type u} {A : Type v} [Group G] [Group A]
    (f : G →* A) (N : Subgroup G) [N.Normal] :
    let K : Subgroup G := f.ker
    let Hsub : Subgroup K := N.subgroupOf K
    letI : K.Normal := inferInstance
    letI : Hsub.Normal := inferInstance
    G →* MulAut (K ⧸ Hsub) := by
  classical
  let K : Subgroup G := f.ker
  let Hsub : Subgroup K := N.subgroupOf K
  letI : K.Normal := inferInstance
  letI : Hsub.Normal := inferInstance
  letI : MulDistribMulAction G (K ⧸ Hsub) :=
    kernelQuotientConjMulDistribMulAction_sec9 f N
  exact MulDistribMulAction.toMulAut G (K ⧸ Hsub)

private theorem kernelQuotientConjHomFromDomain_ker_le_sec9
    {G : Type u} {A : Type v} [Group G] [Group A]
    (f : G →* A) (N : Subgroup G) [N.Normal]
    (hcomm :
      let K : Subgroup G := f.ker
      let Hsub : Subgroup K := N.subgroupOf K
      letI : K.Normal := inferInstance
      letI : Hsub.Normal := inferInstance
      IsMulCommutative (K ⧸ Hsub)) :
    let K : Subgroup G := f.ker
    let Hsub : Subgroup K := N.subgroupOf K
    letI : K.Normal := inferInstance
    letI : Hsub.Normal := inferInstance
    K ≤ (kernelQuotientConjHomFromDomain_sec9 f N).ker := by
  classical
  dsimp only
  intro k hk
  rw [MonoidHom.mem_ker]
  ext q
  refine Quotient.inductionOn' q ?_
  intro x
  let K : Subgroup G := f.ker
  let Hsub : Subgroup K := N.subgroupOf K
  letI : K.Normal := inferInstance
  letI : Hsub.Normal := inferInstance
  letI : MulDistribMulAction G K :=
    MulDistribMulAction.compHom K ConjAct.toConjAct.toMonoidHom
  letI : MulAction.QuotientAction G Hsub :=
    kernelQuotientConjQuotientAction_sec9 f N
  letI : MulDistribMulAction G (K ⧸ Hsub) :=
    kernelQuotientConjMulDistribMulAction_sec9 f N
  haveI : IsMulCommutative (K ⧸ Hsub) := hcomm
  letI : CommGroup (K ⧸ Hsub) := IsMulCommutative.instCommGroup
  let kk : K := ⟨k, hk⟩
  have hconj :
      (⟨k * (x : G) * k⁻¹, (inferInstance : K.Normal).conj_mem
          (x : G) x.property k⟩ : K) =
        kk * x * kk⁻¹ := by
    ext
    simp [kk, mul_assoc]
  change k • (((x : K) : K ⧸ Hsub)) = (((x : K) : K ⧸ Hsub))
  rw [MulAction.Quotient.smul_coe]
  change QuotientGroup.mk' Hsub
      (⟨k * (x : G) * k⁻¹, (inferInstance : K.Normal).conj_mem
          (x : G) x.property k⟩ : K) =
    QuotientGroup.mk' Hsub x
  rw [hconj]
  simp [mul_assoc, mul_comm, mul_left_comm]


private noncomputable def kernelQuotientConjHomOfSurjective_sec9
    {G : Type u} {A : Type v} [Group G] [Group A]
    (f : G →* A) (N : Subgroup G) [N.Normal]
    (hcomm :
      let K : Subgroup G := f.ker
      let Hsub : Subgroup K := N.subgroupOf K
      letI : K.Normal := inferInstance
      letI : Hsub.Normal := inferInstance
      IsMulCommutative (K ⧸ Hsub))
    (hf : Function.Surjective f) :
    let K : Subgroup G := f.ker
    let Hsub : Subgroup K := N.subgroupOf K
    letI : K.Normal := inferInstance
    letI : Hsub.Normal := inferInstance
    A →* MulAut (K ⧸ Hsub) := by
  classical
  let K : Subgroup G := f.ker
  let Hsub : Subgroup K := N.subgroupOf K
  letI : K.Normal := inferInstance
  letI : Hsub.Normal := inferInstance
  let ψ : G →* MulAut (K ⧸ Hsub) :=
    kernelQuotientConjHomFromDomain_sec9 f N
  let ψbar : G ⧸ K →* MulAut (K ⧸ Hsub) :=
    QuotientGroup.lift K ψ (by
      simpa [K, ψ] using kernelQuotientConjHomFromDomain_ker_le_sec9 f N hcomm)
  exact ψbar.comp (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom

private theorem kernelQuotientConjHomOfSurjective_apply_mk_sec9
    {G : Type u} {A : Type v} [Group G] [Group A]
    (f : G →* A) (N : Subgroup G) [N.Normal]
    (hcomm :
      let K : Subgroup G := f.ker
      let Hsub : Subgroup K := N.subgroupOf K
      letI : K.Normal := inferInstance
      letI : Hsub.Normal := inferInstance
      IsMulCommutative (K ⧸ Hsub))
    (hf : Function.Surjective f) (g : G) :
    let K : Subgroup G := f.ker
    let Hsub : Subgroup K := N.subgroupOf K
    letI : K.Normal := inferInstance
    letI : Hsub.Normal := inferInstance
    ∀ x : K,
      kernelQuotientConjHomOfSurjective_sec9 f N hcomm hf (f g)
          (QuotientGroup.mk' Hsub x) =
        QuotientGroup.mk' Hsub
          (⟨g * (x : G) * g⁻¹,
            (inferInstance : K.Normal).conj_mem (x : G) x.property g⟩ : K) := by
  classical
  dsimp only
  let K : Subgroup G := f.ker
  let Hsub : Subgroup K := N.subgroupOf K
  letI : K.Normal := inferInstance
  letI : Hsub.Normal := inferInstance
  intro x
  let ψ : G →* MulAut (K ⧸ Hsub) :=
    kernelQuotientConjHomFromDomain_sec9 f N
  let ψbar : G ⧸ K →* MulAut (K ⧸ Hsub) :=
    QuotientGroup.lift K ψ (by
      simpa [K, Hsub, ψ] using
        kernelQuotientConjHomFromDomain_ker_le_sec9 f N hcomm)
  have hsymm :
      (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f g) =
        QuotientGroup.mk' K g := by
    apply (QuotientGroup.quotientKerEquivOfSurjective f hf).injective
    rw [MulEquiv.apply_symm_apply]
    change f g = QuotientGroup.kerLift f (QuotientGroup.mk' K g)
    exact (QuotientGroup.kerLift_mk f g).symm
  change
      (ψbar.comp (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom)
          (f g) (QuotientGroup.mk' Hsub x) =
        QuotientGroup.mk' Hsub
          (⟨g * (x : G) * g⁻¹,
            (inferInstance : K.Normal).conj_mem (x : G) x.property g⟩ : K)
  rw [MonoidHom.comp_apply]
  have hsymm' :
      (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom (f g) =
        QuotientGroup.mk' K g := by
    simpa using hsymm
  rw [hsymm']
  change ψbar (QuotientGroup.mk' K g) (QuotientGroup.mk' Hsub x) = _
  simp [ψbar, ψ, kernelQuotientConjHomFromDomain_sec9]
  letI : MulDistribMulAction G K :=
    MulDistribMulAction.compHom K ConjAct.toConjAct.toMonoidHom
  letI : MulAction.QuotientAction G Hsub :=
    kernelQuotientConjQuotientAction_sec9 f N
  letI : MulDistribMulAction G (K ⧸ Hsub) :=
    kernelQuotientConjMulDistribMulAction_sec9 f N
  change g • ((x : K) : K ⧸ Hsub) =
    QuotientGroup.mk' Hsub
      (⟨g * (x : G) * g⁻¹,
        (inferInstance : K.Normal).conj_mem (x : G) x.property g⟩ : K)
  rw [MulAction.Quotient.smul_coe]
  rfl


private theorem nonprincipalLinearCharacter_card_eq_pred_sec9
    (Q : Type u) [Group Q] [Finite Q] [IsMulCommutative Q]
    (p : ℕ) (hcard : Nat.card Q = p) :
    Nat.card {χ : Q →* ℂˣ // χ ≠ 1} = p - 1 := by
  classical
  letI : CommGroup Q := IsMulCommutative.instCommGroup
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) :=
    Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent Q)
  letI : Fintype (Q →* ℂˣ) := Fintype.ofFinite _
  letI : Fintype {χ : Q →* ℂˣ // χ ≠ 1} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  have hcompl := Fintype.card_subtype_compl (fun χ : Q →* ℂˣ => χ = 1)
  rw [hcompl]
  have hone : Fintype.card {χ : Q →* ℂˣ // χ = 1} = 1 :=
    Fintype.card_ofSubsingleton ⟨1, rfl⟩
  rw [hone]
  have hlin : Fintype.card (Q →* ℂˣ) = p := by
    rw [← Nat.card_eq_fintype_card]
    calc
      Nat.card (Q →* ℂˣ) = Nat.card Q := by
        exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ
      _ = p := hcard
  rw [hlin]

public noncomputable def nonprincipalLinearCharacterEquivFin_sec9
    (Q : Type u) [Group Q] [Finite Q] [IsMulCommutative Q]
    (p : ℕ) (hcard : Nat.card Q = p) :
    Fin (p - 1) ≃ {χ : Q →* ℂˣ // χ ≠ 1} := by
  classical
  letI : Fintype {χ : Q →* ℂˣ // χ ≠ 1} := Fintype.ofFinite _
  have hcard_nonprincipal :
      Fintype.card {χ : Q →* ℂˣ // χ ≠ 1} = p - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact nonprincipalLinearCharacter_card_eq_pred_sec9 Q p hcard
  exact (Fintype.equivFinOfCardEq hcard_nonprincipal).symm

public theorem case_9_7_a_quotient_isElementaryAbelian_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ} :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      ∃ hnormal : (H0.subgroupOf MF).Normal,
        letI : (H0.subgroupOf MF).Normal := hnormal
        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := by
  intro hcase
  rcases case_9_7_a_hoReductionData_sec9 hcase with ⟨hp, hp_eq, hho⟩
  rcases hho with
    ⟨_hH0MF, _hMFM, _hH0normalM, _hH0normalMF, _hH0lt, hElem, _hrest⟩
  rcases hElem with ⟨hnormal, hElem⟩
  subst hp_eq
  exact ⟨hnormal, hElem⟩

public noncomputable def componentProductLinearCharacter_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (f : Fin q → Fin (p - 1)) : G →* ℂˣ := by
  classical
  let hcomm : Pairwise fun i j : Fin q =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro _i _j _hij x y _hx _hy
    exact mul_comm x y
  exact finiteInternalProductLinearCharacter_sec9 H hcomm hHindep hHsup
    (fun i => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).1)

private theorem componentProductLinearCharacter_apply_subgroup_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (f : Fin q → Fin (p - 1)) (i : Fin q) (x : H i) :
    componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f x =
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).1 x := by
  classical
  let hcomm : Pairwise fun i j : Fin q =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro _i _j _hij x y _hx _hy
    exact mul_comm x y
  simpa [componentProductLinearCharacter_sec9, hcomm] using
    finiteInternalProductLinearCharacter_apply_subgroup_sec9 H hcomm hHindep hHsup
      (fun i => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).1)
      i x

private theorem componentProductLinearCharacter_injective_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤) :
    Function.Injective (componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup) := by
  classical
  let hcomm : Pairwise fun i j : Fin q =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro _i _j _hij x y _hx _hy
    exact mul_comm x y
  intro f g hfg
  funext i
  have hcoord := congrArg
    (fun lam : G →* ℂˣ => lam.comp
      ((finiteInternalProductMulEquiv_sec9 H hcomm hHindep hHsup).toMonoidHom.comp
        (MonoidHom.mulSingle (fun i => H i) i))) hfg
  have hchars :
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).1 =
        ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (g i)).1 := by
    calc
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).1 =
          (finiteInternalProductLinearCharacter_sec9 H hcomm hHindep hHsup
            (fun i => ((nonprincipalLinearCharacterEquivFin_sec9
              (H i) p (hHcard i)) (f i)).1)).comp
            ((finiteInternalProductMulEquiv_sec9 H hcomm hHindep hHsup).toMonoidHom.comp
              (MonoidHom.mulSingle (fun i => H i) i)) := by
        exact (finiteInternalProductLinearCharacter_comp_mulSingle_sec9 H hcomm
          hHindep hHsup
          (fun i => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
            (f i)).1) i).symm
      _ = (finiteInternalProductLinearCharacter_sec9 H hcomm hHindep hHsup
            (fun i => ((nonprincipalLinearCharacterEquivFin_sec9
              (H i) p (hHcard i)) (g i)).1)).comp
            ((finiteInternalProductMulEquiv_sec9 H hcomm hHindep hHsup).toMonoidHom.comp
              (MonoidHom.mulSingle (fun i => H i) i)) := by
        simpa [componentProductLinearCharacter_sec9, hcomm] using hcoord
      _ = ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (g i)).1 :=
        finiteInternalProductLinearCharacter_comp_mulSingle_sec9 H hcomm hHindep hHsup
          (fun i => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
            (g i)).1) i
  have hsub :
      (nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i) =
        (nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (g i) :=
    Subtype.ext hchars
  exact (nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)).injective hsub

public theorem componentProductLinearCharacter_ne_one_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (f : Fin q → Fin (p - 1)) (i : Fin q) :
    componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f ≠ 1 := by
  classical
  let hcomm : Pairwise fun i j : Fin q =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro _i _j _hij x y _hx _hy
    exact mul_comm x y
  intro htrivial
  have hcoord := congrArg
    (fun lam : G →* ℂˣ => lam.comp
      ((finiteInternalProductMulEquiv_sec9 H hcomm hHindep hHsup).toMonoidHom.comp
        (MonoidHom.mulSingle (fun i => H i) i))) htrivial
  have hchar :
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).1 = 1 := by
    calc
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).1 =
          (finiteInternalProductLinearCharacter_sec9 H hcomm hHindep hHsup
            (fun i => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
              (f i)).1)).comp
            ((finiteInternalProductMulEquiv_sec9 H hcomm hHindep hHsup).toMonoidHom.comp
              (MonoidHom.mulSingle (fun i => H i) i)) := by
        exact (finiteInternalProductLinearCharacter_comp_mulSingle_sec9 H hcomm
          hHindep hHsup
          (fun i => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
            (f i)).1) i).symm
      _ = (1 : G →* ℂˣ).comp
            ((finiteInternalProductMulEquiv_sec9 H hcomm hHindep hHsup).toMonoidHom.comp
              (MonoidHom.mulSingle (fun i => H i) i)) := by
        simpa [componentProductLinearCharacter_sec9, hcomm] using hcoord
      _ = 1 := by
        ext x
        rfl
  exact ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).2 hchar

/-- Component-product linear character allowing principal components.  A value
`none` chooses the principal character on that component; `some k` chooses the
`k`th nonprincipal character.  This is the source shape used in PF `(9.11.2)`,
where only two components are nonprincipal. -/
public noncomputable def componentProductOptionalLinearCharacter_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (f : Fin q → Option (Fin (p - 1))) : G →* ℂˣ := by
  classical
  let hcomm : Pairwise fun i j : Fin q =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro _i _j _hij x y _hx _hy
    exact mul_comm x y
  exact finiteInternalProductLinearCharacter_sec9 H hcomm hHindep hHsup
    (fun i =>
      match f i with
      | none => 1
      | some k => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) k).1)

public theorem componentProductOptionalLinearCharacter_apply_subgroup_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (f : Fin q → Option (Fin (p - 1))) (i : Fin q) (x : H i) :
    componentProductOptionalLinearCharacter_sec9 p q H hHcard hHindep hHsup f x =
      (match f i with
      | none => (1 : H i →* ℂˣ)
      | some k => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) k).1) x := by
  classical
  unfold componentProductOptionalLinearCharacter_sec9
  apply finiteInternalProductLinearCharacter_apply_subgroup_sec9

public theorem componentProductOptionalLinearCharacter_ne_one_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (f : Fin q → Option (Fin (p - 1))) (i : Fin q) (k : Fin (p - 1))
    (hf : f i = some k) :
    componentProductOptionalLinearCharacter_sec9 p q H hHcard hHindep hHsup f ≠ 1 := by
  classical
  intro htrivial
  have hchar :
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) k).1 = 1 := by
    ext x
    have hxone :
        componentProductOptionalLinearCharacter_sec9 p q H hHcard hHindep hHsup f
            (x : G) = 1 := by
      simpa using congrArg
        (fun lam : G →* ℂˣ => lam (x : G)) htrivial
    have happly :=
      componentProductOptionalLinearCharacter_apply_subgroup_sec9
        p q H hHcard hHindep hHsup f i x
    rw [hf] at happly
    exact congrArg Units.val (happly.symm.trans hxone)
  exact ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) k).2 hchar

public theorem componentProductOptionalLinearCharacter_not_le_ker_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (f : Fin q → Option (Fin (p - 1))) (i : Fin q) (k : Fin (p - 1))
    (hf : f i = some k) :
    ¬ H i ≤ (componentProductOptionalLinearCharacter_sec9
      p q H hHcard hHindep hHsup f).ker := by
  classical
  intro hker
  have hchar :
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) k).1 = 1 := by
    ext x
    have hxker :
        (componentProductOptionalLinearCharacter_sec9
          p q H hHcard hHindep hHsup f) (x : G) = 1 := by
      have hxmem : (x : G) ∈ H i := x.property
      simpa [MonoidHom.mem_ker] using hker hxmem
    have happly :=
      componentProductOptionalLinearCharacter_apply_subgroup_sec9
        p q H hHcard hHindep hHsup f i x
    rw [hf] at happly
    exact congrArg Units.val (happly.symm.trans hxker)
  exact ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) k).2 hchar

private noncomputable def nonprincipalLinearCharacterDualEquiv_sec9
    {Q : Type u} [Group Q]
    (α : MulAut Q) :
    {χ : Q →* ℂˣ // χ ≠ 1} ≃ {χ : Q →* ℂˣ // χ ≠ 1} where
  toFun χ := ⟨χ.1.comp α.symm.toMonoidHom, by
    intro hχ
    apply χ.2
    ext x
    have hval := congrArg (fun ψ : Q →* ℂˣ => ψ (α x)) hχ
    simpa using hval⟩
  invFun χ := ⟨χ.1.comp α.toMonoidHom, by
    intro hχ
    apply χ.2
    ext x
    have hval := congrArg (fun ψ : Q →* ℂˣ => ψ (α.symm x)) hχ
    simpa using hval⟩
  left_inv χ := by
    apply Subtype.ext
    ext x
    simp [MonoidHom.comp_apply]
  right_inv χ := by
    apply Subtype.ext
    ext x
    simp [MonoidHom.comp_apply]

private theorem nonprincipalLinearCharacterDualEquiv_one_sec9
    {Q : Type u} [Group Q]
    (χ : {χ : Q →* ℂˣ // χ ≠ 1}) :
    nonprincipalLinearCharacterDualEquiv_sec9 (1 : MulAut Q) χ = χ := by
  apply Subtype.ext
  ext x
  rfl

private theorem nonprincipalLinearCharacterDualEquiv_mul_sec9
    {Q : Type u} [Group Q]
    (α β : MulAut Q) (χ : {χ : Q →* ℂˣ // χ ≠ 1}) :
    nonprincipalLinearCharacterDualEquiv_sec9 (α * β) χ =
      nonprincipalLinearCharacterDualEquiv_sec9 α
        (nonprincipalLinearCharacterDualEquiv_sec9 β χ) := by
  apply Subtype.ext
  ext x
  rfl

private theorem nonprincipalLinearCharacter_injective_of_prime_card_sec9
    {Q : Type u} [Group Q] [Finite Q]
    {p : ℕ} (hcard : Nat.card Q = p) (hp : Nat.Prime p)
    (χ : {χ : Q →* ℂˣ // χ ≠ 1}) :
    Function.Injective χ.1 := by
  classical
  have htopcard : Nat.card (⊤ : Subgroup Q) = p := by
    simpa using hcard
  have hnotle : ¬ (⊤ : Subgroup Q) ≤ χ.1.ker := by
    intro hle
    apply χ.2
    ext x
    have hx : x ∈ χ.1.ker := hle (Subgroup.mem_top x)
    simpa [MonoidHom.mem_ker] using hx
  have hinjTop :
      Function.Injective fun x : (⊤ : Subgroup Q) => χ.1 (x : Q) :=
    injective_on_prime_card_subgroup_of_not_le_ker_sec9 χ.1 htopcard hp hnotle
  intro x y hxy
  have hsub :
      (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup Q)) =
        ⟨y, Subgroup.mem_top y⟩ :=
    hinjTop hxy
  exact congrArg Subtype.val hsub

private theorem mulAut_eq_one_of_nonprincipalLinearCharacterDualEquiv_eq_self_sec9
    {Q : Type u} [Group Q] [Finite Q]
    {p : ℕ} (hcard : Nat.card Q = p) (hp : Nat.Prime p)
    (α : MulAut Q) (χ : {χ : Q →* ℂˣ // χ ≠ 1})
    (hfixed : nonprincipalLinearCharacterDualEquiv_sec9 α χ = χ) :
    α = 1 := by
  classical
  have hχinj : Function.Injective χ.1 :=
    nonprincipalLinearCharacter_injective_of_prime_card_sec9 hcard hp χ
  have hsymm_one : α.symm = 1 := by
    ext x
    apply hχinj
    have hval := congrArg (fun ψ : {χ : Q →* ℂˣ // χ ≠ 1} => ψ.1 x) hfixed
    simpa [nonprincipalLinearCharacterDualEquiv_sec9, MonoidHom.comp_apply] using hval
  ext x
  have hval := congrArg (fun β : MulAut Q => β (α x)) hsymm_one
  simpa using hval.symm

@[reducible] private noncomputable def nonprincipalLinearCharacterIndexMulAction_sec9
    {A : Type v} {Q : Type u} [Group A] [Group Q] [Finite Q] [IsMulCommutative Q]
    (p : ℕ) (hcard : Nat.card Q = p)
    (ρ : A →* MulAut Q) :
    MulAction A (Fin (p - 1)) := by
  classical
  let e := nonprincipalLinearCharacterEquivFin_sec9 Q p hcard
  let F : A →* Function.End (Fin (p - 1)) :=
    { toFun := fun a i => e.symm (nonprincipalLinearCharacterDualEquiv_sec9 (ρ a) (e i))
      map_one' := by
        funext i
        apply e.injective
        dsimp
        calc
          e (e.symm (nonprincipalLinearCharacterDualEquiv_sec9 (ρ 1) (e i))) =
              nonprincipalLinearCharacterDualEquiv_sec9 (ρ 1) (e i) := by
                exact e.apply_symm_apply _
          _ = nonprincipalLinearCharacterDualEquiv_sec9 (1 : MulAut Q) (e i) := by
                rw [map_one]
          _ = e i := nonprincipalLinearCharacterDualEquiv_one_sec9 (e i)
      map_mul' := by
        intro a b
        funext i
        apply e.injective
        dsimp
        calc
          e (e.symm (nonprincipalLinearCharacterDualEquiv_sec9 (ρ (a * b)) (e i))) =
              nonprincipalLinearCharacterDualEquiv_sec9 (ρ (a * b)) (e i) := by
                exact e.apply_symm_apply _
          _ = nonprincipalLinearCharacterDualEquiv_sec9 (ρ a * ρ b) (e i) := by
                rw [map_mul]
          _ = nonprincipalLinearCharacterDualEquiv_sec9 (ρ a)
                (nonprincipalLinearCharacterDualEquiv_sec9 (ρ b) (e i)) :=
                nonprincipalLinearCharacterDualEquiv_mul_sec9 (ρ a) (ρ b) (e i)
          _ = e (e.symm (nonprincipalLinearCharacterDualEquiv_sec9 (ρ a)
                (e (e.symm (nonprincipalLinearCharacterDualEquiv_sec9 (ρ b) (e i)))))) := by
                simp }
  exact MulAction.ofEndHom F

private theorem nonprincipalLinearCharacterIndexMulAction_spec_sec9
    {A : Type v} {Q : Type u} [Group A] [Group Q] [Finite Q] [IsMulCommutative Q]
    (p : ℕ) (hcard : Nat.card Q = p)
    (ρ : A →* MulAut Q)
    (a : A) (i : Fin (p - 1)) :
    letI : MulAction A (Fin (p - 1)) :=
      nonprincipalLinearCharacterIndexMulAction_sec9 p hcard ρ
    ((nonprincipalLinearCharacterEquivFin_sec9 Q p hcard) (a • i)).1 =
      (((nonprincipalLinearCharacterEquivFin_sec9 Q p hcard) i).1.comp
        (ρ a).symm.toMonoidHom) := by
  classical
  letI : MulAction A (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p hcard ρ
  let e := nonprincipalLinearCharacterEquivFin_sec9 Q p hcard
  change (e (e.symm (nonprincipalLinearCharacterDualEquiv_sec9 (ρ a) (e i)))).1 =
    ((e i).1.comp (ρ a).symm.toMonoidHom)
  simp [e, nonprincipalLinearCharacterDualEquiv_sec9]

public theorem nonprincipalIndexAction_fixed_eq_one_data_sec9
    {A : Type v} {Q : Type u} [Group A] [Group Q] [Finite Q] [IsMulCommutative Q]
    (p : ℕ) (hp : Nat.Prime p)
    (hcard : Nat.card Q = p)
    (ρ : A →* MulAut Q) :
    ∃ instAction : MulAction A (Fin (p - 1)),
      letI : MulAction A (Fin (p - 1)) := instAction
      ∀ a : A, ∀ i : Fin (p - 1), a • i = i → ρ a = 1 := by
  classical
  let instAction : MulAction A (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p hcard ρ
  refine ⟨instAction, ?_⟩
  letI : MulAction A (Fin (p - 1)) := instAction
  intro a i hfix
  let e := nonprincipalLinearCharacterEquivFin_sec9 Q p hcard
  have hcharfixed :
      nonprincipalLinearCharacterDualEquiv_sec9 (ρ a) (e i) = e i := by
    apply Subtype.ext
    have hspec :=
      nonprincipalLinearCharacterIndexMulAction_spec_sec9 p hcard ρ a i
    have hleft : (e (a • i)).1 = (e i).1 :=
      congrArg Subtype.val (congrArg e hfix)
    exact hspec.symm.trans hleft
  exact
    mulAut_eq_one_of_nonprincipalLinearCharacterDualEquiv_eq_self_sec9
      hcard hp (ρ a) (e i) hcharfixed

@[reducible] private noncomputable def rawCoordinateMulAction_sec9
    {A : Type v} {G : Type u} [Group A] [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρ : ∀ i, A →* MulAut (H i)) :
    MulAction A (ULift.{u, 0} (Fin q → Fin (p - 1))) := by
  classical
  let F : A →* Function.End (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
    { toFun := fun a f =>
        ULift.up fun i =>
          letI : MulAction A (Fin (p - 1)) :=
            nonprincipalLinearCharacterIndexMulAction_sec9 p (hHcard i) (ρ i)
          a • f.down i
      map_one' := by
        funext f
        rcases f with ⟨down⟩
        apply ULift.ext
        funext i
        letI : MulAction A (Fin (p - 1)) :=
          nonprincipalLinearCharacterIndexMulAction_sec9 p (hHcard i) (ρ i)
        change (1 : A) • down i = down i
        rw [one_smul]
      map_mul' := by
        intro a b
        funext f
        rcases f with ⟨down⟩
        apply ULift.ext
        funext i
        letI : MulAction A (Fin (p - 1)) :=
          nonprincipalLinearCharacterIndexMulAction_sec9 p (hHcard i) (ρ i)
        change (a * b) • down i = a • b • down i
        rw [mul_smul] }
  exact MulAction.ofEndHom F

private theorem rawCoordinateMulAction_down_sec9
    {A : Type v} {G : Type u} [Group A] [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρ : ∀ i, A →* MulAut (H i))
    (a : A) (f : ULift.{u, 0} (Fin q → Fin (p - 1))) (i : Fin q) :
    letI : MulAction A (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    (a • f).down i =
      letI : MulAction A (Fin (p - 1)) :=
        nonprincipalLinearCharacterIndexMulAction_sec9 p (hHcard i) (ρ i)
      a • f.down i := by
  rfl

private theorem rawCoordinateMulAction_component_eq_one_of_fixed_sec9
    {A : Type v} {G : Type u} [Group A] [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ) (hp : Nat.Prime p)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρ : ∀ i, A →* MulAut (H i))
    (a : A) (f : ULift.{u, 0} (Fin q → Fin (p - 1))) :
    letI : MulAction A (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    a • f = f →
      ∀ i, ρ i a = 1 := by
  classical
  letI : MulAction A (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  intro hfix i
  letI : MulAction A (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p (hHcard i) (ρ i)
  let e := nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)
  have hcoord : a • f.down i = f.down i := by
    have hdown := congrArg (fun z : ULift.{u, 0} (Fin q → Fin (p - 1)) =>
      z.down i) hfix
    simpa [rawCoordinateMulAction_down_sec9] using hdown
  have hcharfixed :
      nonprincipalLinearCharacterDualEquiv_sec9 (ρ i a) (e (f.down i)) =
        e (f.down i) := by
    apply Subtype.ext
    have hspec :=
      nonprincipalLinearCharacterIndexMulAction_spec_sec9
        p (hHcard i) (ρ i) a (f.down i)
    have hleft :
        (e (a • f.down i)).1 = (e (f.down i)).1 := by
      exact congrArg Subtype.val (congrArg e hcoord)
    exact hspec.symm.trans hleft
  exact
    mulAut_eq_one_of_nonprincipalLinearCharacterDualEquiv_eq_self_sec9
      (hHcard i) hp (ρ i a) (e (f.down i)) hcharfixed

private theorem componentProductLinearCharacter_rawCoordinateMulAction_sec9
    {A : Type v} {G : Type u} [Group A] [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρ : ∀ i, A →* MulAut (H i))
    (a : A) (f : ULift.{u, 0} (Fin q → Fin (p - 1))) :
    letI : MulAction A (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
        (a • f).down =
      (componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
        f.down).comp
        (finiteInternalProductMulAut_sec9 H
          (by
            intro _i _j _hij x y _hx _hy
            exact mul_comm x y)
          hHindep hHsup (fun i => ρ i a)).symm.toMonoidHom := by
  classical
  letI : MulAction A (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  let hcomm : Pairwise fun i j : Fin q =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro _i _j _hij x y _hx _hy
    exact mul_comm x y
  change finiteInternalProductLinearCharacter_sec9 H hcomm hHindep hHsup
      (fun i =>
        ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
          ((a • f).down i)).1) =
    (finiteInternalProductLinearCharacter_sec9 H hcomm hHindep hHsup
      (fun i =>
        ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
          (f.down i)).1)).comp
      (finiteInternalProductMulAut_sec9 H hcomm hHindep hHsup
        (fun i => ρ i a)).symm.toMonoidHom
  have hχ :
      (fun i =>
        ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
          ((a • f).down i)).1) =
        (fun i =>
          (((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
            (f.down i)).1).comp (ρ i a).symm.toMonoidHom) := by
    funext i
    ext x
    have hspec :=
      nonprincipalLinearCharacterIndexMulAction_spec_sec9 p (hHcard i) (ρ i)
        a (f.down i)
    exact congrArg Units.val <| by
      simpa [rawCoordinateMulAction_down_sec9] using
        congrFun (congrArg DFunLike.coe hspec) x
  rw [hχ]
  exact finiteInternalProductLinearCharacter_comp_mulAut_sec9 H hcomm hHindep hHsup
    (fun i =>
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
        (f.down i)).1)
    (fun i => ρ i a)

private theorem mulAut_eq_of_eq_on_iSup_eq_top_sec9
    {ι : Sort v} {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hHsup : iSup H = ⊤)
    (α β : MulAut G)
    (hfix : ∀ i, ∀ x : G, x ∈ H i → α x = β x) :
    α = β := by
  ext x
  let K : Subgroup G :=
    { carrier := {x | α x = β x}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change α (x * y) = β (x * y)
        rw [map_mul, map_mul, hx, hy]
      inv_mem' := by
        intro x hx
        change α x⁻¹ = β x⁻¹
        rw [map_inv, map_inv, hx] }
  have htop_le : (⊤ : Subgroup G) ≤ K := by
    rw [← hHsup]
    exact iSup_le fun i => by
      intro x hx
      exact hfix i x hx
  exact htop_le (Subgroup.mem_top x)

private theorem finiteInternalProductMulAut_eq_quotientConjAction_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C : Subgroup G}
    {q : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hqpos : 0 < q)
    (x : U ⧸ C.subgroupOf U) (u : U)
    (hux : QuotientGroup.mk' (C.subgroupOf U) u = x) :
    ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
      ∀ h : MF,
        finiteInternalProductMulAut_sec9 H
            (by
              intro _i _j _hij y z _hy _hz
              exact mul_comm y z)
            hHindep hHsup (fun i => ρ i x)
          (QuotientGroup.mk' (H0.subgroupOf MF) h) =
        QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩ := by
  classical
  let hcommPair : Pairwise fun i j : Fin q =>
      ∀ y z : MF ⧸ H0.subgroupOf MF, y ∈ H i → z ∈ H j → Commute y z := by
    intro _i _j _hij y z _hy _hz
    exact mul_comm y z
  let α : MulAut (MF ⧸ H0.subgroupOf MF) :=
    finiteInternalProductMulAut_sec9 H hcommPair hHindep hHsup (fun i => ρ i x)
  let i0 : Fin q := ⟨0, hqpos⟩
  rcases hHnorm i0 u with ⟨hconjMF0, action0, haction0, _hmap0⟩
  have hαeq : α = action0 := by
    apply mulAut_eq_of_eq_on_iSup_eq_top_sec9 H hHsup
    intro i y hy
    let yH : H i := ⟨y, hy⟩
    have hαy : α y = (ρ i x yH : MF ⧸ H0.subgroupOf MF) := by
      have hsingle :=
        finiteInternalProductMulAut_apply_mulSingle_sec9 H hcommPair hHindep hHsup
          (fun i => ρ i x) i yH
      simpa [α, yH,
        finiteInternalProductMulEquiv_apply_mulSingle_sec9 H hcommPair hHindep hHsup]
        using hsingle
    rcases hHnorm i u with ⟨hconjMFi, actioni, hactioni, _hmapi⟩
    have haction_eq : actioni = action0 := by
      ext z
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) z with ⟨t, rfl⟩
      calc
        actioni (QuotientGroup.mk' (H0.subgroupOf MF) t) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (t : G) * (u : G), hconjMFi t⟩ := hactioni t
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (t : G) * (u : G), hconjMF0 t⟩ := by
              congr 1
        _ = action0 (QuotientGroup.mk' (H0.subgroupOf MF) t) :=
              (haction0 t).symm
    have hactiony : action0 y = (ρ i x yH : MF ⧸ H0.subgroupOf MF) := by
      rw [← haction_eq]
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) y with ⟨t, rfl⟩
      rcases hρaction i x u hux with ⟨hconjMFρ, hρ_apply⟩
      calc
        actioni (QuotientGroup.mk' (H0.subgroupOf MF) t) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (t : G) * (u : G), hconjMFi t⟩ := hactioni t
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (t : G) * (u : G), hconjMFρ t⟩ := by
              congr 1
        _ = (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) t, hy⟩ :
                MF ⧸ H0.subgroupOf MF) := (hρ_apply t hy).symm
    exact hαy.trans hactiony.symm
  refine ⟨hconjMF0, ?_⟩
  intro h
  calc
    finiteInternalProductMulAut_sec9 H
        (by
          intro _i _j _hij y z _hy _hz
          exact mul_comm y z)
        hHindep hHsup (fun i => ρ i x)
        (QuotientGroup.mk' (H0.subgroupOf MF) h) =
        α (QuotientGroup.mk' (H0.subgroupOf MF) h) := by
          rfl
    _ = action0 (QuotientGroup.mk' (H0.subgroupOf MF) h) := by
          rw [hαeq]
    _ = QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF0 h⟩ := haction0 h

private theorem finiteInternalProductMulAut_symm_eq_quotientConjAction_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C : Subgroup G}
    {q : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hqpos : 0 < q)
    (x : U ⧸ C.subgroupOf U) (u : U)
    (hux : QuotientGroup.mk' (C.subgroupOf U) u = x) :
    ∃ hconjMF : ∀ h : MF, (u : G) * (h : G) * (u : G)⁻¹ ∈ MF,
      ∀ h : MF,
        (finiteInternalProductMulAut_sec9 H
            (by
              intro _i _j _hij y z _hy _hz
              exact mul_comm y z)
            hHindep hHsup (fun i => ρ i x)).symm
          (QuotientGroup.mk' (H0.subgroupOf MF) h) =
        QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(u : G) * (h : G) * (u : G)⁻¹, hconjMF h⟩ := by
  classical
  let hcommPair : Pairwise fun i j : Fin q =>
      ∀ y z : MF ⧸ H0.subgroupOf MF, y ∈ H i → z ∈ H j → Commute y z := by
    intro _i _j _hij y z _hy _hz
    exact mul_comm y z
  let α : MulAut (MF ⧸ H0.subgroupOf MF) :=
    finiteInternalProductMulAut_sec9 H hcommPair hHindep hHsup (fun i => ρ i x)
  rcases finiteInternalProductMulAut_eq_quotientConjAction_sec9
      H hHnorm hHindep hHsup ρ hρaction hqpos x u hux with
    ⟨hconjMFminus, hα_apply⟩
  let uinv : U := ⟨(u : G)⁻¹, U.inv_mem u.property⟩
  have huinvx :
      QuotientGroup.mk' (C.subgroupOf U) uinv = x⁻¹ := by
    calc
      QuotientGroup.mk' (C.subgroupOf U) uinv =
          (QuotientGroup.mk' (C.subgroupOf U) u)⁻¹ := by rfl
      _ = x⁻¹ := by rw [hux]
  rcases finiteInternalProductMulAut_eq_quotientConjAction_sec9
      H hHnorm hHindep hHsup ρ hρaction hqpos x⁻¹ uinv huinvx with
    ⟨hconjMFplus, _hconj_apply_inv⟩
  refine ⟨?_, ?_⟩
  · intro h
    simpa [uinv, mul_assoc] using hconjMFplus h
  · intro h
    have hmem : (u : G) * (h : G) * (u : G)⁻¹ ∈ MF := by
      simpa [uinv, mul_assoc] using hconjMFplus h
    let hplus : MF := ⟨(u : G) * (h : G) * (u : G)⁻¹, hmem⟩
    have hα_hplus :
        α (QuotientGroup.mk' (H0.subgroupOf MF) hplus) =
          QuotientGroup.mk' (H0.subgroupOf MF) h := by
      calc
        α (QuotientGroup.mk' (H0.subgroupOf MF) hplus) =
            finiteInternalProductMulAut_sec9 H hcommPair hHindep hHsup (fun i => ρ i x)
              (QuotientGroup.mk' (H0.subgroupOf MF) hplus) := by
              rfl
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (hplus : G) * (u : G), hconjMFminus hplus⟩ :=
              hα_apply hplus
        _ = QuotientGroup.mk' (H0.subgroupOf MF) h := by
              congr 1
              ext
              simp [hplus, mul_assoc]
    have htarget :
        α.symm (QuotientGroup.mk' (H0.subgroupOf MF) h) =
          QuotientGroup.mk' (H0.subgroupOf MF) hplus := by
      apply α.injective
      calc
        α (α.symm (QuotientGroup.mk' (H0.subgroupOf MF) h)) =
            QuotientGroup.mk' (H0.subgroupOf MF) h := by simp
        _ = α (QuotientGroup.mk' (H0.subgroupOf MF) hplus) := hα_hplus.symm
    simpa [α, hplus] using htarget

private theorem quotient_commutator_mem_of_mk_conj_eq_self_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    {u : G}
    (hconjMF : ∀ h : MF, u⁻¹ * (h : G) * u ∈ MF)
    (hfix : ∀ h : MF,
        QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨u⁻¹ * (h : G) * u, hconjMF h⟩ =
        QuotientGroup.mk' (H0.subgroupOf MF) h) :
    ∀ h : G, h ∈ MF → ⁅u⁻¹, h⁆ ∈ H0 := by
  classical
  intro h hhMF
  let hMF : MF := ⟨h, hhMF⟩
  have hq :
      QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨u⁻¹ * (hMF : G) * u, hconjMF hMF⟩ =
        QuotientGroup.mk' (H0.subgroupOf MF) hMF :=
    hfix hMF
  have hdiv :
      (⟨u⁻¹ * (hMF : G) * u, hconjMF hMF⟩ / hMF : MF) ∈
        H0.subgroupOf MF :=
    QuotientGroup.eq_iff_div_mem.mp hq
  have hval :
      (((⟨u⁻¹ * (hMF : G) * u, hconjMF hMF⟩ / hMF : MF) : G)) =
        ⁅u⁻¹, h⁆ := by
    simp [hMF, div_eq_mul_inv, commutatorElement_def, mul_assoc]
  simpa [Subgroup.mem_subgroupOf, hval] using hdiv

private theorem mulAut_fixed_of_iSup_eq_top_sec9
    {G : Type u} [Group G]
    {ι : Sort v} (H : ι → Subgroup G)
    (hHsup : iSup H = ⊤)
    (α : MulAut G)
    (hfix : ∀ i, ∀ x : G, x ∈ H i → α x = x) :
    ∀ x : G, α x = x := by
  let K : Subgroup G :=
    { carrier := {x | α x = x}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change α (x * y) = x * y
        rw [map_mul, hx, hy]
      inv_mem' := by
        intro x hx
        change α x⁻¹ = x⁻¹
        rw [map_inv, hx] }
  have htop_le : (⊤ : Subgroup G) ≤ K := by
    rw [← hHsup]
    exact iSup_le fun i => by
      intro x hx
      exact hfix i x hx
  intro x
  exact htop_le (Subgroup.mem_top x)

private theorem rawCoordinateMulAction_quotient_eq_one_of_fixed_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHsup : iSup H = ⊤)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (x : U ⧸ C.subgroupOf U)
    (f : ULift.{u, 0} (Fin q → Fin (p - 1))) :
    letI : MulAction (U ⧸ C.subgroupOf U)
        (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    x • f = f →
      x = 1 := by
  classical
  letI : MulAction (U ⧸ C.subgroupOf U)
      (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  intro hfix
  have hρone : ∀ i, ρ i x = 1 :=
    rawCoordinateMulAction_component_eq_one_of_fixed_sec9
      p q (case_9_7_a_p_prime_sec9 hcase) H hHcard ρ x f hfix
  rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
  have hqpos : 0 < q := (case_9_7_a_q_prime_sec9 hcase).pos
  let i0 : Fin q := ⟨0, hqpos⟩
  rcases hHnorm i0 u with ⟨hconjMF0, action0, haction0, _hmap0⟩
  have haction0_fix :
      ∀ y : MF ⧸ H0.subgroupOf MF, action0 y = y := by
    apply mulAut_fixed_of_iSup_eq_top_sec9 H hHsup action0
    intro i y hy
    rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) y with ⟨h, rfl⟩
    rcases hHnorm i u with ⟨hconjMFi, actioni, hactioni, _hmapi⟩
    have haction_eq : actioni = action0 := by
      ext z
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) z with ⟨t, rfl⟩
      calc
        actioni (QuotientGroup.mk' (H0.subgroupOf MF) t) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (t : G) * (u : G), hconjMFi t⟩ := hactioni t
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (t : G) * (u : G), hconjMF0 t⟩ := by
              congr 1
        _ = action0 (QuotientGroup.mk' (H0.subgroupOf MF) t) :=
              (haction0 t).symm
    have hactioni_fix :
        actioni (QuotientGroup.mk' (H0.subgroupOf MF) h) =
          QuotientGroup.mk' (H0.subgroupOf MF) h := by
      rcases hρaction i (QuotientGroup.mk' (C.subgroupOf U) u) u rfl with
        ⟨hconjMFρ, hρ_apply⟩
      calc
        actioni (QuotientGroup.mk' (H0.subgroupOf MF) h) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMFi h⟩ := hactioni h
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMFρ h⟩ := by
              congr 1
        _ = (ρ i (QuotientGroup.mk' (C.subgroupOf U) u)
              ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hy⟩ :
                MF ⧸ H0.subgroupOf MF) := (hρ_apply h hy).symm
        _ = ((1 : MulAut (H i))
              ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hy⟩ :
                MF ⧸ H0.subgroupOf MF) := by
              have hρid :=
                congrFun (congrArg DFunLike.coe (hρone i))
                  ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hy⟩
              exact congrArg Subtype.val hρid
        _ = QuotientGroup.mk' (H0.subgroupOf MF) h := rfl
    simpa [haction_eq] using hactioni_fix
  have huInvC : (u : G)⁻¹ ∈ C := by
    have huInvU : (u : G)⁻¹ ∈ U := by
      exact U.inv_mem u.property
    rw [(case_9_7_a_quotientCentralizerIn_sec9 hcase).2 ((u : G)⁻¹) huInvU]
    intro h hhMF
    have hfix_mk : ∀ z : MF,
        QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(u : G)⁻¹ * (z : G) * (u : G), hconjMF0 z⟩ =
          QuotientGroup.mk' (H0.subgroupOf MF) z := by
      intro z
      exact (haction0 z).symm.trans
        (haction0_fix (QuotientGroup.mk' (H0.subgroupOf MF) z))
    exact quotient_commutator_mem_of_mk_conj_eq_self_sec9 hconjMF0 hfix_mk h hhMF
  have huC : (u : G) ∈ C := by
    simpa using C.inv_mem huInvC
  exact (QuotientGroup.eq_one_iff (N := C.subgroupOf U) (x := u)).2
    (by simpa [Subgroup.mem_subgroupOf] using huC)

private theorem rawCoordinateMulAction_stabilizer_eq_bot_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHsup : iSup H = ⊤)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩) :
    letI : MulAction (U ⧸ C.subgroupOf U)
        (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    ∀ k : ULift.{u, 0} (Fin q → Fin (p - 1)),
      MulAction.stabilizer (U ⧸ C.subgroupOf U) k = ⊥ := by
  classical
  letI : MulAction (U ⧸ C.subgroupOf U)
      (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  intro k
  ext x
  constructor
  · intro hx
    rw [MulAction.mem_stabilizer_iff] at hx
    have hxone :
        x = (1 : U ⧸ C.subgroupOf U) :=
      rawCoordinateMulAction_quotient_eq_one_of_fixed_sec9
        hcase H hHcard hHnorm hHsup ρ hρaction x k hx
    rw [hxone]
    exact Subgroup.mem_bot.2 rfl
  · intro hx
    have hxone : x = (1 : U ⧸ C.subgroupOf U) := by
      simpa using (Subgroup.mem_bot.mp hx)
    rw [MulAction.mem_stabilizer_iff, hxone, one_smul]


private def H0COrderedComponentCharacterFamilyData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U W1 H0 C : Subgroup G)
    (p q : ℕ) : Prop :=
  theorem_9_7_orderedCaseAComponentTransitionData_sec9 MF H0 U W1 C p q


private def H0COrderedXmuCoordinateData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U W1 H0 C : Subgroup G)
    (q aρ : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
  (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i)) : Prop :=
  ∃ hW1normU : W1 ≤ Subgroup.normalizer (U : Set G),
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    ∃ w0 : W1,
      Subgroup.zpowers w0 = ⊤ ∧
        ∃ hqpos : 0 < q,
          (∀ i : Fin q,
            quotientSubgroupConjugateByElement MF H0
              (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G)) ∧
            ∃ χbar : Fin q → (U ⧸ C.subgroupOf U) →*
                Multiplicative (ZMod aρ),
              (∀ i, ∀ x y : U ⧸ C.subgroupOf U,
                χbar i x = χbar i y → ρ i x = ρ i y) ∧
                ∀ x : U,
                  ∀ i,
                    χbar i (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) =
                      χbar (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
                        (QuotientGroup.mk' (C.subgroupOf U) x)

private theorem H0COrderedXmuCoordinateData_of_ordered_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U W1 H0 C : Subgroup G)
    (p q : ℕ) :
    H0COrderedComponentCharacterFamilyData_sec9 MF U W1 H0 C p q →
      ∃ aρ : ℕ,
        ∃ hnormalH0 : (H0.subgroupOf MF).Normal,
          letI : (H0.subgroupOf MF).Normal := hnormalH0
          ∃ hnormalC : (C.subgroupOf U).Normal,
            letI : (C.subgroupOf U).Normal := hnormalC
            ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
              ∃ _hHcard : ∀ i, Nat.card (H i) = p,
                (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                  iSupIndep H ∧
                  iSup H = ⊤ ∧
                  (∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) aρ) ∧
                  (∃ hqpos : 0 < q,
                    ∀ i : Fin q,
                      ∃ w : W1,
                        quotientSubgroupConjugateByElement MF H0
                          (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                  ∃ ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i),
                    (∀ i, IsCyclic (ρ i).range) ∧
                      (∀ i, Nat.card (ρ i).range = aρ) ∧
                      (∀ i, ∀ x : U ⧸ C.subgroupOf U,
                        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
                          ∃ hconjMF : ∀ h : MF,
                            (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
                            ∀ h : MF,
                            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
                              (ρ i x
                                ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                                  MF ⧸ H0.subgroupOf MF) =
                                QuotientGroup.mk' (H0.subgroupOf MF)
                                  ⟨(u : G)⁻¹ * (h : G) * (u : G),
                                    hconjMF h⟩) ∧
                      (∀ i, ∀ x : U ⧸ C.subgroupOf U,
                        ρ i x = 1 ↔
                          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
                            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G)) ∧
                      H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ := by
  classical
  intro hordered
  rcases hordered with
    ⟨aρ, hnormalH0, hW1normU, hnormalC, w0, hw0gen, H, hHcard, hHnorm,
      hHindep, hHsup, hfac, hqpos, hsucc, χbar, hχdata, hχtransition⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  choose ρ hρ using hχdata
  have hρcyc : ∀ i, IsCyclic (ρ i).range := fun i => (hρ i).1
  have hρcard : ∀ i, Nat.card (ρ i).range = aρ := fun i => (hρ i).2.1
  have hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩ :=
    fun i => (hρ i).2.2.1
  have hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G) :=
    fun i => (hρ i).2.2.2.1
  have hρsep :
      ∀ i, ∀ x y : U ⧸ C.subgroupOf U,
        χbar i x = χbar i y → ρ i x = ρ i y :=
    fun i => (hρ i).2.2.2.2
  have hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩)
            (H i) (w : G) :=
    ⟨hqpos,
      theorem_9_7_weak_orbit_of_successor_conjugates_sec9
        (MF := MF) (H0 := H0) (W1 := W1) hqpos H w0 hsucc⟩
  have horderedXmu :
      H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ :=
    ⟨hW1normU, w0, hw0gen, hqpos, hsucc, χbar, hρsep, hχtransition⟩
  exact
    ⟨aρ, hnormalH0, hnormalC, H, hHcard, hHnorm, hHindep, hHsup, hfac,
      hconj, ρ, hρcyc, hρcard, hρaction, hρker, horderedXmu⟩

private abbrev H0CLinearCandidateXthetaRawIndex_sec9 (p q : ℕ) : Type u :=
  ULift.{u, 0} (Fin q → Fin (p - 1))

private abbrev H0CLinearCandidateXmuRawIndex_sec9 (p : ℕ) : Type :=
  Fin (p - 1)


private theorem quotientSubgroupConjugateByElement_mulEquiv_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)} {g : G}
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R g) :
    ∃ e : Q ≃* R,
      ∃ hconjMF : ∀ h : MF, g⁻¹ * (h : G) * g ∈ MF,
        ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ Q,
          (e ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
              MF ⧸ H0.subgroupOf MF) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨g⁻¹ * (h : G) * g, hconjMF h⟩ := by
  classical
  rcases hQR with ⟨hconjMF, action, haction, hR⟩
  let e0 : Q ≃* Q.map action.toMonoidHom := action.subgroupMap Q
  let e : Q ≃* R := e0.trans (MulEquiv.subgroupCongr hR.symm)
  refine ⟨e, hconjMF, ?_⟩
  intro h hhQ
  change action (QuotientGroup.mk' (H0.subgroupOf MF) h) =
    QuotientGroup.mk' (H0.subgroupOf MF) ⟨g⁻¹ * (h : G) * g, hconjMF h⟩
  exact haction h

private theorem conj_inv_mem_of_conj_mem_finite_sec9
    {G : Type u} [Group G] [Finite G]
    {MF : Subgroup G} {g : G}
    (hconjMF : ∀ h : MF, g⁻¹ * (h : G) * g ∈ MF) :
    ∀ h : MF, g * (h : G) * g⁻¹ ∈ MF := by
  classical
  letI : Fintype MF := Fintype.ofFinite MF
  let f : MF → MF := fun h => ⟨g⁻¹ * (h : G) * g, hconjMF h⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hval := congrArg Subtype.val hxy
    dsimp [f] at hval
    calc
      (x : G) = g * (g⁻¹ * (x : G) * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * (y : G) * g) * g⁻¹ := by rw [hval]
      _ = (y : G) := by group
  have hf_surj : Function.Surjective f := by
    exact (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, rfl⟩ |>.2
  intro h
  rcases hf_surj h with ⟨k, hk⟩
  have hkval := congrArg Subtype.val hk
  dsimp [f] at hkval
  have hk_eq : (k : G) = g * (h : G) * g⁻¹ := by
    calc
      (k : G) = g * (g⁻¹ * (k : G) * g) * g⁻¹ := by group
      _ = g * (h : G) * g⁻¹ := by rw [hkval]
  simpa [hk_eq] using k.property

private theorem quotientSubgroupConjugateByElement_action_symm_apply_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)} {g : G}
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R g) :
    ∃ hconjMF : ∀ h : MF, g⁻¹ * (h : G) * g ∈ MF,
      ∃ action : MulAut (MF ⧸ H0.subgroupOf MF),
        (∀ h : MF,
          action (QuotientGroup.mk' (H0.subgroupOf MF) h) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨g⁻¹ * (h : G) * g, hconjMF h⟩) ∧
          R = Q.map action.toMonoidHom ∧
          ∃ hconjInvMF : ∀ h : MF, g * (h : G) * g⁻¹ ∈ MF,
            ∀ h : MF,
              action.symm (QuotientGroup.mk' (H0.subgroupOf MF) h) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨g * (h : G) * g⁻¹, hconjInvMF h⟩ := by
  classical
  rcases hQR with ⟨hconjMF, action, haction, hR⟩
  have hconjInvMF : ∀ h : MF, g * (h : G) * g⁻¹ ∈ MF :=
    conj_inv_mem_of_conj_mem_finite_sec9 hconjMF
  refine ⟨hconjMF, action, haction, hR, hconjInvMF, ?_⟩
  intro h
  apply action.injective
  simp only [MulEquiv.apply_symm_apply]
  symm
  calc
    action (QuotientGroup.mk' (H0.subgroupOf MF)
        ⟨g * (h : G) * g⁻¹, hconjInvMF h⟩) =
        QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨g⁻¹ * (g * (h : G) * g⁻¹) * g,
            hconjMF ⟨g * (h : G) * g⁻¹, hconjInvMF h⟩⟩ := haction _
    _ = QuotientGroup.mk' (H0.subgroupOf MF) h := by
        apply congrArg (QuotientGroup.mk' (H0.subgroupOf MF))
        apply Subtype.ext
        group

private theorem quotientSubgroupConjugateByElement_symm_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)} {g : G}
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R g) :
    quotientSubgroupConjugateByElement MF H0 R Q g⁻¹ := by
  classical
  rcases hQR with ⟨hconjMF, action, haction, hR⟩
  have hconjInvMF : ∀ h : MF, g * (h : G) * g⁻¹ ∈ MF :=
    conj_inv_mem_of_conj_mem_finite_sec9 hconjMF
  refine ⟨?_, action.symm, ?_, ?_⟩
  · intro h
    simpa only [inv_inv] using hconjInvMF h
  · intro h
    apply action.injective
    simp only [MulEquiv.apply_symm_apply]
    symm
    calc
      action (QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(g⁻¹)⁻¹ * (h : G) * g⁻¹, by
            simpa only [inv_inv] using hconjInvMF h⟩) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨g⁻¹ * ((g⁻¹)⁻¹ * (h : G) * g⁻¹) * g,
              hconjMF ⟨(g⁻¹)⁻¹ * (h : G) * g⁻¹, by
                simpa only [inv_inv] using hconjInvMF h⟩⟩ :=
        haction _
      _ = QuotientGroup.mk' (H0.subgroupOf MF) h := by
        apply congrArg (QuotientGroup.mk' (H0.subgroupOf MF))
        apply Subtype.ext
        group
  · ext x
    constructor
    · intro hxQ
      refine ⟨action x, ?_, by simp⟩
      rw [hR]
      exact ⟨x, hxQ, rfl⟩
    · rintro ⟨y, hyR, hyx⟩
      rw [hR] at hyR
      rcases hyR with ⟨z, hzQ, rfl⟩
      have hzx : z = x := by
        simpa using congrArg action hyx
      simpa [← hzx] using hzQ

private theorem quotientSubgroupConjugateByElement_one_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF)) :
    quotientSubgroupConjugateByElement MF H0 Q Q (1 : G) := by
  refine ⟨?_, 1, ?_, ?_⟩
  · intro h
    simp
  · intro h
    simp
  · ext x
    simp [Subgroup.mem_map]

private theorem quotientSubgroupConjugateByElement_trans_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q R S : Subgroup (MF ⧸ H0.subgroupOf MF)} {g h : G}
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R g)
    (hRS : quotientSubgroupConjugateByElement MF H0 R S h) :
    quotientSubgroupConjugateByElement MF H0 Q S (g * h) := by
  rcases hQR with ⟨hconjG, actionG, hactionG, hR⟩
  rcases hRS with ⟨hconjH, actionH, hactionH, hS⟩
  let hconjGH : ∀ k : MF, (g * h)⁻¹ * (k : G) * (g * h) ∈ MF := by
    intro k
    have hmem := hconjH ⟨g⁻¹ * (k : G) * g, hconjG k⟩
    simpa [mul_assoc] using hmem
  refine ⟨hconjGH, actionG.trans actionH, ?_, ?_⟩
  · intro k
    calc
      (actionG.trans actionH) (QuotientGroup.mk' (H0.subgroupOf MF) k) =
          actionH (actionG (QuotientGroup.mk' (H0.subgroupOf MF) k)) := rfl
      _ = actionH (QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨g⁻¹ * (k : G) * g, hconjG k⟩) := by
          rw [hactionG k]
      _ = QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨h⁻¹ * (g⁻¹ * (k : G) * g) * h,
              hconjH ⟨g⁻¹ * (k : G) * g, hconjG k⟩⟩ := by
          exact hactionH ⟨g⁻¹ * (k : G) * g, hconjG k⟩
      _ = QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(g * h)⁻¹ * (k : G) * (g * h), hconjGH k⟩ := by
          congr 1
          apply Subtype.ext
          group
  · calc
      S = R.map actionH.toMonoidHom := hS
      _ = (Q.map actionG.toMonoidHom).map actionH.toMonoidHom := by rw [hR]
      _ = Q.map (actionG.trans actionH).toMonoidHom := by
          rw [Subgroup.map_map]
          rfl

private theorem quotientSubgroupConjugateByElement_target_eq_of_same_element_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q R S : Subgroup (MF ⧸ H0.subgroupOf MF)} {g : G}
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R g)
    (hQS : quotientSubgroupConjugateByElement MF H0 Q S g) :
    R = S := by
  rcases hQR with ⟨hconjMF_R, actionR, hactionR, hR⟩
  rcases hQS with ⟨hconjMF_S, actionS, hactionS, hS⟩
  have haction : actionR = actionS := by
    ext x
    rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨m, rfl⟩
    calc
      actionR (QuotientGroup.mk' (H0.subgroupOf MF) m) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨g⁻¹ * (m : G) * g, hconjMF_R m⟩ := hactionR m
      _ = QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨g⁻¹ * (m : G) * g, hconjMF_S m⟩ := by
            congr 1
      _ = actionS (QuotientGroup.mk' (H0.subgroupOf MF) m) := (hactionS m).symm
  calc
    R = Q.map actionR.toMonoidHom := hR
    _ = Q.map actionS.toMonoidHom := by rw [haction]
    _ = S := hS.symm

private theorem quotientSubgroupNormalizedBy_of_generator_conjugates_self_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W1 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hw0Q : quotientSubgroupConjugateByElement MF H0 Q Q (w0 : G)) :
    quotientSubgroupNormalizedBy MF H0 W1 Q := by
  let N : Subgroup W1 :=
    { carrier := {w | quotientSubgroupConjugateByElement MF H0 Q Q (w : G)}
      one_mem' := by
        simpa using
          quotientSubgroupConjugateByElement_one_sec9
            (MF := MF) (H0 := H0) (Q := Q)
      mul_mem' := by
        intro a b ha hb
        simpa using
          quotientSubgroupConjugateByElement_trans_sec9 ha hb
      inv_mem' := by
        intro a ha
        simpa using
          quotientSubgroupConjugateByElement_symm_sec9 ha }
  intro w
  have hw0N : w0 ∈ N := by
    simpa [N] using hw0Q
  have hwmem : w ∈ Subgroup.zpowers w0 := by
    rw [hw0gen]
    exact Subgroup.mem_top w
  have hwN : w ∈ N :=
    (Subgroup.zpowers_le_of_mem hw0N) hwmem
  simpa [N] using hwN

private theorem subgroup_ne_bot_of_prime_card_sec9
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} (hp : Nat.Prime p)
    (Q : Subgroup G) (hQcard : Nat.card Q = p) :
    Q ≠ ⊥ := by
  intro hQbot
  have hcard : Nat.card Q = 1 := by
    rw [hQbot]
    exact Subgroup.card_bot
  exact hp.ne_one (hQcard.symm.trans hcard)

private theorem iSupIndep_subgroups_injective_of_prime_card_sec9
    {G : Type u} [Group G] [Finite G]
    {ι : Type v} [DecidableEq ι]
    {p : ℕ} (hp : Nat.Prime p)
    (H : ι → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H) :
    Function.Injective H := by
  intro i j hij
  by_contra hne
  have hji : j ≠ i := by
    intro hji
    exact hne hji.symm
  have hleRest : H j ≤ (⨆ k, ⨆ _ : k ≠ i, H k) := by
    exact le_iSup_of_le j (le_iSup_of_le hji le_rfl)
  have hmeet : H i ⊓ H j = ⊥ := by
    have hdisj := (iSupIndep_def.mp hHindep i)
    apply le_bot_iff.mp
    calc
      H i ⊓ H j ≤ H i ⊓ (⨆ k, ⨆ _ : k ≠ i, H k) :=
        inf_le_inf_left _ hleRest
      _ = ⊥ := disjoint_iff.mp hdisj
  have hHi_bot : H i = ⊥ := by
    calc
      H i = H i ⊓ H j := by rw [hij, inf_idem]
      _ = ⊥ := hmeet
  exact subgroup_ne_bot_of_prime_card_sec9 hp (H i) (hHcard i) hHi_bot

private theorem theorem_9_8_base_not_W1_normalized_of_case_a_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a) :
    ¬ quotientSubgroupNormalizedBy MF H0 W1 (H ⟨0, hqpos⟩) := by
  classical
  rcases hcase with
    ⟨h92, _hH0MF, _hC, hpprime, hqprime, hpDataFull, _hdecomp,
      hquotCard, _hadiv, _hbarU⟩
  rcases hpDataFull with ⟨hp, _hp_eq, hpData, h96⟩
  let Q : Subgroup (MF ⧸ H0.subgroupOf MF) := H ⟨0, hqpos⟩
  have hQnormU : quotientSubgroupNormalizedBy MF H0 U Q := by
    dsimp [Q]
    exact hHnorm ⟨0, hqpos⟩
  have hQneBot : Q ≠ ⊥ := by
    exact subgroup_ne_bot_of_prime_card_sec9 hpprime Q (by
      simpa [Q] using hHcard ⟨0, hqpos⟩)
  have hQneTop : Q ≠ ⊤ := by
    intro hQtop
    have hcardTop : Nat.card Q = Nat.card (MF ⧸ H0.subgroupOf MF) := by
      calc
        Nat.card Q = Nat.card (⊤ : Subgroup (MF ⧸ H0.subgroupOf MF)) := by
          rw [hQtop]
        _ = Nat.card (MF ⧸ H0.subgroupOf MF) := Subgroup.card_top
    have hp_eq_pow : p = p ^ q := by
      rw [show Nat.card Q = p by simpa [Q] using hHcard ⟨0, hqpos⟩,
        hquotCard] at hcardTop
      exact hcardTop
    have hpow_gt : p < p ^ q := by
      simpa using Nat.pow_lt_pow_right hpprime.one_lt hqprime.one_lt
    exact (Nat.ne_of_lt hpow_gt) hp_eq_pow
  exact
    quotientSubgroup_not_W1_normalized_of_proper_U_normalized_quotientChiefFactorData_sec9
      M MF U W1 W2 H0 q hp
      h92 hpData h96 hnormalH0
      Q hQnormU hQneBot hQneTop

private theorem theorem_9_8_weak_orbit_nonidentity_moves_base_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a) :
    ∀ w : W1, w ≠ 1 →
      ∃ i : Fin q, i ≠ ⟨0, hqpos⟩ ∧
        quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
          (w : G) := by
  classical
  intro w hwne
  let base : Fin q := ⟨0, hqpos⟩
  have hpprime : Nat.Prime p := case_9_7_a_p_prime_sec9 hcase
  have hHinj : Function.Injective H :=
    iSupIndep_subgroups_injective_of_prime_card_sec9 hpprime H hHcard hHindep
  let v : Fin q → W1 := fun i => Classical.choose (hconjBase i)
  have hv : ∀ i : Fin q,
      quotientSubgroupConjugateByElement MF H0 (H base) (H i) (v i : G) := by
    intro i
    exact Classical.choose_spec (hconjBase i)
  have hvinj : Function.Injective v := by
    intro i j hij
    apply hHinj
    exact quotientSubgroupConjugateByElement_target_eq_of_same_element_sec9
      (hv i) (by simpa [v, hij] using hv j)
  letI : Fintype W1 := Fintype.ofFinite W1
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  have hcard_v : Fintype.card (Fin q) = Fintype.card W1 := by
    calc
      Fintype.card (Fin q) = q := Fintype.card_fin q
      _ = Nat.card W1 := h92.q_eq.symm
      _ = Fintype.card W1 := Nat.card_eq_fintype_card
  have hvsurj : Function.Surjective v := by
    letI : DecidableEq W1 := Classical.decEq W1
    by_contra hnot
    rw [Function.Surjective] at hnot
    push Not at hnot
    rcases hnot with ⟨w0, hw0⟩
    have hw0not : w0 ∉ (Finset.univ : Finset (Fin q)).image v := by
      intro hwmem
      rcases Finset.mem_image.mp hwmem with ⟨i, _hi, hiw⟩
      exact hw0 i hiw
    have hproper :
        (Finset.univ : Finset (Fin q)).image v ⊂ (Finset.univ : Finset W1) := by
      refine ⟨Finset.subset_univ _, ?_⟩
      intro hEq
      exact hw0not (hEq (Finset.mem_univ w0))
    have hlt :
        ((Finset.univ : Finset (Fin q)).image v).card <
          (Finset.univ : Finset W1).card :=
      Finset.card_lt_card hproper
    have himage :
        ((Finset.univ : Finset (Fin q)).image v).card = Fintype.card (Fin q) :=
      Finset.card_image_of_injective (Finset.univ : Finset (Fin q)) hvinj
    have huniv :
        (Finset.univ : Finset W1).card = Fintype.card W1 :=
      Finset.card_univ
    omega
  rcases hvsurj w with ⟨i, hiw⟩
  have hine : i ≠ base := by
    intro hibase
    have hself :
        quotientSubgroupConjugateByElement MF H0 (H base) (H base) (w : G) := by
      simpa [base, hibase, hiw.symm] using hv i
    have hW1prime : Nat.Prime (Nat.card W1) := by
      rw [h92.q_eq]
      exact case_9_7_a_q_prime_sec9 hcase
    have hwgen : Subgroup.zpowers w = ⊤ :=
      zpowers_eq_top_of_prime_card_of_ne_one hW1prime hwne
    exact
      theorem_9_8_base_not_W1_normalized_of_case_a_sec9
        H hqpos hHcard hHnorm hcase
        (quotientSubgroupNormalizedBy_of_generator_conjugates_self_sec9
          w hwgen hself)
  exact ⟨i, by simpa [base] using hine, by simpa [hiw.symm, base] using hv i⟩

private noncomputable def H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (base : Fin q)
    (E : ∀ j : Fin q, H base ≃* H j)
    (i : H0CLinearCandidateXmuRawIndex_sec9 p) :
    H0CLinearCandidateXthetaRawIndex_sec9.{u} p q :=
  ULift.up fun j =>
    (nonprincipalLinearCharacterEquivFin_sec9 (H j) p (hHcard j)).symm
      ⟨((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
          (hHcard base)) i).1.comp (E j).symm.toMonoidHom, by
        intro htriv
        exact ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
          (hHcard base)) i).2 <| by
          ext x
          have hval := congrArg
            (fun χ : H j →* ℂˣ => χ ((E j) x)) htriv
          simpa [MonoidHom.comp_apply] using hval⟩

private theorem H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_component_spec_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (base : Fin q)
    (E : ∀ j : Fin q, H base ≃* H j)
    (i : H0CLinearCandidateXmuRawIndex_sec9 p)
    (j : Fin q) :
    ((nonprincipalLinearCharacterEquivFin_sec9 (H j) p (hHcard j))
        ((H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
          p q H hHcard base E i).down j)).1 =
      ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
          (hHcard base)) i).1.comp (E j).symm.toMonoidHom := by
  simp [H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9]

private theorem H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_injective_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (base : Fin q)
    (E : ∀ j : Fin q, H base ≃* H j) :
    Function.Injective
      (H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
        p q H hHcard base E) := by
  intro i j hij
  let ebase := nonprincipalLinearCharacterEquivFin_sec9 (H base) p (hHcard base)
  have hcoord :
      (H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
        p q H hHcard base E i).down base =
      (H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
        p q H hHcard base E j).down base := by
    exact congrArg (fun f : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q =>
      f.down base) hij
  have hcomp :
      (ebase i).1.comp (E base).symm.toMonoidHom =
        (ebase j).1.comp (E base).symm.toMonoidHom := by
    have hcoordChar := congrArg
      (nonprincipalLinearCharacterEquivFin_sec9 (H base) p (hHcard base)) hcoord
    have hval := congrArg
      (fun χ : {χ : H base →* ℂˣ // χ ≠ 1} => χ.1) hcoordChar
    simpa [ebase,
      H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_component_spec_sec9]
      using hval
  have hbaseChar : ebase i = ebase j := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    have hval := congrArg (fun χ : H base →* ℂˣ => χ ((E base) x)) hcomp
    simpa [MonoidHom.comp_apply] using hval
  exact ebase.injective hbaseChar

private theorem H0CLinearCandidateXmuRawIndex_card_sec9 (p : ℕ) :
    Fintype.card (H0CLinearCandidateXmuRawIndex_sec9 p) = p - 1 := by
  simp [H0CLinearCandidateXmuRawIndex_sec9]


private def H0CLinearCandidateXmuTransportedRawCoordinateOfConjData_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (p q : ℕ)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) : Prop :=
  ∃ hqpos : 0 < q,
    let base : Fin q := ⟨0, hqpos⟩
    ∃ w : ∀ _j : Fin q, W,
      ∃ _hw : ∀ j : Fin q,
        quotientSubgroupConjugateByElement MF H0 (H base) (H j) (w j : G),
        ∃ E : ∀ j : Fin q, H base ≃* H j,
          (∀ j : Fin q,
            ∃ hconjMF : ∀ h : MF, (w j : G)⁻¹ * (h : G) * (w j : G) ∈ MF,
              ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H base,
                (E j ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                    MF ⧸ H0.subgroupOf MF) =
                  QuotientGroup.mk' (H0.subgroupOf MF)
                    ⟨(w j : G)⁻¹ * (h : G) * (w j : G), hconjMF h⟩) ∧
            μraw =
              H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
                p q H hHcard base E


private def H0CLinearCandidateXmuOrderedTransportedRawCoordinateData_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W1 : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (p q : ℕ)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (w0 : W1)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) : Prop :=
  ∃ hqpos : 0 < q,
    let base : Fin q := ⟨0, hqpos⟩
    ∃ _hw : ∀ j : Fin q,
      quotientSubgroupConjugateByElement MF H0 (H base) (H j)
        ((w0 ^ j.1 : W1) : G),
      ∃ E : ∀ j : Fin q, H base ≃* H j,
        (∀ j : Fin q,
          ∃ hconjMF : ∀ h : MF,
            (((w0 ^ j.1 : W1) : G))⁻¹ * (h : G) *
                (((w0 ^ j.1 : W1) : G)) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H base,
              (E j ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(((w0 ^ j.1 : W1) : G))⁻¹ * (h : G) *
                      (((w0 ^ j.1 : W1) : G)), hconjMF h⟩) ∧
          μraw =
            H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
              p q H hHcard base E

private theorem
    H0CLinearCandidateXmuOrderedTransportedRawCoordinate_data_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W1 : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (p q : ℕ)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (w0 : W1)
    (hqpos : 0 < q)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G)) :
    ∃ μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
        H0CLinearCandidateXthetaRawIndex_sec9.{u} p q,
      H0CLinearCandidateXmuOrderedTransportedRawCoordinateData_sec9
        (MF := MF) (H0 := H0) (W1 := W1) p q H hHcard w0 μraw ∧
        H0CLinearCandidateXmuTransportedRawCoordinateOfConjData_sec9
          (MF := MF) (H0 := H0) (W := W1) p q H hHcard μraw ∧
        Function.Injective μraw := by
  classical
  let base : Fin q := ⟨0, hqpos⟩
  have hw : ∀ j : Fin q,
      quotientSubgroupConjugateByElement MF H0 (H base) (H j)
        ((w0 ^ j.1 : W1) : G) := by
    intro j
    simpa [base] using
      theorem_9_7_successor_conjugates_pow_sec9 hqpos H w0 hsucc j.1 j.2
  choose E hE using fun j =>
    quotientSubgroupConjugateByElement_mulEquiv_sec9 (hw j)
  let μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q :=
    H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
      p q H hHcard base E
  refine ⟨μraw, ?_, ?_, ?_⟩
  · refine ⟨hqpos, hw, E, ?_, rfl⟩
    intro j
    simpa using hE j
  · let w : ∀ j : Fin q, W1 := fun j => w0 ^ j.1
    refine ⟨hqpos, w, ?_, E, ?_, rfl⟩
    · intro j
      exact hw j
    · intro j
      simpa [w] using hE j
  · exact
      H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_injective_sec9
        p q H hHcard base E

private def H0CLinearCandidateXmuOrderedTransportedRawActionData_sec9
    {G : Type u} [Group G] [Finite G]
    {MF U W1 H0 C : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (p q aρ : ℕ)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) : Prop :=
  ∃ hW1normU : W1 ≤ Subgroup.normalizer (U : Set G),
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    ∃ w0 : W1,
      Subgroup.zpowers w0 = ⊤ ∧
        H0CLinearCandidateXmuOrderedTransportedRawCoordinateData_sec9
          (MF := MF) (H0 := H0) (W1 := W1) p q H hHcard w0 μraw ∧
        ∃ hqpos : 0 < q,
          (∀ i : Fin q,
            quotientSubgroupConjugateByElement MF H0
              (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G)) ∧
            ∃ χbar : Fin q → (U ⧸ C.subgroupOf U) →*
                Multiplicative (ZMod aρ),
              (∀ i, ∀ x y : U ⧸ C.subgroupOf U,
                χbar i x = χbar i y → ρ i x = ρ i y) ∧
                ∀ x : U,
                  ∀ i,
                    χbar i (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) =
                      χbar (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
                        (QuotientGroup.mk' (C.subgroupOf U) x)


private theorem H0CLinearCandidateXmu_image_card_of_injective_withRaw_sec9
    (p : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι) :
    Function.Injective μorbit →
      (Finset.univ.image μorbit).card = p - 1 := by
  intro hinj
  rw [Finset.card_image_of_injective _ hinj]
  exact H0CLinearCandidateXmuRawIndex_card_sec9 p


private def H0CLinearCandidateXmuConcreteFinalImageDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M _MF _H0 _C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) : Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  Function.Injective μorbit ∧
    (∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      Section1.inducedCF Dm (θ (μorbit i)) ∈
        reducibleCharacterFilter_sec9 M SH0C) ∧
    (∀ χ : Section1.ClassFunction M,
      χ ∈ reducibleCharacterFilter_sec9 M SH0C →
        ∃ i : H0CLinearCandidateXmuRawIndex_sec9 p,
          χ = Section1.inducedCF Dm (θ (μorbit i))) ∧
    ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      ∀ j : ι, j ∉ Finset.univ.image μorbit →
        Section1.inducedCF Dm (θ (μorbit i)) ≠ Section1.inducedCF Dm (θ j)

private def H0CLinearCandidateXmuFinalSeparationDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M _MF _H0 _C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) : Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  Function.Injective μfinal ∧
    (∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      μfinal i ∈ reducibleCharacterFilter_sec9 M SH0C) ∧
    ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      ∀ j : ι,
        μfinal i = Section1.inducedCF Dm (θ j) →
          j ∈ Finset.univ.image μorbit

private def H0CLinearCandidateXmuSmuDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M _MF _H0 _C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) : Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  Function.Injective μfinal ∧
    (∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      μfinal i ∈ reducibleCharacterFilter_sec9 M SH0C) ∧
      ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
        ∀ j : ι,
          μfinal i = Section1.inducedCF Dm (θ j) →
            j ∈ Finset.univ.image μorbit

private def H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (p : ℕ)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  Function.Injective μfinal

private def H0CLinearCandidateXmuSmuCoreDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M _MF _H0 _C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) : Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  Function.Injective μfinal ∧
    (∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      Section1.inertiaSubgroup Dm (θ (μorbit i)) = ⊤) ∧
    (∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      μfinal i ∈ reducibleCharacterFilter_sec9 M SH0C) ∧
    ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      ∀ j : ι,
        μfinal i = Section1.inducedCF Dm (θ j) →
          j ∈ Finset.univ.image μorbit

private def H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  Function.Injective θ ∧
    (∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      Section1.inertiaSubgroup Dm (θ (μorbit i)) = ⊤) ∧
    ∀ i : ι,
      Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
        ¬ Section1.subgroupInKernel' (θ i)
          ((MF.subgroupOf M).subgroupOf Dm) ∧
        Section1.subgroupInKernel' (θ i)
          (((H0 ⊔ C).subgroupOf M).subgroupOf Dm)

private def H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M _MF _H0 _C : Subgroup G)
    (p : ℕ)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
    Section1.inertiaSubgroup Dm (θ (μorbit i)) = ⊤

private def H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M W1 : Subgroup G)
    (p : ℕ)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
    W1.subgroupOf M ≤ Section1.inertiaSubgroup Dm (θ (μorbit i))


private theorem inertiaSubgroup_eq_top_of_isComplement'_le_sec9
    {G : Type u} [Group G]
    (H W : Subgroup G) [H.Normal]
    (θ : Section1.ClassFunction H)
    (hθ : Section1.IsClassFunction θ)
    (hcomp : H.IsComplement' W)
    (hW : W ≤ Section1.inertiaSubgroup H θ) :
    Section1.inertiaSubgroup H θ = ⊤ := by
  apply le_antisymm le_top
  intro g _hg
  rcases hcomp.2 g with ⟨⟨h, w⟩, hgw⟩
  have hHleI : H ≤ Section1.inertiaSubgroup H θ :=
    Section1.proposition_1_7_inertia_contains_H H θ hθ
  have hhI : (h : G) ∈ Section1.inertiaSubgroup H θ :=
    hHleI h.property
  have hwI : (w : G) ∈ Section1.inertiaSubgroup H θ :=
    hW w.property
  have hmulI : (h : G) * (w : G) ∈ Section1.inertiaSubgroup H θ :=
    (Section1.inertiaSubgroup H θ).mul_mem hhI hwI
  simpa [hgw] using hmulI

private theorem subgroupOf_le_inertiaSubgroup_of_zpowers_generator_mem_sec9
    {G : Type u} [Group G]
    {M W1 : Subgroup G}
    (H : Subgroup M) [H.Normal]
    (θ : Section1.ClassFunction H)
    (w0 : W1)
    (hW1M : W1 ≤ M)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hw0I : (⟨(w0 : G), hW1M w0.property⟩ : M) ∈
      Section1.inertiaSubgroup H θ) :
    W1.subgroupOf M ≤ Section1.inertiaSubgroup H θ := by
  let f : W1 →* M :=
    { toFun := fun w => ⟨(w : G), hW1M w.property⟩
      map_one' := by
        ext
        rfl
      map_mul' := by
        intro x y
        ext
        rfl }
  have hw0pre :
      w0 ∈ (Section1.inertiaSubgroup H θ).comap f := by
    simpa [f] using hw0I
  have htop_le : (⊤ : Subgroup W1) ≤
      (Section1.inertiaSubgroup H θ).comap f := by
    rw [← hw0gen]
    exact Subgroup.zpowers_le_of_mem hw0pre
  intro x hx
  let xW1 : W1 := ⟨(x : G), hx⟩
  have hxpre : xW1 ∈ (Section1.inertiaSubgroup H θ).comap f :=
    htop_le trivial
  have hfx : f xW1 = x := by
    ext
    rfl
  simpa [hfx] using hxpre


private theorem induced_eq_imp_conjugateOrbitConj_for_xmu_sec9
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    {φ θ : Section1.ClassFunction H}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hθ : Section1.IsIrreducibleCharacterOnGroup θ)
    (hInd : Section1.inducedCF H φ = Section1.inducedCF H θ) :
    ∃ i : Section1.conjugateOrbitIndex H θ,
      φ = Section1.conjugateOrbitConj H θ i := by
  classical
  rcases hφ with ⟨nφ, φRep, hφirr, hφeq⟩
  rcases hθ with ⟨nθ, θRep, hθirr, hθeq⟩
  subst φ
  subst θ
  exact Section1.proposition_1_5_c_induced_eq_imp_conjugate_orbit_canonical
    H φRep θRep hφirr hθirr hInd

private theorem conjugateOrbitConj_eq_self_of_inertia_top_sec9
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal]
    (θ : Section1.ClassFunction H)
    (hI : Section1.inertiaSubgroup H θ = ⊤)
    (i : Section1.conjugateOrbitIndex H θ) :
    Section1.conjugateOrbitConj H θ i = θ := by
  refine Quotient.inductionOn i ?_
  intro g
  have hg : g ∈ Section1.inertiaSubgroup H θ := by
    rw [hI]
    trivial
  change Section1.conjugateOnNormal H θ g = θ
  simpa [Section1.inertiaSubgroup] using hg


private theorem H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_of_W1InertiaData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (∀ i : ι, Section1.IsClassFunction (θ i)) →
        H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9 M W1 p
            ι μorbit θ →
          H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9 M MF H0 C
            p ι μorbit θ := by
  intro hcase hθclass hdata
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  dsimp [H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9] at hdata
  have hcomp : Dm.IsComplement' (W1.subgroupOf M) := by
    dsimp [Dm]
    exact ambientDerived_W1_isComplement'_subgroupOf_M_of_hypothesis_9_2_sec9
      M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
  intro i
  exact inertiaSubgroup_eq_top_of_isComplement'_le_sec9
    Dm (W1.subgroupOf M) (θ (μorbit i)) (hθclass (μorbit i)) hcomp
    (by simpa [Dm] using hdata i)

private theorem H0CLinearCandidateXmu_final_inertia_membership_withRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M))
    (hSH0C : kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C)
    (hθdata :
      ∀ i : ι,
        Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
          ¬ Section1.subgroupInKernel' (θ i)
            ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) ∧
          Section1.subgroupInKernel' (θ i)
            (((H0 ⊔ C).subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M))) :
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      Section1.inducedCF Dm (θ (μorbit i)) ∈ SH0C := by
  intro Dm i
  rcases hSH0C with ⟨_hYle, _hMFle, hmem⟩
  rw [hmem]
  exact ⟨θ (μorbit i), (hθdata (μorbit i)).1,
    (hθdata (μorbit i)).2.1, (hθdata (μorbit i)).2.2, rfl⟩

private theorem H0CLinearCandidateXmu_final_inertia_not_irreducible_withRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι}
    {θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)}
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hθirr : ∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (θ i))
    (hfinalInertia :
      let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
      let hDnormal : Dm.Normal := by
        simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
      letI : Dm.Normal := hDnormal
      ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
        Section1.inertiaSubgroup Dm (θ (μorbit i)) = ⊤) :
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      ¬ Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF Dm (θ (μorbit i))) := by
  classical
  intro Dm i hIndIrr
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  rcases hθirr (μorbit i) with ⟨n, ρ, hρirr, hθeq⟩
  have hnormInd :
      Section1.scalarProduct M
          (Section1.inducedCF Dm (θ (μorbit i)))
          (Section1.inducedCF Dm (θ (μorbit i))) =
        (Subgroup.index Dm : ℕ) := by
    have hnormρ :
        Section1.scalarProduct M
            (Section1.inducedCF Dm ρ.character)
            (Section1.inducedCF Dm ρ.character) =
          Dm.relIndex (Section1.inertiaSubgroup Dm ρ.character) :=
      Section1.proposition_1_5_b_rep_orbit_relIndex_canonical Dm ρ hρirr
    have hIρ :
        Section1.inertiaSubgroup Dm ρ.character = ⊤ := by
      simpa [hθeq, Dm] using hfinalInertia i
    simpa [hθeq, hIρ, Subgroup.relIndex_top_right] using hnormρ
  have hnormIrr :
      Section1.scalarProduct M
          (Section1.inducedCF Dm (θ (μorbit i)))
          (Section1.inducedCF Dm (θ (μorbit i))) = 1 :=
    Section1.scalarProduct_irreducibleCharacter_self hIndIrr
  have hindex_eq_one : Subgroup.index Dm = 1 := by
    exact_mod_cast hnormInd.symm.trans hnormIrr
  have hqeq : Subgroup.index Dm = q := by
    simpa [Dm] using
      ambientDerived_subgroupOf_index_eq_q_of_hypothesis_9_2_sec9
        M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
  have hqone : q = 1 := hqeq.symm.trans hindex_eq_one
  exact (case_9_7_a_q_prime_sec9 hcase).ne_one hqone

private theorem H0CLinearCandidateXmuSmuCoreDataWithRaw_of_finalInertiaData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
        H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9 M MF H0 C p
            ι μorbit θ →
          H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9 M p
              ι μorbit θ →
            H0CLinearCandidateXmuSmuCoreDataWithRaw_sec9 M MF H0 C p
              SH0C ι μorbit θ := by
  classical
  intro hcase hSH0C hdata hfinalInj
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  dsimp [H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9] at hdata
  dsimp [H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9] at hfinalInj
  rcases hdata with ⟨hθinj, hfinalInertia, hθdata⟩
  have hSHmem :
      ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
        Section1.inducedCF Dm (θ (μorbit i)) ∈ SH0C := by
    simpa [Dm] using
      H0CLinearCandidateXmu_final_inertia_membership_withRaw_sec9
        M MF H0 C p SH0C μorbit θ hSH0C hθdata
  have hnotIrr :
      ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
        ¬ Section1.IsIrreducibleCharacterOnGroup
          (Section1.inducedCF Dm (θ (μorbit i))) := by
    simpa [Dm] using
      H0CLinearCandidateXmu_final_inertia_not_irreducible_withRaw_sec9
        M MF U W1 W2 H0 C p q a hcase (fun i => (hθdata i).1)
        (by simpa [Dm] using hfinalInertia)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [μfinal, Dm] using hfinalInj
  · intro i
    exact hfinalInertia i
  · intro i
    have hpair :
        Section1.inducedCF Dm (θ (μorbit i)) ∈ SH0C ∧
          ¬ Section1.IsIrreducibleCharacterOnGroup
            (Section1.inducedCF Dm (θ (μorbit i))) :=
      ⟨hSHmem i, hnotIrr i⟩
    simpa [μfinal, reducibleCharacterFilter_sec9, Dm] using hpair
  · intro i j hij
    have hInd :
        Section1.inducedCF Dm (θ j) =
          Section1.inducedCF Dm (θ (μorbit i)) := by
      simpa [μfinal, Dm] using hij.symm
    rcases induced_eq_imp_conjugateOrbitConj_for_xmu_sec9
        Dm (hθdata j).1 (hθdata (μorbit i)).1 hInd with
      ⟨o, ho⟩
    have hconjSelf :
        Section1.conjugateOrbitConj Dm (θ (μorbit i)) o = θ (μorbit i) :=
      conjugateOrbitConj_eq_self_of_inertia_top_sec9
        Dm (θ (μorbit i)) (hfinalInertia i) o
    have hθeq : θ j = θ (μorbit i) := ho.trans hconjSelf
    refine Finset.mem_image.mpr ⟨i, by simp, ?_⟩
    exact (hθinj hθeq).symm

private theorem H0CLinearCandidateXmuFinalInjectiveDataWithRaw_of_finalInertiaData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    Function.Injective μorbit →
      H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9 M MF H0 C p
          ι μorbit θ →
        H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9 M p
          ι μorbit θ := by
  classical
  intro hμinj hdata
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  dsimp [H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9] at hdata
  dsimp [H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9]
  rcases hdata with ⟨hθinj, hfinalInertia, hθdata⟩
  intro i j hij
  have hInd :
      Section1.inducedCF Dm (θ (μorbit i)) =
        Section1.inducedCF Dm (θ (μorbit j)) := by
    simpa [μfinal, Dm] using hij
  rcases induced_eq_imp_conjugateOrbitConj_for_xmu_sec9
      Dm (hθdata (μorbit i)).1 (hθdata (μorbit j)).1 hInd with
    ⟨o, ho⟩
  have hconjSelf :
      Section1.conjugateOrbitConj Dm (θ (μorbit j)) o = θ (μorbit j) :=
    conjugateOrbitConj_eq_self_of_inertia_top_sec9
      Dm (θ (μorbit j)) (hfinalInertia j) o
  have hθeq : θ (μorbit i) = θ (μorbit j) := ho.trans hconjSelf
  exact hμinj (hθinj hθeq)

private theorem H0CLinearCandidateXmuSmuDataWithRaw_of_coreData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    H0CLinearCandidateXmuSmuCoreDataWithRaw_sec9 M MF H0 C p SH0C
        ι μorbit θ →
      H0CLinearCandidateXmuSmuDataWithRaw_sec9 M MF H0 C p SH0C
        ι μorbit θ := by
  classical
  intro hcore
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  dsimp [H0CLinearCandidateXmuSmuCoreDataWithRaw_sec9] at hcore
  rcases hcore with ⟨hfinalInj, _hfinalInertia, hfinalRed, hfinalEqMem⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact hfinalInj (by simpa [μfinal, Dm] using hij)
  · intro i
    simpa [μfinal, Dm] using hfinalRed i
  · intro i j hij
    exact hfinalEqMem i j (by simpa [μfinal, Dm] using hij)

private theorem H0CLinearCandidateXmuFinalSeparationDataWithRaw_of_smuData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    H0CLinearCandidateXmuSmuDataWithRaw_sec9 M MF H0 C p SH0C
        ι μorbit θ →
      H0CLinearCandidateXmuFinalSeparationDataWithRaw_sec9 M MF H0 C p
        SH0C ι μorbit θ := by
  intro h
  simpa [H0CLinearCandidateXmuSmuDataWithRaw_sec9,
    H0CLinearCandidateXmuFinalSeparationDataWithRaw_sec9] using h

private theorem H0CLinearCandidateXmuConcreteFinalImageDataWithRaw_of_final_separation_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    (reducibleCharacterFilter_sec9 M SH0C).card = p - 1 →
      H0CLinearCandidateXmuFinalSeparationDataWithRaw_sec9 M MF H0 C p
          SH0C ι μorbit θ →
        H0CLinearCandidateXmuConcreteFinalImageDataWithRaw_sec9 M MF H0 C p
          SH0C ι μorbit θ := by
  classical
  intro hredCard hdata
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  dsimp [H0CLinearCandidateXmuFinalSeparationDataWithRaw_sec9] at hdata
  rcases hdata with ⟨hfinalInj, hfinalRed, hfinalEqMem⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply hfinalInj
    simpa [μfinal, Dm] using
      congrArg (fun t : ι => Section1.inducedCF Dm (θ t)) hij
  · intro i
    simpa [μfinal, Dm] using hfinalRed i
  · intro χ hχred
    let Smu : Finset (Section1.ClassFunction M) := Finset.univ.image μfinal
    have hSmuSub : Smu ⊆ reducibleCharacterFilter_sec9 M SH0C := by
      intro χ hχ
      rcases Finset.mem_image.mp hχ with ⟨i, _hi, rfl⟩
      simpa [μfinal, Dm] using hfinalRed i
    have hSmuCard : Smu.card = p - 1 := by
      rw [Finset.card_image_of_injective _ hfinalInj]
      exact H0CLinearCandidateXmuRawIndex_card_sec9 p
    have hSmuEq :
        Smu = reducibleCharacterFilter_sec9 M SH0C :=
      Finset.eq_of_subset_of_card_le hSmuSub (by rw [hredCard, hSmuCard])
    have hχSmu : χ ∈ Smu := by
      rw [hSmuEq]
      exact hχred
    rcases Finset.mem_image.mp hχSmu with ⟨i, _hi, hiχ⟩
    exact ⟨i, hiχ.symm⟩
  · intro i j hj hijeq
    exact hj (hfinalEqMem i j (by simpa [μfinal, Dm] using hijeq))

private theorem H0CLinearCandidateXmuFinalImageData_of_concrete_final_image_withRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    H0CLinearCandidateXmuConcreteFinalImageDataWithRaw_sec9 M MF H0 C p
        SH0C ι μorbit θ →
      H0CLinearCandidateXmuFinalImageData_sec9 M MF H0 C p SH0C ι θ := by
  classical
  intro hdata
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let Xmu : Finset ι := Finset.univ.image μorbit
  dsimp [H0CLinearCandidateXmuConcreteFinalImageDataWithRaw_sec9] at hdata
  rcases hdata with ⟨hinj, hred, hcover, hsep⟩
  refine ⟨Xmu, ?_, ?_, ?_, ?_⟩
  · simpa [Xmu] using
      H0CLinearCandidateXmu_image_card_of_injective_withRaw_sec9 p μorbit hinj
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, _hj, rfl⟩
    simpa [Dm] using hred j
  · intro χ hχ
    rcases hcover χ hχ with ⟨i, hχeq⟩
    refine ⟨μorbit i, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
    · simpa [Dm] using hχeq
  · intro i hi j hj hijeq
    rcases Finset.mem_image.mp hi with ⟨k, _hk, rfl⟩
    exact hsep k j (by simpa [Xmu] using hj) (by
      simpa [Dm] using hijeq)


private def H0CLinearCandidateXthetaThetaCoordinateActionData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U _H0 C : Subgroup G)
    (p q ubar : ℕ)
    (ψHC : ULift.{u, 0} (Fin q → Fin (p - 1)) →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) : Prop :=
  let κ : Type u := ULift.{u, 0} (Fin q → Fin (p - 1))
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  ∃ hnormalC : (C.subgroupOf U).Normal,
    letI : (C.subgroupOf U).Normal := hnormalC
    ∃ instAction : MulAction (U ⧸ C.subgroupOf U) κ,
      letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
      (∀ k : κ, MulAction.stabilizer (U ⧸ C.subgroupOf U) k = ⊥) ∧
        Nat.card (U ⧸ C.subgroupOf U) = ubar ∧
        ∀ hnormalHCD : HCD.Normal,
          letI : HCD.Normal := hnormalHCD
          let ψ : κ → Section1.ClassFunction HCm :=
            fun k => Section1.subgroupOfClassFunction (ψHC k)
          let θ : κ → Section1.ClassFunction Dm :=
            fun k => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ k))
          (∀ k : κ,
            Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ k)) =
              HCD) ∧
            ∀ k l : κ,
              θ k = θ l ↔
                MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l

private def H0CLinearCandidateXthetaThetaCoordinateActionCoreData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U _H0 C : Subgroup G)
    (p q : ℕ)
    (ψHC : ULift.{u, 0} (Fin q → Fin (p - 1)) →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) : Prop :=
  let κ : Type u := ULift.{u, 0} (Fin q → Fin (p - 1))
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  ∃ hnormalC : (C.subgroupOf U).Normal,
    letI : (C.subgroupOf U).Normal := hnormalC
    ∃ instAction : MulAction (U ⧸ C.subgroupOf U) κ,
      letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
      (∀ k : κ, MulAction.stabilizer (U ⧸ C.subgroupOf U) k = ⊥) ∧
        ∀ hnormalHCD : HCD.Normal,
          letI : HCD.Normal := hnormalHCD
          let ψ : κ → Section1.ClassFunction HCm :=
            fun k => Section1.subgroupOfClassFunction (ψHC k)
          let θ : κ → Section1.ClassFunction Dm :=
            fun k => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ k))
          (∀ k : κ,
            Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ k)) =
              HCD) ∧
            ∀ k l : κ,
              θ k = θ l ↔
                MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l

private def H0CLinearCandidateXthetaThetaCoordinateOrbitData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U _H0 C : Subgroup G)
    (p q ubar : ℕ)
    (ψHC : ULift.{u, 0} (Fin q → Fin (p - 1)) →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) : Prop :=
  let κ : Type u := ULift.{u, 0} (Fin q → Fin (p - 1))
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  ∃ hnormalC : (C.subgroupOf U).Normal,
    letI : (C.subgroupOf U).Normal := hnormalC
    ∃ instAction : MulAction (U ⧸ C.subgroupOf U) κ,
      letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
      (∀ k : κ, MulAction.stabilizer (U ⧸ C.subgroupOf U) k = ⊥) ∧
        Nat.card (U ⧸ C.subgroupOf U) = ubar ∧
        ∀ hnormalHCD : HCD.Normal,
          letI : HCD.Normal := hnormalHCD
          let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
          let ψ : ι → Section1.ClassFunction HCm :=
            fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
          let θ : ι → Section1.ClassFunction Dm :=
            fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
          Function.Injective θ ∧
            ∀ i : ι,
              Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ i)) = HCD


private theorem
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_of_core_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C : Subgroup G)
    (p q ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    quotientBarUCardinality U C ubar →
      H0CLinearCandidateXthetaThetaCoordinateActionCoreData_sec9
        M MF U H0 C p q ψHC →
        H0CLinearCandidateXthetaThetaCoordinateActionData_sec9
          M MF U H0 C p q ubar ψHC := by
  intro hBarU hcore
  rcases hBarU with ⟨_hCU, hnormalBarC, hbarCard⟩
  rcases hcore with ⟨hnormalC, instAction, hstab, hcoord⟩
  refine ⟨hnormalC, instAction, hstab, ?_, hcoord⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  simpa using hbarCard

private theorem isIrreducible_subgroupOfClassFunction_sec9
    {G : Type u} [Group G] {H T : Subgroup G} [Finite H] [Finite T]
    (hHT : H ≤ T)
    {θ : Section1.ClassFunction H}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.subgroupOfClassFunction (T := T) θ) := by
  classical
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  let e : H.subgroupOf T ≃* H := Subgroup.subgroupOfEquivOfLe hHT
  let ρH : Representation ℂ (H.subgroupOf T) (Fin n → ℂ) :=
    ρ.comp e.toMonoidHom
  refine ⟨n, ρH, ?_, ?_⟩
  · exact (Section6.representation_isIrreducible_comp_surjective
      ρ e.toMonoidHom e.surjective hρirr)
  · ext h
    simp [ρH, e, Section1.subgroupOfClassFunction, hθeq,
      Representation.character, Subgroup.subgroupOfEquivOfLe]

private theorem subgroupInKernel'_subgroupOfClassFunction_sec9
    {G : Type u} [Group G] {H T A : Subgroup G}
    (_hAT : A ≤ T) (hAH : A ≤ H)
    {θ : Section1.ClassFunction H}
    (hθker : Section1.subgroupInKernel' θ (A.subgroupOf H)) :
    Section1.subgroupInKernel'
      (Section1.subgroupOfClassFunction (T := T) θ)
        ((A.subgroupOf T).subgroupOf (H.subgroupOf T)) := by
  intro a
  have haA : (((a : H.subgroupOf T) : T) : G) ∈ A := by
    have haAT : ((a : H.subgroupOf T) : T) ∈ A.subgroupOf T :=
      (a : (A.subgroupOf T).subgroupOf (H.subgroupOf T)).property
    simpa [Subgroup.mem_subgroupOf] using haAT
  let aH : A.subgroupOf H := ⟨⟨(((a : H.subgroupOf T) : T) : G), hAH haA⟩, by
    simpa [Subgroup.mem_subgroupOf] using haA⟩
  have ha := hθker aH
  simpa [Section1.subgroupOfClassFunction, aH,
    Section1.degree_subgroupOfClassFunction]
    using ha

private theorem subgroupInKernel'_of_subgroupOfClassFunction_sec9
    {G : Type u} [Group G] {H T A : Subgroup G}
    (hAT : A ≤ T) (_hAH : A ≤ H)
    {θ : Section1.ClassFunction H}
    (hθker : Section1.subgroupInKernel'
      (Section1.subgroupOfClassFunction (T := T) θ)
        ((A.subgroupOf T).subgroupOf (H.subgroupOf T))) :
    Section1.subgroupInKernel' θ (A.subgroupOf H) := by
  intro a
  have haA : ((a : H) : G) ∈ A := by
    exact (a : A.subgroupOf H).property
  let aT : H.subgroupOf T := ⟨⟨((a : H) : G), hAT haA⟩, by
    exact (a : H).property⟩
  have haT : (aT : T) ∈ A.subgroupOf T := by
    simpa [aT, Subgroup.mem_subgroupOf] using haA
  let aHT : (A.subgroupOf T).subgroupOf (H.subgroupOf T) := ⟨aT, haT⟩
  have ha := hθker aHT
  simpa [aT, aHT, Section1.subgroupOfClassFunction,
    Section1.degree_subgroupOfClassFunction] using ha

private theorem inducedCF_isIrreducible_of_inertia_eq_self_sec9
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal]
    {X : Section1.ClassFunction K}
    (hXirr : Section1.IsIrreducibleCharacterOnGroup X)
    (hIeq : Section1.inertiaSubgroup K X = K) :
    Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF K X) := by
  rcases hXirr with ⟨n, ρ, hρirr, hXeq⟩
  have hIeqρ :
      Section1.inertiaSubgroup K ρ.character = K := by
    simpa [hXeq] using hIeq
  have hrel :
      K.relIndex (Section1.inertiaSubgroup K ρ.character) = 1 := by
    rw [hIeqρ]
    simp [Subgroup.relIndex]
  simpa [hXeq] using
    Section1.proposition_1_5_b_irreducible_rep_orbit_relIndex_canonical
      K ρ hρirr hrel

private theorem inertiaSubgroup_eq_of_semidirect_no_nontrivial_complement_fixed_sec9
    {L : Type u} [Group L] [Finite L]
    (K W : Subgroup L) [K.Normal]
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) K W)
    {X : Section1.ClassFunction K}
    (hXclass : Section1.IsClassFunction X)
    (hnoFix :
      ∀ g : L, g ∈ W → g ≠ 1 →
        Section1.conjugateOnNormal K X g ≠ X) :
    Section1.inertiaSubgroup K X = K := by
  have hKleI : K ≤ Section1.inertiaSubgroup K X := by
    intro x hx
    change Section1.conjugateOnNormal K X x = X
    funext h
    unfold Section1.conjugateOnNormal
    change X ((⟨x, hx⟩ : K) * h * (⟨x, hx⟩ : K)⁻¹) = X h
    exact hXclass ⟨x, hx⟩ h
  apply le_antisymm
  · intro g hgI
    rcases hsemi.mul_surjective g (by trivial) with ⟨k, hkK, w, hwW, hkw⟩
    have hkI : k ∈ Section1.inertiaSubgroup K X := hKleI hkK
    have hwI : w ∈ Section1.inertiaSubgroup K X := by
      have :
          k⁻¹ * g ∈ Section1.inertiaSubgroup K X :=
        (Section1.inertiaSubgroup K X).mul_mem
          ((Section1.inertiaSubgroup K X).inv_mem hkI) hgI
      simpa [hkw, mul_assoc] using this
    have hw1 : w = 1 := by
      by_contra hwne
      have hfixw : Section1.conjugateOnNormal K X w = X := by
        simpa [Section1.inertiaSubgroup] using hwI
      exact hnoFix w hwW hwne hfixw
    have hgk : g = k := by
      calc
        g = k * w := hkw
        _ = k := by simp [hw1]
    simpa [hgk] using hkK
  · exact hKleI

private theorem inducedCF_isIrreducible_of_semidirect_no_nontrivial_complement_fixed_sec9
    {L : Type u} [Group L] [Finite L]
    (K W : Subgroup L) [K.Normal]
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) K W)
    {X : Section1.ClassFunction K}
    (hXirr : Section1.IsIrreducibleCharacterOnGroup X)
    (hnoFix :
      ∀ g : L, g ∈ W → g ≠ 1 →
        Section1.conjugateOnNormal K X g ≠ X) :
    Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF K X) := by
  rcases hXirr with ⟨n, ρ, hρirr, rfl⟩
  have hXclass : Section1.IsClassFunction ρ.character := by
    intro x g
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  have hIeq :
      Section1.inertiaSubgroup K ρ.character = K :=
    inertiaSubgroup_eq_of_semidirect_no_nontrivial_complement_fixed_sec9
      K W hsemi hXclass hnoFix
  exact inducedCF_isIrreducible_of_inertia_eq_self_sec9 K
    ⟨n, ρ, hρirr, rfl⟩ hIeq

private theorem subgroupInKernel'_inducedCF_of_subgroupInKernel'_sec9
    {L : Type u} [Group L] [Finite L]
    (K A : Subgroup L) [K.Normal] [A.Normal] (hAK : A ≤ K)
    {θ : Section1.ClassFunction K}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθker : Section1.subgroupInKernel' θ (A.subgroupOf K)) :
    Section1.subgroupInKernel' (Section1.inducedCF K θ) A := by
  rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
  have hρker : Section1.subgroupInKernel' ρ.character (A.subgroupOf K) := by
    simpa [hθeq] using hθker
  have hindKer : Section1.subgroupInKernel' (Section1.inducedCF K ρ.character) A :=
    (Section1.proposition_1_6_a K A hAK ρ).mp hρker
  simpa [hθeq] using hindKer

private theorem subgroupInKernel'_of_inducedCF_sec9
    {L : Type u} [Group L] [Finite L]
    (K A : Subgroup L) [K.Normal] [A.Normal] (hAK : A ≤ K)
    {θ : Section1.ClassFunction K}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθker : Section1.subgroupInKernel' (Section1.inducedCF K θ) A) :
    Section1.subgroupInKernel' θ (A.subgroupOf K) := by
  rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
  have hindKer :
      Section1.subgroupInKernel' (Section1.inducedCF K ρ.character) A := by
    simpa [hθeq] using hθker
  have hρker : Section1.subgroupInKernel' ρ.character (A.subgroupOf K) :=
    (Section1.proposition_1_6_a K A hAK ρ).mpr hindKer
  simpa [hθeq] using hρker

private theorem subgroupInKernel'_sup_of_irreducible_sec9
    {L : Type u} [Group L] [Finite L]
    {θ : Section1.ClassFunction L} {A B : Subgroup L}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hA : Section1.subgroupInKernel' θ A)
    (hB : Section1.subgroupInKernel' θ B) :
    Section1.subgroupInKernel' θ (A ⊔ B) := by
  rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
  subst θ
  have hAker : Section1.subgroupInRepresentationKernel ρ A :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ A).mp hA
  have hBker : Section1.subgroupInRepresentationKernel ρ B :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ B).mp hB
  let K : Subgroup L :=
    { carrier := {g | ρ g = 1}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change ρ (x * y) = 1
        rw [map_mul, hx, hy, one_mul]
      inv_mem' := by
        intro x hx
        change ρ x = 1 at hx
        change ρ (x⁻¹) = 1
        have hmul : ρ (x⁻¹) * ρ x = 1 := by
          rw [← map_mul]
          simp
        rw [hx] at hmul
        simpa using hmul }
  have hAK : A ≤ K := by
    intro x hx
    exact hAker ⟨x, hx⟩
  have hBK : B ≤ K := by
    intro x hx
    exact hBker ⟨x, hx⟩
  have hsupK : A ⊔ B ≤ K := sup_le hAK hBK
  apply (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
    ρ (A ⊔ B)).mpr
  intro x
  exact hsupK x.property


public theorem theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      MF ⊔ C ≤ ambientDerivedSubgroup M := by
  intro hcase
  rcases hcase with
    ⟨h92, _hH0MF, hC, _hpprime, _hqprime, _hpData, _hcomponent, _hrest⟩
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
      _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hMFD : MF ≤ ambientDerivedSubgroup M :=
    MF_le_ambientDerived_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hCD : C ≤ ambientDerivedSubgroup M := hC.1.trans hUleD
  exact sup_le hMFD hCD

public theorem theorem_9_8_HC_subgroupOf_ambientDerived_relIndex_eq_u_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        ((MF ⊔ C).subgroupOf M).relIndex
          ((ambientDerivedSubgroup M).subgroupOf M) = u := by
  classical
  intro hcase hBarU
  let D : Subgroup G := ambientDerivedSubgroup M
  let HC : Subgroup G := MF ⊔ C
  change (HC.subgroupOf M).relIndex (D.subgroupOf M) = u
  have hidxHC :
      Subgroup.index (HC.subgroupOf M) = q * u :=
    HC_index_eq_q_mul_u_of_hypothesis_9_2_sec9 M MF U W1 W2 C q u
      (case_9_7_a_hypothesis_9_2_sec9 hcase) hBarU
  have hDindex_eq_q : (D.subgroupOf M).index = q :=
    ambientDerived_subgroupOf_index_eq_q_of_hypothesis_9_2_sec9
      M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
  have hHC_le_D : HC ≤ D := by
    dsimp [HC, D]
    exact theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase
  have hHCsub_le_Dsub : HC.subgroupOf M ≤ D.subgroupOf M := by
    intro x hx
    have hxHC : ((x : M) : G) ∈ HC := by
      simpa [HC, Subgroup.mem_subgroupOf] using hx
    have hxD : ((x : M) : G) ∈ D := hHC_le_D hxHC
    simpa [D, Subgroup.mem_subgroupOf] using hxD
  have hright :
      (HC.subgroupOf M).relIndex (D.subgroupOf M) * q = u * q := by
    calc
      (HC.subgroupOf M).relIndex (D.subgroupOf M) * q
          = (HC.subgroupOf M).relIndex (D.subgroupOf M) *
              (D.subgroupOf M).index := by rw [hDindex_eq_q]
      _ = Subgroup.index (HC.subgroupOf M) := by
            exact Subgroup.relIndex_mul_index hHCsub_le_Dsub
      _ = q * u := hidxHC
      _ = u * q := Nat.mul_comm q u
  exact Nat.mul_right_cancel (case_9_7_a_q_prime_sec9 hcase).pos hright

private theorem theorem_9_8_MF_normal_HC_of_case_a_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (MF.subgroupOf (MF ⊔ C)).Normal := by
  intro hcase
  have hHC_le_M :
      MF ⊔ C ≤ M :=
    (theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase).trans
      (section12_ambientDerivedSubgroup_le (E := M))
  rcases case_9_7_a_hypothesis_9_2_sec9 hcase with h92
  rcases h92.mf.1 with ⟨hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
  have hM_le_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormalM
  have hHC_le_norm_MF : MF ⊔ C ≤ Subgroup.normalizer (MF : Set G) :=
    hHC_le_M.trans hM_le_norm_MF
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (show MF ≤ MF ⊔ C from le_sup_left)).2 hHC_le_norm_MF


public theorem theorem_9_8_H0C_normal_HC_of_case_a_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal := by
  intro hcase
  have hH0C_le_HC : H0 ⊔ C ≤ MF ⊔ C :=
    sup_le_sup (case_9_7_a_H0_le_MF_sec9 hcase) le_rfl
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hH0C_le_HC).2
  have hH0_le_M : H0 ≤ M :=
    (case_9_7_a_H0_le_MF_sec9 hcase).trans (case_9_7_a_MF_le_M_sec9 hcase)
  have hH0normalM : (H0.subgroupOf M).Normal :=
    case_9_7_a_H0_normal_M_sec9 hcase
  have hM_le_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_M).1 hH0normalM
  have hMF_norm_H0C :
      MF ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) := by
    apply le_normalizer_sup_of_le_normalizer_left_commutator_right_sec9
    · exact (case_9_7_a_MF_le_M_sec9 hcase).trans hM_le_norm_H0
    · intro n hnMF b hbC
      exact ((case_9_7_a_quotientCentralizerIn_sec9 hcase).2 b
        ((case_9_7_a_quotientCentralizerIn_sec9 hcase).1 hbC)).mp hbC n hnMF
  have hC_norm_H0C :
      C ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) :=
    le_sup_right.trans (Subgroup.le_normalizer (H := H0 ⊔ C))
  exact sup_le hMF_norm_H0C hC_norm_H0C

public theorem theorem_9_8_HC_normal_ambientDerived_subgroupOf_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        (((MF ⊔ C).subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal := by
  intro hcase hBarU
  let D : Subgroup G := ambientDerivedSubgroup M
  let HC : Subgroup G := MF ⊔ C
  rcases hBarU with ⟨hC_le_U_card, hCnormalU, _hcardU⟩
  have h92 := case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.mf.1 with ⟨hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, hD_eq, _hMFUdisj⟩
  have hHC_le_D : HC ≤ D := by
    dsimp [HC, D]
    exact sup_le hMFleD (hC_le_U_card.trans hUleD)
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le (E := M)
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormalM
  have hD_norm_MF : D ≤ Subgroup.normalizer (MF : Set G) :=
    hDleM.trans hM_norm_MF
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    hUleD.trans hD_norm_MF
  have hU_norm_C : U ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_U_card).1 hCnormalU
  have hU_norm_HC : U ≤ Subgroup.normalizer (HC : Set G) := by
    dsimp [HC]
    exact le_normalizer_sup_of_le_normalizer_sec9 MF C U hU_norm_MF hU_norm_C
  have hMF_norm_HC : MF ≤ Subgroup.normalizer (HC : Set G) :=
    (le_sup_left : MF ≤ HC).trans (Subgroup.le_normalizer (H := HC))
  have hMFU_norm_HC : MF ⊔ U ≤ Subgroup.normalizer (HC : Set G) :=
    sup_le hMF_norm_HC hU_norm_HC
  have hD_norm_HC : D ≤ Subgroup.normalizer (HC : Set G) := by
    simpa [D, hD_eq] using hMFU_norm_HC
  change ((HC.subgroupOf M).subgroupOf (D.subgroupOf M)).Normal
  exact subgroupOf_subgroupOf_normal_of_le_normalizer_sec9 hHC_le_D hD_norm_HC

public theorem theorem_9_8_H0C_normal_M_of_case_a_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      ((H0 ⊔ C).subgroupOf M).Normal := by
  intro hcase
  have hpData :
      ∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
            quotientChiefFactorData_9_6 M MF H0 W1 hp := by
    rcases hcase with
      ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, hpData, _hrest⟩
    exact hpData
  exact theorem_9_H0C_normal_M_source_core_sec9 M MF U W1 W2 H0 C p q
    (case_9_7_a_hypothesis_9_2_sec9 hcase)
    (case_9_7_a_H0_le_MF_sec9 hcase)
    (case_9_7_a_quotientCentralizerIn_sec9 hcase)
    (case_9_7_a_p_prime_sec9 hcase)
    hpData

public theorem theorem_9_8_H0C_normal_ambientDerived_subgroupOf_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (((H0 ⊔ C).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)).Normal := by
  intro hcase
  have hH0CnormalM : ((H0 ⊔ C).subgroupOf M).Normal :=
    theorem_9_8_H0C_normal_M_of_case_a_sec9 M MF U W1 W2 H0 C p q a hcase
  letI : ((H0 ⊔ C).subgroupOf M).Normal := hH0CnormalM
  exact Section1.subgroupOf_normal_of_normal ((H0 ⊔ C).subgroupOf M)
    ((ambientDerivedSubgroup M).subgroupOf M)

private theorem theorem_9_8_H0Uprime_normal_ambientDerived_subgroupOf_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Uprime = (_root_.commutator U).map U.subtype →
        (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal := by
  intro hcase hUprimeEq
  let D : Subgroup G := ambientDerivedSubgroup M
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, hD_eq, _hMFUdisj⟩
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le (E := M)
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hUprimeU : Uprime ≤ U := by
    rw [hUprimeEq, Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_le_self U
  have hH0Uprime_le_D : H0 ⊔ Uprime ≤ D :=
    sup_le (hH0MF.trans hMFleD) (hUprimeU.trans hUleD)
  have hH0leM : H0 ≤ M := (hH0MF.trans hMFleD).trans hDleM
  have hM_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH0leM).1
      (case_9_7_a_H0_normal_M_sec9 hcase)
  have hMF_norm_H0 : MF ≤ Subgroup.normalizer (H0 : Set G) :=
    (hMFleD.trans hDleM).trans hM_norm_H0
  have hU_norm_H0 : U ≤ Subgroup.normalizer (H0 : Set G) :=
    (hUleD.trans hDleM).trans hM_norm_H0
  have hcomm_image :
      (_root_.commutator U).map U.subtype ≤ Subgroup.centralizer (MF : Set G) :=
    (Section8.theorem_8_5_b M MF U W1 W2 h92.typePDefinitionData).1
  have hMF_norm_H0Uprime :
      MF ≤ Subgroup.normalizer ((H0 ⊔ Uprime : Subgroup G) : Set G) := by
    apply le_normalizer_sup_of_le_normalizer_left_commutator_right_sec9
    · exact hMF_norm_H0
    · intro n hnMF b hbUprime
      have hbcent : b ∈ Subgroup.centralizer (MF : Set G) := by
        exact hcomm_image (by simpa [hUprimeEq] using hbUprime)
      have hbcomm : n * b = b * n :=
        (Subgroup.mem_centralizer_iff.mp hbcent) n hnMF
      have hcomm_eq : ⁅b, n⁆ = 1 := by
        rw [commutatorElement_def]
        calc
          b * n * b⁻¹ * n⁻¹ = (n * b) * b⁻¹ * n⁻¹ := by rw [← hbcomm]
          _ = 1 := by group
      rw [hcomm_eq]
      exact H0.one_mem
  have hUprime_comm : Uprime = (⁅U, U⁆ : Subgroup G) := by
    rw [hUprimeEq, Subgroup.map_subtype_commutator]
  have hU_norm_Uprime : U ≤ Subgroup.normalizer (Uprime : Set G) := by
    have hU_norm_comm :
        U ≤ Subgroup.normalizer (((⁅U, U⁆ : Subgroup G) : Set G)) :=
      normalizer_le_normalizer_commutator_self_sec9 U U
        (Subgroup.le_normalizer (H := U))
    simpa [hUprime_comm] using hU_norm_comm
  have hU_norm_H0Uprime :
      U ≤ Subgroup.normalizer ((H0 ⊔ Uprime : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer_sec9 H0 Uprime U
      hU_norm_H0 hU_norm_Uprime
  have hMFU_norm_H0Uprime :
      MF ⊔ U ≤ Subgroup.normalizer ((H0 ⊔ Uprime : Subgroup G) : Set G) :=
    sup_le hMF_norm_H0Uprime hU_norm_H0Uprime
  have hD_norm_H0Uprime :
      D ≤ Subgroup.normalizer ((H0 ⊔ Uprime : Subgroup G) : Set G) := by
    simpa [D, hD_eq] using hMFU_norm_H0Uprime
  exact subgroupOf_subgroupOf_normal_of_le_normalizer_sec9
    hH0Uprime_le_D hD_norm_H0Uprime

public theorem theorem_9_8_HC_normal_M_of_case_a_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        ((MF ⊔ C).subgroupOf M).Normal := by
  intro hcase hBarU
  let D : Subgroup G := ambientDerivedSubgroup M
  let HC : Subgroup G := MF ⊔ C
  rcases hBarU with ⟨hC_le_U_card, hCnormalU, _hcardU⟩
  have h92 := case_9_7_a_hypothesis_9_2_sec9 hcase
  have hC : quotientCentralizerIn MF H0 U C :=
    case_9_7_a_quotientCentralizerIn_sec9 hcase
  rcases h92.mf.1 with ⟨hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, hcompMW1, hUleD,
      _hUnil, hW1normUInM, hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
      _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hHC_le_M : HC ≤ M := by
    dsimp [HC]
    exact (theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase).trans
      (section12_ambientDerivedSubgroup_le (E := M))
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hHC_le_M).2 ?_
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le (E := M)
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormalM
  have hD_norm_MF : D ≤ Subgroup.normalizer (MF : Set G) :=
    hDleM.trans hM_norm_MF
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    hUleD.trans hD_norm_MF
  have hU_norm_C : U ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_U_card).1 hCnormalU
  have hU_norm_HC : U ≤ Subgroup.normalizer (HC : Set G) := by
    dsimp [HC]
    exact le_normalizer_sup_of_le_normalizer_sec9 MF C U hU_norm_MF hU_norm_C
  have hMF_norm_HC : MF ≤ Subgroup.normalizer (HC : Set G) :=
    (le_sup_left : MF ≤ HC).trans (Subgroup.le_normalizer (H := HC))
  have hMFU_norm_HC : MF ⊔ U ≤ Subgroup.normalizer (HC : Set G) :=
    sup_le hMF_norm_HC hU_norm_HC
  have hD_norm_HC : D ≤ Subgroup.normalizer (HC : Set G) := by
    have hD_eq : D = MF ⊔ U := by
      dsimp [D]
      exact hcompDU.2.2.1
    simpa [D, hD_eq] using hMFU_norm_HC
  have hW1_le_M : W1 ≤ M := hW1hall.1
  have hW1_norm_U : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro w hw
    exact (mem_subgroupNormalizerIn.mp (hW1normUInM hw)).1
  have hW1_norm_MF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    hW1_le_M.trans hM_norm_MF
  have hH0_le_M : H0 ≤ M :=
    (case_9_7_a_H0_le_MF_sec9 hcase).trans hMFleM
  have hH0_normal_M : (H0.subgroupOf M).Normal :=
    case_9_7_a_H0_normal_M_sec9 hcase
  have hW1_norm_C : W1 ≤ Subgroup.normalizer (C : Set G) :=
    quotientCentralizerIn_le_normalizer_of_le_normalizers_sec9
      (M := M) (MF := MF) (U := U) (H0 := H0) (N := W1)
      hW1_le_M hW1_norm_U hW1_norm_MF hH0_le_M hH0_normal_M hC
  have hW1_norm_HC : W1 ≤ Subgroup.normalizer (HC : Set G) := by
    dsimp [HC]
    exact le_normalizer_sup_of_le_normalizer_sec9 MF C W1
      hW1_norm_MF hW1_norm_C
  have hDW1_norm_HC : D ⊔ W1 ≤ Subgroup.normalizer (HC : Set G) :=
    sup_le hD_norm_HC hW1_norm_HC
  have hM_eq : M = D ⊔ W1 := by
    dsimp [D]
    exact hcompMW1.2.2.1
  simpa [hM_eq] using hDW1_norm_HC

private theorem theorem_9_8_MF_C_isComplement_HC_of_case_a_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (MF.subgroupOf (MF ⊔ C)).IsComplement' (C.subgroupOf (MF ⊔ C)) := by
  intro hcase
  have hMFnormalHC : (MF.subgroupOf (MF ⊔ C)).Normal :=
    theorem_9_8_MF_normal_HC_of_case_a_sec9 M MF U W1 W2 H0 C p q a hcase
  have hC_le_U : C ≤ U :=
    (case_9_7_a_quotientCentralizerIn_sec9 hcase).1
  have h92 := case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', _hUleD, _hD_eq, hMFUdisj⟩
  have hdisjMFC : Disjoint MF C := by
    rw [disjoint_iff] at hMFUdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : x ∈ MF ⊓ U := ⟨hx.1, hC_le_U hx.2⟩
      simpa [hMFUdisj] using hxAmb
    · exact bot_le
  have hdisjMFC_sub :
      Disjoint (MF.subgroupOf (MF ⊔ C)) (C.subgroupOf (MF ⊔ C)) := by
    rw [disjoint_iff] at hdisjMFC ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ MF ⊓ C := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf] using hx.1,
          by simpa [Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hdisjMFC] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hMF_C_supTop : MF.subgroupOf (MF ⊔ C) ⊔ C.subgroupOf (MF ⊔ C) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := MF) (A' := C) (B := MF ⊔ C)
      le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  letI : (MF.subgroupOf (MF ⊔ C)).Normal := hMFnormalHC
  exact isComplement'_of_disjoint_sup_eq_top_of_normal
    (MF.subgroupOf (MF ⊔ C)) (C.subgroupOf (MF ⊔ C))
    hdisjMFC_sub hMF_C_supTop

private theorem subgroupOfClassFunction_injective_sec9
    {G : Type u} [Group G] {H T : Subgroup G} (hHT : H ≤ T) :
    Function.Injective
      (fun θ : Section1.ClassFunction H =>
        Section1.subgroupOfClassFunction (T := T) θ) := by
  intro θ ψ hθψ
  ext h
  have hval := congrFun hθψ ((Subgroup.subgroupOfEquivOfLe hHT).symm h)
  simpa [Section1.subgroupOfClassFunction, Subgroup.subgroupOfEquivOfLe] using hval

private theorem degree_eq_one_of_irreducible_subgroupInKernel_commutator_sec9
    {G : Type u} [Group G] [Finite G]
    {θ : Section1.ClassFunction G}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hker : Section1.subgroupInKernel' θ (_root_.commutator G)) :
    Section1.degree θ = (1 : ℂ) := by
  classical
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  have hθkerρ : Section1.subgroupInKernel' ρ.character (_root_.commutator G) := by
    simpa [hθeq] using hker
  have hkerRep : Section1.subgroupInRepresentationKernel ρ (_root_.commutator G) :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ
      (_root_.commutator G)).mp hθkerρ
  let ρq : Representation ℂ (G ⧸ _root_.commutator G) (Fin n → ℂ) :=
    Section1.quotientRepresentationOfKernelSubgroup ρ (_root_.commutator G) hkerRep
  let q : G →* G ⧸ _root_.commutator G := QuotientGroup.mk' (_root_.commutator G)
  have hcomp_eq : ρq.comp q = ρ := by
    apply MonoidHom.ext
    intro g
    exact Section1.quotientRepresentationOfKernelSubgroup_mk ρ
      (_root_.commutator G) hkerRep g
  have hρqirr : Representation.IsIrreducible ρq := by
    apply Section6.representation_isIrreducible_of_comp_surjective ρq q
      (QuotientGroup.mk'_surjective (_root_.commutator G))
    simpa [hcomp_eq] using hρirr
  haveI : IsMulCommutative (G ⧸ _root_.commutator G) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (by
      intro x hx
      exact hx)
  have hn : n = 1 := by
    haveI : Representation.IsIrreducible ρq := hρqirr
    simpa using
      (Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := ρq))
  rw [hθeq, Section1.degree_representation_character]
  simp [hn]

private theorem monoidHom_mem_commutator_of_mem_sec9
    {G H : Type u} [Group G] [Group H] (f : G →* H) {x : G}
    (hx : x ∈ _root_.commutator G) :
    f x ∈ _root_.commutator H := by
  rw [commutator_eq_closure] at hx ⊢
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨a, b, rfl⟩
    exact Subgroup.subset_closure
      ⟨f a, f b, by rw [map_commutatorElement]⟩
  · rw [map_one]
    exact (Subgroup.closure (commutatorSet H)).one_mem
  · intro a b _ha_mem _hb_mem ha hb
    simpa [map_mul] using (Subgroup.closure (commutatorSet H)).mul_mem ha hb
  · intro a _ha_mem ha
    simpa [map_inv] using (Subgroup.closure (commutatorSet H)).inv_mem ha

private theorem commutator_le_subgroupOf_of_isComplement'_pairwise_sec9
    {G : Type u} [Group G]
    {K A B N : Subgroup G}
    (_hAK : A ≤ K) (_hBK : B ≤ K) (_hNK : N ≤ K)
    [hNnormalK : (N.subgroupOf K).Normal]
    (hcomp : (A.subgroupOf K).IsComplement' (B.subgroupOf K))
    (hAA : ⁅A, A⁆ ≤ N) (hAB : ⁅A, B⁆ ≤ N) (hBB : ⁅B, B⁆ ≤ N) :
    _root_.commutator K ≤ N.subgroupOf K := by
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  let qK : K →* K ⧸ N.subgroupOf K := QuotientGroup.mk' (N.subgroupOf K)
  have hcomm_AB : ∀ (u v : K), (u : G) ∈ A → (v : G) ∈ B →
      qK u * qK v = qK v * qK u := by
    intro u v huA hvB
    rw [← commutatorElement_eq_one_iff_mul_comm]
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := N.subgroupOf K) ⁅u, v⁆).mpr (by
      rw [Subgroup.mem_subgroupOf]
      exact hAB (Subgroup.commutator_mem_commutator huA hvB))
  have hcomm_AA : ∀ (u v : K), (u : G) ∈ A → (v : G) ∈ A →
      qK u * qK v = qK v * qK u := by
    intro u v huA hvA
    rw [← commutatorElement_eq_one_iff_mul_comm]
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := N.subgroupOf K) ⁅u, v⁆).mpr (by
      rw [Subgroup.mem_subgroupOf]
      exact hAA (Subgroup.commutator_mem_commutator huA hvA))
  have hcomm_BB : ∀ (u v : K), (u : G) ∈ B → (v : G) ∈ B →
      qK u * qK v = qK v * qK u := by
    intro u v huB hvB
    rw [← commutatorElement_eq_one_iff_mul_comm]
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := N.subgroupOf K) ⁅u, v⁆).mpr (by
      rw [Subgroup.mem_subgroupOf]
      exact hBB (Subgroup.commutator_mem_commutator huB hvB))
  refine ⟨?_⟩
  apply Std.Commutative.mk
  intro x
  obtain ⟨x0, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf K) x
  intro y
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf K) y
  rcases hcomp.2 x0 with ⟨⟨a, b⟩, hxab⟩
  rcases hcomp.2 y0 with ⟨⟨c, d⟩, hycd⟩
  have haA : (a : G) ∈ A := a.2
  have hbB : (b : G) ∈ B := b.2
  have hcA : (c : G) ∈ A := c.2
  have hdB : (d : G) ∈ B := d.2
  have hxq : qK x0 = qK a * qK b := by rw [← hxab]; simp [qK]
  have hyq : qK y0 = qK c * qK d := by rw [← hycd]; simp [qK]
  have hAC := hcomm_AA a c haA hcA
  have hAD := hcomm_AB a d haA hdB
  have hCB := hcomm_AB c b hcA hbB
  have hBC : qK b * qK c = qK c * qK b := hCB.symm
  have hBD := hcomm_BB b d hbB hdB
  calc
    qK x0 * qK y0 = (qK a * qK b) * (qK c * qK d) := by rw [hxq, hyq]
    _ = qK a * (qK b * qK c) * qK d := by simp [mul_assoc]
    _ = qK a * (qK c * qK b) * qK d := by rw [hBC]
    _ = (qK a * qK c) * (qK b * qK d) := by simp [mul_assoc]
    _ = (qK c * qK a) * (qK d * qK b) := by rw [hAC, hBD]
    _ = qK c * (qK a * qK d) * qK b := by simp [mul_assoc]
    _ = qK c * (qK d * qK a) * qK b := by rw [hAD]
    _ = (qK c * qK d) * (qK a * qK b) := by simp [mul_assoc]
    _ = qK y0 * qK x0 := by rw [hxq, hyq]


private theorem theorem_9_8_H0Cprime_le_HC_of_case_a_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Cprime = (_root_.commutator C).map C.subtype →
        H0 ⊔ Cprime ≤ MF ⊔ C := by
  intro hcase hCprimeEq
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hCprimeC : Cprime ≤ C := by
    rw [hCprimeEq]
    rintro x ⟨y, _hy, rfl⟩
    exact y.property
  exact sup_le_sup hH0MF hCprimeC

private theorem theorem_9_8_H0Cprime_normal_HC_of_case_a_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Cprime = (_root_.commutator C).map C.subtype →
        ((H0 ⊔ Cprime).subgroupOf (MF ⊔ C)).Normal := by
  intro hcase hCprimeEq
  have hN_le_HC : H0 ⊔ Cprime ≤ MF ⊔ C :=
    theorem_9_8_H0Cprime_le_HC_of_case_a_sec9
      M MF U W1 W2 H0 C Cprime p q a hcase hCprimeEq
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hN_le_HC).2
  let N : Subgroup G := H0 ⊔ Cprime
  have hCprimeC : Cprime ≤ C := by
    rw [hCprimeEq]
    rintro x ⟨y, _hy, rfl⟩
    exact y.property
  have hCprime_comm : Cprime = (⁅C, C⁆ : Subgroup G) := by
    rw [hCprimeEq, Subgroup.map_subtype_commutator]
  have h92 := case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
  have hDleM : ambientDerivedSubgroup M ≤ M :=
    section12_ambientDerivedSubgroup_le (E := M)
  have hH0_le_M : H0 ≤ M :=
    (case_9_7_a_H0_le_MF_sec9 hcase).trans
      (case_9_7_a_MF_le_M_sec9 hcase)
  have hM_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_M).1
      (case_9_7_a_H0_normal_M_sec9 hcase)
  have hMF_norm_H0 : MF ≤ Subgroup.normalizer (H0 : Set G) :=
    (case_9_7_a_MF_le_M_sec9 hcase).trans hM_norm_H0
  have hC_le_U : C ≤ U := (case_9_7_a_quotientCentralizerIn_sec9 hcase).1
  have hC_norm_H0 : C ≤ Subgroup.normalizer (H0 : Set G) :=
    hC_le_U.trans (hUleD.trans (hDleM.trans hM_norm_H0))
  have hMF_norm_N : MF ≤ Subgroup.normalizer (N : Set G) := by
    dsimp [N]
    apply le_normalizer_sup_of_le_normalizer_left_commutator_right_sec9
    · exact hMF_norm_H0
    · intro n hnMF b hbCprime
      have hbC : b ∈ C := hCprimeC hbCprime
      have hbU : b ∈ U := hC_le_U hbC
      exact ((case_9_7_a_quotientCentralizerIn_sec9 hcase).2 b hbU).mp
        hbC n hnMF
  have hC_norm_Cprime : C ≤ Subgroup.normalizer (Cprime : Set G) := by
    have hC_norm_comm :
        C ≤ Subgroup.normalizer (((⁅C, C⁆ : Subgroup G) : Set G)) :=
      normalizer_le_normalizer_commutator_self_sec9 C C
        (Subgroup.le_normalizer (H := C))
    simpa [hCprime_comm] using hC_norm_comm
  have hC_norm_N : C ≤ Subgroup.normalizer (N : Set G) := by
    dsimp [N]
    exact le_normalizer_sup_of_le_normalizer_sec9 H0 Cprime C
      hC_norm_H0 hC_norm_Cprime
  exact sup_le hMF_norm_N hC_norm_N

private theorem theorem_9_8_HC_commutator_le_H0Cprime_subgroupOf_case_a_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Cprime = (_root_.commutator C).map C.subtype →
        _root_.commutator
            (((MF ⊔ C).subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M)) ≤
          ((((H0 ⊔ Cprime).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
              (((MF ⊔ C).subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M))) := by
  intro hcase hCprimeEq
  let D : Subgroup G := ambientDerivedSubgroup M
  let HC : Subgroup G := MF ⊔ C
  let N : Subgroup G := H0 ⊔ Cprime
  have hN_le_HC : N ≤ HC := by
    dsimp [N, HC]
    exact theorem_9_8_H0Cprime_le_HC_of_case_a_sec9
      M MF U W1 W2 H0 C Cprime p q a hcase hCprimeEq
  have hCprimeC : Cprime ≤ C := by
    rw [hCprimeEq]
    rintro x ⟨y, _hy, rfl⟩
    exact y.property
  have hNnormalHC : (N.subgroupOf HC).Normal := by
    dsimp [N, HC]
    exact theorem_9_8_H0Cprime_normal_HC_of_case_a_sec9
      M MF U W1 W2 H0 C Cprime p q a hcase hCprimeEq
  letI : (N.subgroupOf HC).Normal := hNnormalHC
  have hMFroot_le_H0sub : _root_.commutator MF ≤ H0.subgroupOf MF := by
    rcases case_9_7_a_hoReductionData_sec9 hcase with ⟨hp, _hpval, hpData⟩
    rcases hpData with
      ⟨_hH0MF, _hMFM, _hH0normalM, _hH0normalMF, _hH0ltMF, hElem,
        _hrest⟩
    rcases hElem with ⟨hnormal, hbarElem⟩
    letI : (H0.subgroupOf MF).Normal := hnormal
    letI : IsElementaryAbelian hp.val (MF ⧸ H0.subgroupOf MF) := hbarElem
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    infer_instance
  have hAA : ⁅MF, MF⁆ ≤ N := by
    intro x hx
    have hxmap : x ∈ (_root_.commutator MF).map MF.subtype := by
      simpa [Subgroup.map_subtype_commutator] using hx
    rcases hxmap with ⟨y, hy, hyx⟩
    have hyH0 : (y : G) ∈ H0 := hMFroot_le_H0sub hy
    rw [← hyx]
    exact Subgroup.mem_sup_left hyH0
  have hCMF_le_H0 : ⁅C, MF⁆ ≤ H0 := by
    rw [Subgroup.commutator_le]
    intro c hc m hm
    have hcent := case_9_7_a_quotientCentralizerIn_sec9 hcase
    exact (hcent.2 c (hcent.1 hc)).mp hc m hm
  have hAB : ⁅MF, C⁆ ≤ N := by
    intro x hx
    exact Subgroup.mem_sup_left
      (hCMF_le_H0 ((Subgroup.commutator_comm_le MF C) hx))
  have hBB : ⁅C, C⁆ ≤ N := by
    intro x hx
    exact Subgroup.mem_sup_right (by
      simpa [hCprimeEq, Subgroup.map_subtype_commutator] using hx)
  have hrootHC : _root_.commutator HC ≤ N.subgroupOf HC := by
    exact commutator_le_subgroupOf_of_isComplement'_pairwise_sec9
      (K := HC) (A := MF) (B := C) (N := N)
      le_sup_left le_sup_right hN_le_HC
      (theorem_9_8_MF_C_isComplement_HC_of_case_a_sec9
        M MF U W1 W2 H0 C p q a hcase)
      hAA hAB hBB
  let Dm : Subgroup M := D.subgroupOf M
  let K : Subgroup Dm := (HC.subgroupOf M).subgroupOf Dm
  change _root_.commutator K ≤
    (((N.subgroupOf M).subgroupOf Dm).subgroupOf K)
  intro x hx
  let φ : K →* HC :=
    { toFun := fun x =>
        ⟨(((x : Dm) : M) : G), by
          have hxHCm : ((x : Dm) : M) ∈ HC.subgroupOf M := by
            have hxK : (x : Dm) ∈ (HC.subgroupOf M).subgroupOf Dm := by
              exact x.property
            change ((x : Dm) : M) ∈ HC.subgroupOf M at hxK
            exact hxK
          simpa [Subgroup.mem_subgroupOf] using hxHCm⟩
      map_one' := by
        ext
        rfl
      map_mul' := by
        intro a b
        ext
        rfl }
  have hxHC : φ x ∈ _root_.commutator HC :=
    monoidHom_mem_commutator_of_mem_sec9 φ hx
  have hxNsub : φ x ∈ N.subgroupOf HC := hrootHC hxHC
  have hxN : ((φ x : HC) : G) ∈ N := by
    simpa [Subgroup.mem_subgroupOf] using hxNsub
  rw [Subgroup.mem_subgroupOf]
  change (((x : Dm) : M) : G) ∈ N
  simpa [φ] using hxN

private theorem irreducible_degree_nat_le_induced_linear_index_of_inner_sec9
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {θ : Section1.ClassFunction L} {ψ : Section1.ClassFunction K}
    {d : ℕ} :
    Section1.IsIrreducibleCharacterOnGroup θ →
      Section1.IsIrreducibleCharacterOnGroup ψ →
        Section1.degree ψ = (1 : ℂ) →
          Section1.scalarProduct K ψ (Section1.subgroupRestriction K θ) ≠ 0 →
            Section1.degree θ = (d : ℂ) →
              d ≤ Subgroup.index K := by
  classical
  intro hθirr hψirr hψdeg hinner hθdeg
  rcases hθirr with ⟨nθ, ρθ, hρθirr, hθeq⟩
  rcases hψirr with ⟨nψ, ρψ, _hρψirr, hψeq⟩
  let indρψ : Representation ℂ L (Representation.IndV K.subtype ρψ) :=
    Representation.ind K.subtype ρψ
  haveI : FiniteDimensional ℂ (Representation.IndV K.subtype ρψ) :=
    Representation.finiteDimensional_ind K ρψ
  have hθclass : Section1.IsClassFunction θ := by
    intro x g
    rw [hθeq]
    simpa [mul_assoc] using Representation.char_conj (ρ := ρθ) g x
  have hIndInner :
      Section1.scalarProduct L (Section1.inducedCF K ψ) θ ≠ 0 := by
    rw [Section1.scalarProduct_inducedCF_left K ψ θ hθclass]
    exact hinner
  have hIndInnerRep :
      Section1.scalarProduct L indρψ.character ρθ.character ≠ 0 := by
    simpa [indρψ, hθeq, hψeq,
      Section1.inducedCF_eq_representation_character K ρψ] using hIndInner
  have hfinrank_ne :
      (Module.finrank ℂ (Representation.IntertwiningMap ρθ indρψ) : ℂ) ≠ 0 := by
    simpa [Section1.scalarProduct_representation_char_eq_finrank ρθ indρψ]
      using hIndInnerRep
  have hfinrank_nat_ne :
      Module.finrank ℂ (Representation.IntertwiningMap ρθ indρψ) ≠ 0 := by
    intro hzero
    apply hfinrank_ne
    simp [hzero]
  have hfinrank_pos :
      0 < Module.finrank ℂ (Representation.IntertwiningMap ρθ indρψ) :=
    Nat.pos_of_ne_zero hfinrank_nat_ne
  rw [Module.finrank_pos_iff_exists_ne_zero] at hfinrank_pos
  rcases hfinrank_pos with ⟨f, hf⟩
  have hf_inj : Function.Injective f := by
    letI : Representation.IsIrreducible ρθ := hρθirr
    rcases (Representation.IsIrreducible.injective_or_eq_zero
        (ρ := ρθ) (σ := indρψ) f) with hinj | hzero
    · exact hinj
    · exact (hf hzero).elim
  have hnθ_le_ind :
      nθ ≤ Module.finrank ℂ (Representation.IndV K.subtype ρψ) := by
    simpa [Module.finrank_fin_fun] using
      (LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) hf_inj)
  have hfinrank_ind_eq_index :
      Module.finrank ℂ (Representation.IndV K.subtype ρψ) = Subgroup.index K := by
    have hdeg_ind :
        Section1.degree (Section1.inducedCF K ψ) = (Subgroup.index K : ℂ) := by
      rw [Section1.degree_inducedClassFunction, hψdeg]
      simp
    have hdeg_ind_rep :
        Section1.degree (Section1.inducedCF K ψ) =
          (Module.finrank ℂ (Representation.IndV K.subtype ρψ) : ℂ) := by
      rw [hψeq, Section1.inducedCF_eq_representation_character K ρψ,
        Section1.degree_representation_character]
    have hcast :
        (Module.finrank ℂ (Representation.IndV K.subtype ρψ) : ℂ) =
          (Subgroup.index K : ℂ) :=
      hdeg_ind_rep.symm.trans hdeg_ind
    exact_mod_cast hcast
  have hnθ_eq_d : nθ = d := by
    have hcast : (nθ : ℂ) = (d : ℂ) := by
      simpa [hθeq, Section1.degree_representation_character,
        Module.finrank_fin_fun] using hθdeg
    exact_mod_cast hcast
  simpa [hnθ_eq_d, hfinrank_ind_eq_index] using hnθ_le_ind


public theorem theorem_9_8_case_a_underlying_constituent_degree_le_barU_of_H0Cprime_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q a u dθ : ℕ)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Cprime = (_root_.commutator C).map C.subtype →
          Section1.IsIrreducibleCharacterOnGroup θ →
            ¬ Section1.subgroupInKernel' θ
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
            Section1.subgroupInKernel' θ
              (((H0 ⊔ Cprime).subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
            Section1.degree θ = (dθ : ℂ) →
              dθ ≤ u := by
  classical
  intro hcase hBarU hCprimeEq hθirr _hθnotMF hθkerH0Cprime hθdeg
  let D : Subgroup G := ambientDerivedSubgroup M
  let Dm : Subgroup M := D.subgroupOf M
  let HC : Subgroup G := MF ⊔ C
  let K : Subgroup Dm := (HC.subgroupOf M).subgroupOf Dm
  let A : Subgroup Dm := ((H0 ⊔ Cprime).subgroupOf M).subgroupOf Dm
  rcases exists_irreducible_constituent_of_subgroupRestriction_sec9 K hθirr with
    ⟨ψ, hψirr, hψinner⟩
  have hψkerA : Section1.subgroupInKernel' ψ (A.subgroupOf K) :=
    subgroupInKernel'_constituent_of_subgroupRestriction_kernel_sec9
      K A hθirr (by simpa [D, Dm, A] using hθkerH0Cprime) hψirr
      (by simpa [D, Dm, HC, K] using hψinner)
  have hcomm_le : _root_.commutator K ≤ A.subgroupOf K := by
    dsimp [K, A, Dm, D, HC]
    exact theorem_9_8_HC_commutator_le_H0Cprime_subgroupOf_case_a_sec9
      M MF U W1 W2 H0 C Cprime p q a hcase hCprimeEq
  have hψkerComm :
      Section1.subgroupInKernel' ψ (_root_.commutator K) := by
    intro x
    exact hψkerA ⟨x.1, hcomm_le x.2⟩
  have hψdeg : Section1.degree ψ = (1 : ℂ) :=
    degree_eq_one_of_irreducible_subgroupInKernel_commutator_sec9
      hψirr hψkerComm
  have hdeg_le_index :
      dθ ≤ Subgroup.index K :=
    irreducible_degree_nat_le_induced_linear_index_of_inner_sec9 K
      hθirr hψirr hψdeg (by simpa [D, Dm, HC, K] using hψinner)
      (by simpa [D, Dm] using hθdeg)
  have hidx :
      Subgroup.index K = u := by
    simpa [D, Dm, HC, K, Subgroup.relIndex] using
      theorem_9_8_HC_subgroupOf_ambientDerived_relIndex_eq_u_sec9
        M MF U W1 W2 H0 C p q a u hcase hBarU
  exact hdeg_le_index.trans_eq hidx

@[expose] public noncomputable def quotientInfSupEquiv_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 HC H0C : Subgroup G)
    [(H0.subgroupOf MF).Normal]
    [(H0C.subgroupOf HC).Normal]
    (hMFHC : MF ≤ HC)
    (hH0CinfMF : H0C ⊓ MF = H0)
    (hsup : H0C.subgroupOf HC ⊔ MF.subgroupOf HC = ⊤) :
    (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) := by
  classical
  let φ : MF →* HC ⧸ H0C.subgroupOf HC :=
    (QuotientGroup.mk' (H0C.subgroupOf HC)).comp (Subgroup.inclusion hMFHC)
  have hφker : φ.ker = H0.subgroupOf MF := by
    ext x
    constructor
    · intro hx
      change φ x = 1 at hx
      have hxH0C : (x : G) ∈ H0C := by
        have hxH0Cs :
            Subgroup.inclusion hMFHC x ∈ H0C.subgroupOf HC :=
          (QuotientGroup.eq_one_iff (N := H0C.subgroupOf HC)
            (x := Subgroup.inclusion hMFHC x)).1 hx
        simpa [Subgroup.mem_subgroupOf] using hxH0Cs
      have hxinf : (x : G) ∈ H0C ⊓ MF := ⟨hxH0C, x.property⟩
      have hxH0 : (x : G) ∈ H0 := by
        rw [← hH0CinfMF]
        exact hxinf
      simpa [Subgroup.mem_subgroupOf] using hxH0
    · intro hx
      change φ x = 1
      apply (QuotientGroup.eq_one_iff (N := H0C.subgroupOf HC)
        (x := Subgroup.inclusion hMFHC x)).2
      have hxH0 : (x : G) ∈ H0 := by
        simpa [Subgroup.mem_subgroupOf] using hx
      have hxinf : (x : G) ∈ H0C ⊓ MF := by
        rw [hH0CinfMF]
        exact hxH0
      simpa [Subgroup.mem_subgroupOf] using hxinf.1
  have hφsurj : Function.Surjective φ := by
    intro y
    rcases QuotientGroup.mk'_surjective (H0C.subgroupOf HC) y with ⟨h, rfl⟩
    have hmem : h ∈ H0C.subgroupOf HC ⊔ MF.subgroupOf HC := by
      rw [hsup]
      trivial
    rcases (Subgroup.mem_sup_of_normal_left
        (s := H0C.subgroupOf HC) (t := MF.subgroupOf HC) (x := h)).1 hmem with
      ⟨a, ha, b, hb, hab⟩
    let bMF : MF := ⟨(b : G), by
      simpa [Subgroup.mem_subgroupOf] using hb⟩
    refine ⟨bMF, ?_⟩
    have hqeq :
        QuotientGroup.mk' (H0C.subgroupOf HC) h =
          QuotientGroup.mk' (H0C.subgroupOf HC) b := by
      rw [← hab]
      simp [ha]
    have hb_incl : Subgroup.inclusion hMFHC bMF = b := by
      apply Subtype.ext
      rfl
    change QuotientGroup.mk' (H0C.subgroupOf HC)
        (Subgroup.inclusion hMFHC bMF) =
      QuotientGroup.mk' (H0C.subgroupOf HC) h
    rw [hb_incl]
    exact hqeq.symm
  haveI : φ.ker.Normal := MonoidHom.normal_ker φ
  exact (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)

public theorem theorem_9_8_H0C_subgroupOf_HC_relIndex_eq_p_pow_q_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      ((H0 ⊔ C).subgroupOf M).relIndex ((MF ⊔ C).subgroupOf M) = p ^ q := by
  classical
  intro hcase
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  have hHC_le_M : HC ≤ M := by
    dsimp [HC]
    exact (theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase).trans
      (section12_ambientDerivedSubgroup_le (E := M))
  have hH0CnormalHC : (H0C.subgroupOf HC).Normal := by
    dsimp [H0C, HC]
    exact theorem_9_8_H0C_normal_HC_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase
  have hH0normalMF : (H0.subgroupOf MF).Normal :=
    case_9_7_a_H0_normal_MF_sec9 hcase
  letI : (H0.subgroupOf MF).Normal := hH0normalMF
  letI : (H0C.subgroupOf HC).Normal := hH0CnormalHC
  have hH0CinfMF : H0C ⊓ MF = H0 := by
    dsimp [H0C]
    rcases hcase with ⟨h92, hH0MF, hC, hpprime, _hqprime, hpData, _hrest⟩
    exact theorem_9_H0C_inf_MF_eq_H0_source_core_sec9
      M MF U W1 W2 H0 C p q h92 hH0MF hC hpprime hpData
  have hsup : H0C.subgroupOf HC ⊔ MF.subgroupOf HC = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := H0C) (A' := MF) (B := HC)]
    · apply Subgroup.subgroupOf_eq_top.2
      dsimp [H0C, HC]
      exact sup_le
        (show MF ≤ (H0 ⊔ C) ⊔ MF from le_sup_right)
        (show C ≤ (H0 ⊔ C) ⊔ MF from le_sup_right.trans le_sup_left)
    · dsimp [H0C, HC]
      exact sup_le_sup (case_9_7_a_H0_le_MF_sec9 hcase) le_rfl
    · dsimp [HC]
      exact le_sup_left
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  have hcard :
      Nat.card (HC ⧸ H0C.subgroupOf HC) =
        Nat.card (MF ⧸ H0.subgroupOf MF) := by
    exact Nat.card_congr e.symm.toEquiv
  rw [Subgroup.relIndex_subgroupOf (H := H0C) (K := HC) (L := M) hHC_le_M]
  change Nat.card (HC ⧸ H0C.subgroupOf HC) = p ^ q
  rw [hcard]
  exact case_9_7_a_quotient_cardinality_sec9 hcase

public theorem theorem_9_8_H0C_subgroupOf_ambientDerived_relIndex_eq_p_pow_q_mul_u_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        ((H0 ⊔ C).subgroupOf M).relIndex
          ((ambientDerivedSubgroup M).subgroupOf M) = p ^ q * u := by
  intro hcase hBarU
  let D : Subgroup G := ambientDerivedSubgroup M
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  have hHC_le_D : HC ≤ D := by
    dsimp [HC, D]
    exact theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase
  have hH0C_le_HC : H0C ≤ HC := by
    dsimp [H0C, HC]
    exact sup_le_sup (case_9_7_a_H0_le_MF_sec9 hcase) le_rfl
  have hH0Cm_le_HCm :
      H0C.subgroupOf M ≤ HC.subgroupOf M := by
    intro x hx
    exact hH0C_le_HC hx
  have hHCm_le_Dm :
      HC.subgroupOf M ≤ D.subgroupOf M := by
    intro x hx
    exact hHC_le_D hx
  have hH0C_HC :
      (H0C.subgroupOf M).relIndex (HC.subgroupOf M) = p ^ q := by
    dsimp [H0C, HC]
    exact theorem_9_8_H0C_subgroupOf_HC_relIndex_eq_p_pow_q_sec9
      M MF U W1 W2 H0 C p q a hcase
  have hHC_D :
      (HC.subgroupOf M).relIndex (D.subgroupOf M) = u := by
    dsimp [HC, D]
    exact theorem_9_8_HC_subgroupOf_ambientDerived_relIndex_eq_u_sec9
      M MF U W1 W2 H0 C p q a u hcase hBarU
  have hmul :
      (H0C.subgroupOf M).relIndex (HC.subgroupOf M) *
          (HC.subgroupOf M).relIndex (D.subgroupOf M) =
        (H0C.subgroupOf M).relIndex (D.subgroupOf M) :=
    Subgroup.relIndex_mul_relIndex
      (H0C.subgroupOf M) (HC.subgroupOf M) (D.subgroupOf M)
      hH0Cm_le_HCm hHCm_le_Dm
  simpa [D, H0C, hH0C_HC, hHC_D] using hmul.symm

private theorem quotientInfSupEquiv_symm_conj_eq_mulAut_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 HC H0C : Subgroup G)
    [(H0.subgroupOf MF).Normal]
    [(H0C.subgroupOf HC).Normal]
    (hMFHC : MF ≤ HC)
    (hH0CinfMF : H0C ⊓ MF = H0)
    (hsup : H0C.subgroupOf HC ⊔ MF.subgroupOf HC = ⊤)
    (u : G)
    (hconjMF : ∀ h : MF, u * (h : G) * u⁻¹ ∈ MF)
    (hconjH0C : ∀ h : H0C, u * (h : G) * u⁻¹ ∈ H0C)
    (hconjHC : ∀ h : HC, u * (h : G) * u⁻¹ ∈ HC)
    (β : MulAut (MF ⧸ H0.subgroupOf MF))
    (hβ : ∀ h : MF,
      β (QuotientGroup.mk' (H0.subgroupOf MF) h) =
        QuotientGroup.mk' (H0.subgroupOf MF) ⟨u * (h : G) * u⁻¹, hconjMF h⟩)
    (h : HC) :
    let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
      quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
    e.symm
        (QuotientGroup.mk' (H0C.subgroupOf HC)
          ⟨u * (h : G) * u⁻¹, hconjHC h⟩) =
      β (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) h)) := by
  classical
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
  let y : HC ⧸ H0C.subgroupOf HC := QuotientGroup.mk' (H0C.subgroupOf HC) h
  rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) (e.symm y) with
    ⟨m, hm⟩
  have hmy :
      QuotientGroup.mk' (H0C.subgroupOf HC) (Subgroup.inclusion hMFHC m) = y := by
    calc
      QuotientGroup.mk' (H0C.subgroupOf HC) (Subgroup.inclusion hMFHC m) =
          e (QuotientGroup.mk' (H0.subgroupOf MF) m) := rfl
      _ = y := by rw [hm, MulEquiv.apply_symm_apply]
  have hhm :
      QuotientGroup.mk' (H0C.subgroupOf HC) h =
        QuotientGroup.mk' (H0C.subgroupOf HC) (Subgroup.inclusion hMFHC m) := by
    simpa [y] using hmy.symm
  have hdivH0C : (h / Subgroup.inclusion hMFHC m : HC) ∈ H0C.subgroupOf HC := by
    exact (QuotientGroup.eq_iff_div_mem).1 hhm
  have hdivH0CG : (h : G) * (m : G)⁻¹ ∈ H0C := by
    simpa [Subgroup.mem_subgroupOf, div_eq_mul_inv] using hdivH0C
  let d : H0C := ⟨(h : G) * (m : G)⁻¹, hdivH0CG⟩
  have hconjQuot :
      QuotientGroup.mk' (H0C.subgroupOf HC)
          ⟨u * (h : G) * u⁻¹, hconjHC h⟩ =
        QuotientGroup.mk' (H0C.subgroupOf HC)
          (Subgroup.inclusion hMFHC ⟨u * (m : G) * u⁻¹, hconjMF m⟩) := by
    apply (QuotientGroup.eq_iff_div_mem).2
    have hd : u * (d : G) * u⁻¹ ∈ H0C := hconjH0C d
    simpa [Subgroup.mem_subgroupOf, d, div_eq_mul_inv, mul_assoc] using hd
  apply e.injective
  calc
    e (e.symm
        (QuotientGroup.mk' (H0C.subgroupOf HC)
          ⟨u * (h : G) * u⁻¹, hconjHC h⟩)) =
        QuotientGroup.mk' (H0C.subgroupOf HC)
          ⟨u * (h : G) * u⁻¹, hconjHC h⟩ := by
          rw [MulEquiv.apply_symm_apply]
    _ = QuotientGroup.mk' (H0C.subgroupOf HC)
          (Subgroup.inclusion hMFHC ⟨u * (m : G) * u⁻¹, hconjMF m⟩) :=
          hconjQuot
    _ = e (QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨u * (m : G) * u⁻¹, hconjMF m⟩) := rfl
    _ = e (β (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) h))) := by
          rw [← hβ m, ← hm]

private theorem quotientInfSupEquiv_symm_conj_eq_finiteInternalProductMulAut_symm_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hnormalHCD : (((MF ⊔ C).subgroupOf M).subgroupOf
      ((ambientDerivedSubgroup M).subgroupOf M)).Normal)
    (x : U ⧸ C.subgroupOf U) (u : U)
    (hux : QuotientGroup.mk' (C.subgroupOf U) u = x) :
    let HC : Subgroup G := MF ⊔ C
    let H0C : Subgroup G := H0 ⊔ C
    let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
      quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
    let α : MulAut (MF ⧸ H0.subgroupOf MF) :=
      finiteInternalProductMulAut_sec9 H
        (by
          intro _i _j _hij y z _hy _hz
          exact mul_comm y z)
        hHindep hHsup (fun i => ρ i x)
    ∃ hconjHC : ∀ h : HC, (u : G) * (h : G) * (u : G)⁻¹ ∈ HC,
      ∀ h : HC,
        e.symm
            (QuotientGroup.mk' (H0C.subgroupOf HC)
              ⟨(u : G) * (h : G) * (u : G)⁻¹, hconjHC h⟩) =
          α.symm (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) h)) := by
  classical
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let D : Subgroup G := ambientDerivedSubgroup M
  let Dm : Subgroup M := D.subgroupOf M
  let HCm : Subgroup M := HC.subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  let α : MulAut (MF ⧸ H0.subgroupOf MF) :=
    finiteInternalProductMulAut_sec9 H
      (by
        intro _i _j _hij y z _hy _hz
        exact mul_comm y z)
      hHindep hHsup (fun i => ρ i x)
  rcases hconj with ⟨hqpos, _hconj⟩
  rcases finiteInternalProductMulAut_symm_eq_quotientConjAction_sec9
      H hHnorm hHindep hHsup ρ hρaction hqpos x u hux with
    ⟨hconjMF, hαsymm⟩
  have h92 := case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le (E := M)
  have hUleM : U ≤ M := hUleD.trans hDleM
  have hHCleD : HC ≤ D := by
    dsimp [HC, D]
    exact theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase
  have hHCleM : HC ≤ M := hHCleD.trans hDleM
  have hH0CleD : H0C ≤ D := by
    dsimp [H0C, D]
    exact theorem_9_H0C_le_ambientDerived_of_source_sec9
      M MF U W1 W2 H0 C q h92
        (case_9_7_a_H0_le_MF_sec9 hcase)
        (case_9_7_a_quotientCentralizerIn_sec9 hcase)
  have hH0CleM : H0C ≤ M := hH0CleD.trans hDleM
  have hH0CnormalM : (H0C.subgroupOf M).Normal := by
    dsimp [H0C]
    rcases hcase with ⟨h92', hH0MF, hCcent, hpprime, _hqprime, hpData, _hrest⟩
    exact theorem_9_H0C_normal_M_source_core_sec9
      M MF U W1 W2 H0 C p q h92' hH0MF hCcent hpprime hpData
  have hconjH0C : ∀ h : H0C, (u : G) * (h : G) * (u : G)⁻¹ ∈ H0C := by
    intro h
    let uM : M := ⟨(u : G), hUleM u.property⟩
    let hM : M := ⟨(h : G), hH0CleM h.property⟩
    let hH0CM : H0C.subgroupOf M := ⟨hM, by
      simp [H0C, hM, Subgroup.mem_subgroupOf]⟩
    have hmem :
        uM * hH0CM * uM⁻¹ ∈ H0C.subgroupOf M :=
      hH0CnormalM.conj_mem hH0CM hH0CM.property uM
    simpa [H0C, uM, hM, hH0CM, Subgroup.mem_subgroupOf, mul_assoc] using hmem
  have hconjHC : ∀ h : HC, (u : G) * (h : G) * (u : G)⁻¹ ∈ HC := by
    intro h
    let uM : M := ⟨(u : G), hUleM u.property⟩
    let uD : Dm := ⟨uM, by
      change (u : G) ∈ D
      exact hUleD u.property⟩
    let hM : M := ⟨(h : G), hHCleM h.property⟩
    let hD : Dm := ⟨hM, by
      change (h : G) ∈ D
      exact hHCleD h.property⟩
    let hHCD : HCD := ⟨hD, by
      change (h : G) ∈ HC
      exact h.property⟩
    have hmem : uD * hHCD * uD⁻¹ ∈ HCD :=
      hnormalHCD.conj_mem hHCD hHCD.property uD
    change (u : G) * (h : G) * (u : G)⁻¹ ∈ HC at hmem
    exact hmem
  refine ⟨hconjHC, ?_⟩
  intro h
  exact quotientInfSupEquiv_symm_conj_eq_mulAut_sec9
    MF H0 HC H0C le_sup_left hH0CinfMF hsup
    (u : G) hconjMF hconjH0C hconjHC α.symm hαsymm h

private theorem quotientCharacterInflation_rawCoordinateMulAction_eq_conjugateOnNormal_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hnormalHCD : (((MF ⊔ C).subgroupOf M).subgroupOf
      ((ambientDerivedSubgroup M).subgroupOf M)).Normal)
    (x : U ⧸ C.subgroupOf U) (u : U)
    (uD : (ambientDerivedSubgroup M).subgroupOf M)
    (hux : QuotientGroup.mk' (C.subgroupOf U) u = x)
    (huD : ((uD : M) : G) = (u : G))
    (f : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :
    let instAction : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    letI : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
    let HC : Subgroup G := MF ⊔ C
    let H0C : Subgroup G := H0 ⊔ C
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let HCm : Subgroup M := HC.subgroupOf M
    let HCD : Subgroup Dm := HCm.subgroupOf Dm
    letI : HCD.Normal := hnormalHCD
    let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
      quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
    let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
      fun k => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup k.down
    let θHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
      fun k => (θH k).comp e.symm.toMonoidHom
    Section1.subgroupOfClassFunction
        (Section1.subgroupOfClassFunction
          (Section1.quotientCharacterInflation H0C HC (θHC (x • f)))) =
      Section1.conjugateOnNormal HCD
        (Section1.subgroupOfClassFunction
          (Section1.subgroupOfClassFunction
            (Section1.quotientCharacterInflation H0C HC (θHC f)))) uD := by
  classical
  let instAction : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := HC.subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  letI : HCD.Normal := hnormalHCD
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun k => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup k.down
  let θHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun k => (θH k).comp e.symm.toMonoidHom
  let α : MulAut (MF ⧸ H0.subgroupOf MF) :=
    finiteInternalProductMulAut_sec9 H
      (by
        intro _i _j _hij y z _hy _hz
        exact mul_comm y z)
      hHindep hHsup (fun i => ρ i x)
  rcases quotientInfSupEquiv_symm_conj_eq_finiteInternalProductMulAut_symm_sec9
      M MF U W1 W2 H0 C p q a H hHnorm hHindep hHsup ρ
      hρaction hconj hH0CinfMF hsup hcase hnormalHCD x u hux with
    ⟨hconjHC, hquot⟩
  have hraw :
      θH (x • f) = (θH f).comp α.symm.toMonoidHom := by
    dsimp [θH, α]
    exact componentProductLinearCharacter_rawCoordinateMulAction_sec9
      p q H hHcard hHindep hHsup ρ x f
  ext h
  let hDm : Dm := (h : HCD)
  let hM : M := hDm
  let hHC : HC := ⟨(hM : G), by
    have hhHCm : hM ∈ HCm := by
      exact h.property
    simpa [HCm, HC, hM, Subgroup.mem_subgroupOf] using hhHCm⟩
  let hConjHCByU : HC :=
    ⟨(u : G) * (hHC : G) * (u : G)⁻¹, hconjHC hHC⟩
  let hConjHCD : HCD :=
    ⟨uD * (h : Dm) * uD⁻¹, hnormalHCD.conj_mem h h.property uD⟩
  let hConjHCm : HCm := ⟨(hConjHCD : Dm), hConjHCD.property⟩
  let hConjHC : HC := ⟨((hConjHCm : M) : G), by
    exact hConjHCm.property⟩
  have hConjHC_mk :
      QuotientGroup.mk' (H0C.subgroupOf HC) hConjHC =
        QuotientGroup.mk' (H0C.subgroupOf HC) hConjHCByU := by
    congr 1
    ext
    simp [hConjHC, hConjHCm, hConjHCD, hConjHCByU, hHC, hDm, hM, huD, mul_assoc]
  have hunit :
      θHC (x • f) (QuotientGroup.mk' (H0C.subgroupOf HC) hHC) =
        θHC f (QuotientGroup.mk' (H0C.subgroupOf HC) hConjHC) := by
    have happ := congrArg
      (fun χ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ =>
        χ (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) hHC))) hraw
    calc
      θHC (x • f) (QuotientGroup.mk' (H0C.subgroupOf HC) hHC) =
          θH (x • f) (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) hHC)) := by
            rfl
      _ = θH f (α.symm
            (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) hHC))) := by
            simpa using happ
      _ = θH f
            (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) hConjHC)) := by
            rw [hConjHC_mk, ← hquot hHC]
      _ = θHC f (QuotientGroup.mk' (H0C.subgroupOf HC) hConjHC) := by
            rfl
  simpa [Section1.subgroupOfClassFunction, Section1.quotientCharacterInflation,
    Section1.conjugateOnNormal, θHC, θH, hHC, hDm, hM, hConjHC, hConjHCm,
    hConjHCD, huD, mul_assoc] using congrArg Units.val hunit

private theorem inducedCF_conjugateOnNormal_sec9
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [hH : H.Normal]
    (theta : Section1.ClassFunction H) (g : G) :
    Section1.inducedCF H (Section1.conjugateOnNormal H theta g) =
      Section1.inducedCF H theta := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  funext y
  let f : G → ℂ := fun z =>
    if hz : z * y * z⁻¹ ∈ H then
      theta ⟨z * y * z⁻¹, hz⟩
    else
      0
  unfold Section1.inducedCF Section1.inducedClassFunction
  have hsum :
      ∑ x : G,
          (if hx : x * y * x⁻¹ ∈ H then
            Section1.conjugateOnNormal H theta g ⟨x * y * x⁻¹, hx⟩
          else
            0) =
        ∑ x : G, f (g * x) := by
    refine Finset.sum_congr rfl ?_
    intro x _hx
    have hmem :
        x * y * x⁻¹ ∈ H ↔ g * x * y * (x⁻¹ * g⁻¹) ∈ H := by
      constructor
      · intro hxy
        have hgxy : g * (x * y * x⁻¹) * g⁻¹ ∈ H := hH.conj_mem _ hxy g
        simpa [mul_assoc] using hgxy
      · intro hgxy
        have hgxy' : g⁻¹ * (g * x * y * (x⁻¹ * g⁻¹)) * (g⁻¹)⁻¹ ∈ H :=
          hH.conj_mem _ hgxy g⁻¹
        simpa [mul_assoc] using hgxy'
    by_cases hxH : x * y * x⁻¹ ∈ H
    · have hgxH : g * x * y * (x⁻¹ * g⁻¹) ∈ H := hmem.mp hxH
      have hxH' : x * (y * x⁻¹) ∈ H := by
        simpa [mul_assoc] using hxH
      have hgxH' : g * (x * (y * (x⁻¹ * g⁻¹))) ∈ H := by
        simpa [mul_assoc] using hgxH
      rw [show f (g * x) =
        if h : g * (x * (y * (x⁻¹ * g⁻¹))) ∈ H then
          theta ⟨g * (x * (y * (x⁻¹ * g⁻¹))), h⟩
        else 0 by simp [f, mul_assoc]]
      simp [Section1.conjugateOnNormal, hxH', hgxH', mul_assoc]
    · have hgxH : ¬ g * x * y * (x⁻¹ * g⁻¹) ∈ H := by
        exact fun h => hxH (hmem.mpr h)
      have hxH' : ¬ x * (y * x⁻¹) ∈ H := by
        simpa [mul_assoc] using hxH
      have hgxH' : ¬ g * (x * (y * (x⁻¹ * g⁻¹))) ∈ H := by
        simpa [mul_assoc] using hgxH
      rw [show f (g * x) =
        if h : g * (x * (y * (x⁻¹ * g⁻¹))) ∈ H then
          theta ⟨g * (x * (y * (x⁻¹ * g⁻¹))), h⟩
        else 0 by simp [f, mul_assoc]]
      simp [hxH', hgxH', mul_assoc]
  calc
    (Nat.card H : ℂ)⁻¹ *
        ∑ x : G,
          (if hx : x * y * x⁻¹ ∈ H then
            Section1.conjugateOnNormal H theta g ⟨x * y * x⁻¹, hx⟩
          else
            0)
        =
      (Nat.card H : ℂ)⁻¹ * ∑ x : G, f (g * x) := by
          rw [hsum]
    _ = (Nat.card H : ℂ)⁻¹ * ∑ z : G, f z := by
          congr 1
          simpa using (Equiv.sum_comp (Equiv.mulLeft g) f)
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ z : G,
          (if hz : z * y * z⁻¹ ∈ H then
            theta ⟨z * y * z⁻¹, hz⟩
          else
            0) := by
          rfl


private theorem conjugateOnNormal_inducedCF_eq_of_source_conjugation_sec9
    {G : Type u} [Group G] [Finite G]
    (D : Subgroup G) [hD : D.Normal]
    (H : Subgroup D) [Finite H]
    (θ η : Section1.ClassFunction H) (g : G)
    (hgH : ∀ d : D,
      d ∈ H ↔
        (⟨g * (d : G) * g⁻¹, hD.conj_mem (d : G) d.property g⟩ : D) ∈ H)
    (hθη : ∀ h : H,
      θ ⟨⟨g * ((h : D) : G) * g⁻¹,
          hD.conj_mem ((h : D) : G) (h : D).property g⟩,
        (hgH (h : D)).mp h.property⟩ = η h) :
    Section1.conjugateOnNormal D (Section1.inducedCF H θ) g =
      Section1.inducedCF H η := by
  classical
  letI : Fintype D := Fintype.ofFinite D
  funext y
  let c : D ≃ D :=
    { toFun := fun z =>
        ⟨g * (z : G) * g⁻¹, hD.conj_mem (z : G) z.property g⟩
      invFun := fun z =>
        ⟨g⁻¹ * (z : G) * g, by
          simpa only [inv_inv] using hD.conj_mem (z : G) z.property g⁻¹⟩
      left_inv := by
        intro z
        ext
        simp [mul_assoc]
      right_inv := by
        intro z
        ext
        simp [mul_assoc] }
  let gy : D := ⟨g * (y : G) * g⁻¹, hD.conj_mem (y : G) y.property g⟩
  let F : D → ℂ := fun x =>
    if hx : x * gy * x⁻¹ ∈ H then θ ⟨x * gy * x⁻¹, hx⟩ else 0
  let R : D → ℂ := fun z =>
    if hz : z * y * z⁻¹ ∈ H then η ⟨z * y * z⁻¹, hz⟩ else 0
  unfold Section1.conjugateOnNormal Section1.inducedCF Section1.inducedClassFunction
  have hsum : (∑ x : D, F x) = ∑ z : D, R z := by
    calc
      (∑ x : D, F x) = ∑ z : D, F (c z) := by
        simpa using (Equiv.sum_comp c F).symm
      _ = ∑ z : D, R z := by
        refine Finset.sum_congr rfl ?_
        intro z _hzmem
        have harg : c z * gy * (c z)⁻¹ =
            (⟨g * (((z * y * z⁻¹ : D) : G)) * g⁻¹,
              hD.conj_mem (((z * y * z⁻¹ : D) : G))
                (z * y * z⁻¹ : D).property g⟩ : D) := by
          ext
          simp [c, gy, mul_assoc]
        by_cases hzH : z * y * z⁻¹ ∈ H
        · have hcgH : c z * gy * (c z)⁻¹ ∈ H := by
            simpa [harg] using (hgH (z * y * z⁻¹)).mp hzH
          have hθ := hθη ⟨z * y * z⁻¹, hzH⟩
          simp [F, R, hzH, hcgH]
          simpa [harg] using hθ
        · have hcgH : ¬ c z * gy * (c z)⁻¹ ∈ H := by
            intro hbad
            exact hzH ((hgH (z * y * z⁻¹)).mpr (by
              simpa [harg] using hbad))
          simp [F, R, hzH, hcgH]
  simpa [gy, F, R] using hsum

private theorem
    conjugateOnNormal_inducedCF_eq_of_subgroupOf_source_conjugation_sec9
    {G : Type u} [Group G] [Finite G]
    (D K : Subgroup G) [hD : D.Normal] [hK : K.Normal]
    [Finite (K.subgroupOf D)]
    (θ η : Section1.ClassFunction (K.subgroupOf D)) (g : G)
    (hθη : ∀ h : K.subgroupOf D,
      θ ⟨⟨g * ((h : D) : G) * g⁻¹,
          hD.conj_mem ((h : D) : G) (h : D).property g⟩,
        by
          change g * ((h : D) : G) * g⁻¹ ∈ K
          exact hK.conj_mem ((h : D) : G) h.property g⟩ = η h) :
    Section1.conjugateOnNormal D
        (Section1.inducedCF (K.subgroupOf D) θ) g =
      Section1.inducedCF (K.subgroupOf D) η := by
  classical
  refine conjugateOnNormal_inducedCF_eq_of_source_conjugation_sec9
    D (K.subgroupOf D) θ η g ?_ ?_
  · intro d
    constructor
    · intro hd
      change g * (d : G) * g⁻¹ ∈ K
      exact hK.conj_mem (d : G) hd g
    · intro hd
      have hback :
          g⁻¹ * (g * (d : G) * g⁻¹) * (g⁻¹)⁻¹ ∈ K :=
        hK.conj_mem (g * (d : G) * g⁻¹)
          (by simpa [Subgroup.mem_subgroupOf] using hd) g⁻¹
      change (d : G) ∈ K
      simpa [mul_assoc] using hback
  · intro h
    exact hθη h

private theorem induced_eq_of_rawCoordinateMulAction_orbitRel_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hnormalHCD : (((MF ⊔ C).subgroupOf M).subgroupOf
      ((ambientDerivedSubgroup M).subgroupOf M)).Normal)
    (k l : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hrel :
      let instAction : MulAction (U ⧸ C.subgroupOf U)
          (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
        rawCoordinateMulAction_sec9 p q H hHcard ρ
      letI : MulAction (U ⧸ C.subgroupOf U)
          (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
      MulAction.orbitRel (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) k l) :
    let instAction : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    letI : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
    let HC : Subgroup G := MF ⊔ C
    let H0C : Subgroup G := H0 ⊔ C
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let HCm : Subgroup M := HC.subgroupOf M
    let HCD : Subgroup Dm := HCm.subgroupOf Dm
    letI : HCD.Normal := hnormalHCD
    let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
      quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
    let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
      fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
    let θHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
      fun f => (θH f).comp e.symm.toMonoidHom
    let ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        Section1.ClassFunction HC :=
      fun f => Section1.quotientCharacterInflation H0C HC (θHC f)
    let ψ : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        Section1.ClassFunction HCm :=
      fun f => Section1.subgroupOfClassFunction (ψHC f)
    let θ : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        Section1.ClassFunction Dm :=
      fun f => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ f))
    θ k = θ l := by
  classical
  let instAction : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let D : Subgroup G := ambientDerivedSubgroup M
  let Dm : Subgroup M := D.subgroupOf M
  let HCm : Subgroup M := HC.subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  letI : HCD.Normal := hnormalHCD
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  let ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction HC :=
    fun f => Section1.quotientCharacterInflation H0C HC (θHC f)
  let ψ : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction HCm :=
    fun f => Section1.subgroupOfClassFunction (ψHC f)
  let θ : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction Dm :=
    fun f => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ f))
  have h92 := case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
  rw [MulAction.orbitRel_apply] at hrel
  rcases MulAction.mem_orbit_iff.mp hrel with ⟨x, hx⟩
  obtain ⟨u, hux⟩ := QuotientGroup.mk'_surjective (C.subgroupOf U) x
  let uM : M := ⟨(u : G), (hUleD.trans section12_ambientDerivedSubgroup_le) u.property⟩
  let uD : Dm := ⟨uM, by
    simpa [D, Dm, uM, Subgroup.mem_subgroupOf] using hUleD u.property⟩
  have huD : ((uD : M) : G) = (u : G) := rfl
  have hψconj :
      Section1.subgroupOfClassFunction
          (Section1.subgroupOfClassFunction (ψHC k)) =
      Section1.conjugateOnNormal HCD
          (Section1.subgroupOfClassFunction
            (Section1.subgroupOfClassFunction (ψHC l))) uD := by
    rw [← hx]
    simpa [instAction, HC, H0C, D, Dm, HCm, HCD, e, θH, θHC, ψHC, ψ] using
      quotientCharacterInflation_rawCoordinateMulAction_eq_conjugateOnNormal_sec9
        M MF U W1 W2 H0 C p q a H hHcard hHnorm hHindep hHsup ρ
        hρaction hconj hH0CinfMF hsup hcase hnormalHCD x u uD hux huD l
  have hθHCD :
      θ k = θ l := by
    dsimp [θ, ψ]
    rw [hψconj]
    exact inducedCF_conjugateOnNormal_sec9 HCD
      (Section1.subgroupOfClassFunction (Section1.subgroupOfClassFunction (ψHC l))) uD
  simpa [instAction, HC, H0C, D, Dm, HCm, HCD, e, θH, θHC, ψHC, ψ, θ] using
    hθHCD

private theorem rawCoordinate_eq_of_restricted_quotientCharacterInflation_eq_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (ψHC =
          (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
           let HC : Subgroup G := MF ⊔ C
           let H0C : Subgroup G := H0 ⊔ C
           let hMFHC : MF ≤ HC := le_sup_left
           let e : (MF ⧸ H0.subgroupOf MF) ≃*
               (HC ⧸ H0C.subgroupOf HC) :=
             quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
           let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
             fun f =>
               componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
                 f.down
           let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
             fun f => (θH f).comp e.symm.toMonoidHom
           fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
        ∀ k l : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q,
          let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
          Section1.subgroupOfClassFunction (T := Dm)
              (Section1.subgroupOfClassFunction (T := M) (ψHC k)) =
            Section1.subgroupOfClassFunction (T := Dm)
              (Section1.subgroupOfClassFunction (T := M) (ψHC l)) →
          k = l := by
  classical
  intro hcase hψformula k l
  dsimp only
  intro hres
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let D : Subgroup G := ambientDerivedSubgroup M
  let Dm : Subgroup M := D.subgroupOf M
  let HCm : Subgroup M := HC.subgroupOf M
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  have hHCleD : HC ≤ D := by
    dsimp [HC, D]
    exact theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase
  have hHCleM : HC ≤ M :=
    hHCleD.trans (section12_ambientDerivedSubgroup_le (E := M))
  have hHCm_le_Dm : HCm ≤ Dm := by
    intro x hx
    change ((x : M) : G) ∈ D
    exact hHCleD (by simpa [HCm, HC, Subgroup.mem_subgroupOf] using hx)
  have hres' :
      Section1.subgroupOfClassFunction (T := Dm)
          (Section1.subgroupOfClassFunction (T := M) (ψHC k)) =
        Section1.subgroupOfClassFunction (T := Dm)
          (Section1.subgroupOfClassFunction (T := M) (ψHC l)) := by
    simpa [D, Dm, HCm] using hres
  have hψM :
      Section1.subgroupOfClassFunction (T := M) (ψHC k) =
        Section1.subgroupOfClassFunction (T := M) (ψHC l) :=
    subgroupOfClassFunction_injective_sec9 (G := M) (H := HCm) (T := Dm)
      hHCm_le_Dm hres'
  have hψ :
      ψHC k = ψHC l :=
    subgroupOfClassFunction_injective_sec9 (G := G) (H := HC) (T := M)
      hHCleM hψM
  rw [hψformula] at hψ
  have hθHC : θHC k = θHC l :=
    Section1.quotientCharacterInflation_injective H0C HC hψ
  have hθH : θH k = θH l := by
    ext x
    have hval := congrArg
      (fun χ : (HC ⧸ H0C.subgroupOf HC) →* ℂˣ => χ (e x)) hθHC
    simpa [θHC] using congrArg Units.val hval
  have hdown :
      k.down = l.down :=
    componentProductLinearCharacter_injective_sec9
      p q H hHcard hHindep hHsup (by simpa [θH] using hθH)
  rcases k with ⟨kdown⟩
  rcases l with ⟨ldown⟩
  dsimp at hdown
  cases hdown
  rfl

private theorem subgroupOfClassFunction_isClassFunction_sec9
    {G : Type u} [Group G] {H T : Subgroup G}
    {θ : Section1.ClassFunction H}
    (hθ : Section1.IsClassFunction θ) :
    Section1.IsClassFunction (Section1.subgroupOfClassFunction (T := T) θ) := by
  intro x g
  unfold Section1.subgroupOfClassFunction
  let xH : H := ⟨(x : T), x.property⟩
  let gH : H := ⟨(g : T), g.property⟩
  let lhsH : H :=
    ⟨((x * g * x⁻¹ : H.subgroupOf T) : T),
      (x * g * x⁻¹ : H.subgroupOf T).property⟩
  change θ lhsH = θ gH
  have hlhs : lhsH = xH * gH * xH⁻¹ := by
    apply Subtype.ext
    rfl
  rw [hlhs]
  exact hθ xH gH

private theorem conjugateOnNormal_mul_left_of_mem_sec9
    {G : Type u} [Group G] {H : Subgroup G} [H.Normal]
    (θ : Section1.ClassFunction H)
    (hθ : Section1.IsClassFunction θ)
    {k w : G} (hk : k ∈ H) :
    Section1.conjugateOnNormal H θ (k * w) =
      Section1.conjugateOnNormal H θ w := by
  ext h
  let y : H := ⟨w * (h : G) * w⁻¹, (inferInstance : H.Normal).conj_mem h h.property w⟩
  let z : H := ⟨(k * w) * (h : G) * (k * w)⁻¹,
    (inferInstance : H.Normal).conj_mem h h.property (k * w)⟩
  have hz : z = ⟨k, hk⟩ * y * (⟨k, hk⟩ : H)⁻¹ := by
    apply Subtype.ext
    simp [z, y, mul_assoc]
  have hclass := hθ ⟨k, hk⟩ y
  change θ z = θ y
  rw [hz]
  exact hclass

private theorem rawCoordinateMulAction_eq_self_of_conjugateOnNormal_fixed_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (ψHC =
          (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
           let HC : Subgroup G := MF ⊔ C
           let H0C : Subgroup G := H0 ⊔ C
           let hMFHC : MF ≤ HC := le_sup_left
           let e : (MF ⧸ H0.subgroupOf MF) ≃*
               (HC ⧸ H0C.subgroupOf HC) :=
             quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
           let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
             fun f =>
               componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
                 f.down
           let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
             fun f => (θH f).comp e.symm.toMonoidHom
           fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
        ∀ hnormalHCD : (((MF ⊔ C).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).Normal,
          letI : (((MF ⊔ C).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hnormalHCD
          ∀ (x : U ⧸ C.subgroupOf U) (u : U)
            (uD : (ambientDerivedSubgroup M).subgroupOf M),
            QuotientGroup.mk' (C.subgroupOf U) u = x →
              ((uD : M) : G) = (u : G) →
                ∀ k : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q,
                  Section1.conjugateOnNormal
                      ((((MF ⊔ C).subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M)))
                      (Section1.subgroupOfClassFunction
                        (Section1.subgroupOfClassFunction (ψHC k))) uD =
                    Section1.subgroupOfClassFunction
                      (Section1.subgroupOfClassFunction (ψHC k)) →
                  letI : MulAction (U ⧸ C.subgroupOf U)
                      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
                    rawCoordinateMulAction_sec9 p q H hHcard ρ
                  x • k = k := by
  classical
  intro hcase hψformula hnormalHCD x u uD hux huD k hfix
  let instAction : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := HC.subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  letI : HCD.Normal := hnormalHCD
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  have hψconj :
      Section1.subgroupOfClassFunction (T := Dm)
          (Section1.subgroupOfClassFunction (T := M) (ψHC (x • k))) =
        Section1.conjugateOnNormal HCD
          (Section1.subgroupOfClassFunction (T := Dm)
            (Section1.subgroupOfClassFunction (T := M) (ψHC k))) uD := by
    rw [hψformula]
    simpa [instAction, HC, H0C, Dm, HCm, HCD, e, θH, θHC] using
      quotientCharacterInflation_rawCoordinateMulAction_eq_conjugateOnNormal_sec9
        M MF U W1 W2 H0 C p q a H hHcard hHnorm hHindep hHsup ρ
        hρaction hconj hH0CinfMF hsup hcase hnormalHCD x u uD hux huD k
  have hres :
      Section1.subgroupOfClassFunction (T := Dm)
          (Section1.subgroupOfClassFunction (T := M) (ψHC (x • k))) =
        Section1.subgroupOfClassFunction (T := Dm)
          (Section1.subgroupOfClassFunction (T := M) (ψHC k)) := by
    exact hψconj.trans (by simpa [HC, Dm, HCm, HCD] using hfix)
  simpa [instAction, HC, H0C, Dm, HCm, HCD] using
    rawCoordinate_eq_of_restricted_quotientCharacterInflation_eq_sec9
      M MF U W1 W2 H0 C p q a H hHcard hHindep hHsup hH0CinfMF hsup
      ψHC hcase hψformula (x • k) k hres

private theorem induced_eq_imp_conjugateOrbitConj_of_irreducible_sec9
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    {φ θ : Section1.ClassFunction H}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hθ : Section1.IsIrreducibleCharacterOnGroup θ)
    (hInd : Section1.inducedCF H φ = Section1.inducedCF H θ) :
    ∃ i : Section1.conjugateOrbitIndex H θ,
      φ = Section1.conjugateOrbitConj H θ i := by
  classical
  rcases hφ with ⟨nφ, φRep, hφirr, hφeq⟩
  rcases hθ with ⟨nθ, θRep, hθirr, hθeq⟩
  subst φ
  subst θ
  exact Section1.proposition_1_5_c_induced_eq_imp_conjugate_orbit_canonical
    H φRep θRep hφirr hθirr hInd


private theorem theorem_9_8_H0C_linear_candidate_Xtheta_thetaHC_concrete_fields_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      ∃ hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF),
        letI : IsMulCommutative (MF ⧸ H0.subgroupOf MF) := hcomm
        let HC : Subgroup G := MF ⊔ C
        let H0C : Subgroup G := H0 ⊔ C
        ∃ hnormalH0C : (H0C.subgroupOf HC).Normal,
          letI : (H0C.subgroupOf HC).Normal := hnormalH0C
          ∃ hH0CinfMF : H0C ⊓ MF = H0,
            ∃ hsup : H0C.subgroupOf HC ⊔ MF.subgroupOf HC = ⊤,
              let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
              let hMFHC : MF ≤ HC := le_sup_left
              let e : (MF ⧸ H0.subgroupOf MF) ≃*
                  (HC ⧸ H0C.subgroupOf HC) :=
                quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
              let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
                fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
                  f.down
              let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
                fun f => (θH f).comp e.symm.toMonoidHom
              ∃ ψHC : κ → Section1.ClassFunction HC,
                ψHC =
                    (fun f => Section1.quotientCharacterInflation H0C HC (θHC f)) ∧
                  Function.Injective ψHC ∧
                  (∀ f : κ, Section1.IsIrreducibleCharacterOnGroup (ψHC f)) ∧
                  (∀ f : κ, Section1.degree (ψHC f) = (1 : ℂ)) ∧
                  (∀ f : κ, Section1.subgroupInKernel' (ψHC f) (H0C.subgroupOf HC)) ∧
                  ∀ f : κ, ¬ Section1.subgroupInKernel' (ψHC f) (MF.subgroupOf HC) := by
  classical
  intro hcase
  have hquotElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := by
    rcases case_9_7_a_quotient_isElementaryAbelian_sec9 hcase with
      ⟨_hnormalH0', hElem⟩
    exact hElem
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hquotElem
  let hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF) := inferInstance
  letI : IsMulCommutative (MF ⧸ H0.subgroupOf MF) := hcomm
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  have hH0CnormalHC : (H0C.subgroupOf HC).Normal := by
    dsimp [H0C, HC]
    exact theorem_9_8_H0C_normal_HC_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase
  letI : (H0C.subgroupOf HC).Normal := hH0CnormalHC
  have hH0CinfMF : H0C ⊓ MF = H0 := by
    dsimp [H0C]
    rcases hcase with ⟨h92, hH0MF, hC, hpprime, _hqprime, hpData, _hrest⟩
    exact theorem_9_H0C_inf_MF_eq_H0_source_core_sec9
      M MF U W1 W2 H0 C p q h92 hH0MF hC hpprime hpData
  have hMFHC : MF ≤ HC := by
    dsimp [HC]
    exact le_sup_left
  have hsup : H0C.subgroupOf HC ⊔ MF.subgroupOf HC = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := H0C) (A' := MF) (B := HC)]
    · apply Subgroup.subgroupOf_eq_top.2
      dsimp [H0C, HC]
      exact sup_le
        (show MF ≤ (H0 ⊔ C) ⊔ MF from le_sup_right)
        (show C ≤ (H0 ⊔ C) ⊔ MF from le_sup_right.trans le_sup_left)
    · dsimp [H0C, HC]
      exact sup_le_sup (case_9_7_a_H0_le_MF_sec9 hcase) le_rfl
    · dsimp [HC]
      exact le_sup_left
  let e : (MF ⧸ H0.subgroupOf MF) ≃*
      (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
  let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  let ψHC : κ → Section1.ClassFunction HC :=
    fun f => Section1.quotientCharacterInflation H0C HC (θHC f)
  have hqpos : 0 < q := (case_9_7_a_q_prime_sec9 hcase).pos
  have hθHinj : Function.Injective θH := by
    intro f g hfg
    have hdown :
        f.down = g.down :=
      componentProductLinearCharacter_injective_sec9 p q H hHcard hHindep hHsup hfg
    cases f
    cases g
    simp at hdown
    cases hdown
    rfl
  have hθHne : ∀ f : κ, θH f ≠ 1 := by
    intro f
    exact componentProductLinearCharacter_ne_one_sec9 p q H hHcard hHindep hHsup
      f.down ⟨0, hqpos⟩
  refine ⟨hcomm, hH0CnormalHC, hH0CinfMF, hsup, ψHC, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g hfg
    apply hθHinj
    have hθHC :
        θHC f = θHC g :=
      Section1.quotientCharacterInflation_injective H0C HC hfg
    ext x
    have hval := congrArg (fun χ : (HC ⧸ H0C.subgroupOf HC) →* ℂˣ =>
      χ (e x)) hθHC
    exact congrArg Units.val (by simpa [θHC] using hval)
  · intro f
    exact Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      H0C HC (θHC f)
  · intro f
    exact Section1.quotientCharacterInflation_degree H0C HC (θHC f)
  · intro f
    exact Section1.subgroupInKernel'_quotientCharacterInflation H0C HC (θHC f)
  · intro f hkerMF
    exact hθHne f <| by
      ext x
      have hxker : ψHC f (Subgroup.inclusion hMFHC x) =
          Section1.degree (ψHC f) := by
        exact hkerMF ⟨Subgroup.inclusion hMFHC x, by
          simp [Subgroup.mem_subgroupOf]⟩
      have hqval : θH f x = 1 := by
        have hxval := hxker
        rw [Section1.quotientCharacterInflation_degree] at hxval
        have hxval' :
            ((θHC f) (QuotientGroup.mk' (H0C.subgroupOf HC)
                (Subgroup.inclusion hMFHC x)) : ℂˣ) = (1 : ℂˣ) := by
          exact Units.ext (by simpa [ψHC, Section1.quotientCharacterInflation] using hxval)
        have heq : QuotientGroup.mk' (H0C.subgroupOf HC)
              (Subgroup.inclusion hMFHC x) = e x := rfl
        have hunit : (θHC f) (e x) = 1 := by
          simpa [heq] using hxval'
        have hunit' : θH f x = 1 := by
          simpa [θHC] using hunit
        exact hunit'
      exact congrArg Units.val (by simpa using hqval)


private theorem H0CLinearCandidateXtheta_theta_orbit_entry_data_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    {ψHC : ULift.{u, 0} (Fin q → Fin (p - 1)) →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))}
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (rep : ι → ULift.{u, 0} (Fin q → Fin (p - 1))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (∀ f, Section1.IsIrreducibleCharacterOnGroup (ψHC f)) →
        (∀ f, Section1.degree (ψHC f) = (1 : ℂ)) →
          (∀ f, Section1.subgroupInKernel' (ψHC f)
            ((H0 ⊔ C).subgroupOf (MF ⊔ C))) →
          (∀ f, ¬ Section1.subgroupInKernel' (ψHC f)
            (MF.subgroupOf (MF ⊔ C))) →
            let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
            let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
            let HCD : Subgroup Dm := HCm.subgroupOf Dm
            let H0CD : Subgroup Dm := ((H0 ⊔ C).subgroupOf M).subgroupOf Dm
            let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
            ∀ hnormalHCD : HCD.Normal,
              letI : HCD.Normal := hnormalHCD
              let ψ : ι → Section1.ClassFunction HCm :=
                fun i => Section1.subgroupOfClassFunction (ψHC (rep i))
              let θ : ι → Section1.ClassFunction Dm :=
                fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
              (∀ i : ι,
                Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ i)) =
                  HCD) →
                ∀ i : ι,
                  Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                    ¬ Section1.subgroupInKernel' (θ i) MFD ∧
                    Section1.subgroupInKernel' (θ i) H0CD ∧
                    Section1.IsIrreducibleCharacterOnGroup (ψ i) ∧
                    Section1.degree (ψ i) = (1 : ℂ) := by
  classical
  intro hcase hψirr hψdeg hψkerH0C hψnotMF
  dsimp only
  intro hnormalHCD hIeq i
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let H0CD : Subgroup Dm := ((H0 ⊔ C).subgroupOf M).subgroupOf Dm
  let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (rep i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  letI : HCD.Normal := hnormalHCD
  have hHC_le_D : MF ⊔ C ≤ ambientDerivedSubgroup M :=
    theorem_9_8_HC_le_ambientDerived_of_case_a_sec9 M MF U W1 W2 H0 C p q a hcase
  have hH0C_le_HC : H0 ⊔ C ≤ MF ⊔ C :=
    sup_le_sup (case_9_7_a_H0_le_MF_sec9 hcase) le_rfl
  have hMF_le_HC : MF ≤ MF ⊔ C := le_sup_left
  have hH0C_le_D : H0 ⊔ C ≤ ambientDerivedSubgroup M :=
    theorem_9_H0C_le_ambientDerived_of_source_sec9 M MF U W1 W2 H0 C q
      (case_9_7_a_hypothesis_9_2_sec9 hcase)
      (case_9_7_a_H0_le_MF_sec9 hcase)
      (case_9_7_a_quotientCentralizerIn_sec9 hcase)
  have hH0C_le_M : H0 ⊔ C ≤ M :=
    hH0C_le_D.trans (section12_ambientDerivedSubgroup_le (E := M))
  have hMF_le_M : MF ≤ M := case_9_7_a_MF_le_M_sec9 hcase
  have hMF_le_D : MF ≤ ambientDerivedSubgroup M :=
    hMF_le_HC.trans hHC_le_D
  have hpData :
      ∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
            quotientChiefFactorData_9_6 M MF H0 W1 hp := by
    rcases hcase with
      ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, hpData, _hrest⟩
    exact hpData
  have hH0CnormalM : ((H0 ⊔ C).subgroupOf M).Normal :=
    theorem_9_H0C_normal_M_source_core_sec9 M MF U W1 W2 H0 C p q
      (case_9_7_a_hypothesis_9_2_sec9 hcase)
      (case_9_7_a_H0_le_MF_sec9 hcase)
      (case_9_7_a_quotientCentralizerIn_sec9 hcase)
      (case_9_7_a_p_prime_sec9 hcase)
      hpData
  letI : ((H0 ⊔ C).subgroupOf M).Normal := hH0CnormalM
  have hH0CDnormal : H0CD.Normal := by
    dsimp [H0CD, Dm]
    exact Section1.subgroupOf_normal_of_normal ((H0 ⊔ C).subgroupOf M)
      ((ambientDerivedSubgroup M).subgroupOf M)
  letI : H0CD.Normal := hH0CDnormal
  have hMFDnormal : MFD.Normal := by
    simpa [MFD, Dm] using
      theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
        M MF U W1 W2 H0 C p q a hcase
  letI : MFD.Normal := hMFDnormal
  have hH0CD_le_HCD : H0CD ≤ HCD := by
    intro x hx
    have hxH0C : ((x : Dm) : M) ∈ (H0 ⊔ C).subgroupOf M := by
      simpa [H0CD, Subgroup.mem_subgroupOf] using hx
    have hxH0CG : (((x : Dm) : M) : G) ∈ H0 ⊔ C := by
      simpa [Subgroup.mem_subgroupOf] using hxH0C
    have hxHCG : (((x : Dm) : M) : G) ∈ MF ⊔ C :=
      hH0C_le_HC hxH0CG
    simpa [HCD, HCm, Subgroup.mem_subgroupOf] using hxHCG
  have hMFD_le_HCD : MFD ≤ HCD := by
    intro x hx
    have hxMF : ((x : Dm) : M) ∈ MF.subgroupOf M := by
      simpa [MFD, Subgroup.mem_subgroupOf] using hx
    have hxMFG : (((x : Dm) : M) : G) ∈ MF := by
      simpa [Subgroup.mem_subgroupOf] using hxMF
    have hxHCG : (((x : Dm) : M) : G) ∈ MF ⊔ C := hMF_le_HC hxMFG
    simpa [HCD, HCm, Subgroup.mem_subgroupOf] using hxHCG
  have hH0CM_le_HCm : (H0 ⊔ C).subgroupOf M ≤ HCm := by
    intro x hx
    have hxH0CG : ((x : M) : G) ∈ H0 ⊔ C := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxHCG : ((x : M) : G) ∈ MF ⊔ C := hH0C_le_HC hxH0CG
    simpa [HCm, Subgroup.mem_subgroupOf] using hxHCG
  have hH0CM_le_Dm : (H0 ⊔ C).subgroupOf M ≤ Dm := by
    intro x hx
    have hxH0CG : ((x : M) : G) ∈ H0 ⊔ C := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxD : ((x : M) : G) ∈ ambientDerivedSubgroup M := hH0C_le_D hxH0CG
    simpa [Dm, Subgroup.mem_subgroupOf] using hxD
  have hMFM_le_HCm : MF.subgroupOf M ≤ HCm := by
    intro x hx
    have hxMFG : ((x : M) : G) ∈ MF := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxHCG : ((x : M) : G) ∈ MF ⊔ C := hMF_le_HC hxMFG
    simpa [HCm, Subgroup.mem_subgroupOf] using hxHCG
  have hMFM_le_Dm : MF.subgroupOf M ≤ Dm := by
    intro x hx
    have hxMFG : ((x : M) : G) ∈ MF := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxD : ((x : M) : G) ∈ ambientDerivedSubgroup M := hMF_le_D hxMFG
    simpa [Dm, Subgroup.mem_subgroupOf] using hxD
  have hψi_irr : Section1.IsIrreducibleCharacterOnGroup (ψ i) := by
    dsimp [ψ, HCm]
    exact isIrreducible_subgroupOfClassFunction_sec9
      (show MF ⊔ C ≤ M from
        (theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
          M MF U W1 W2 H0 C p q a hcase).trans
          (section12_ambientDerivedSubgroup_le (E := M)))
      (hψirr (rep i))
  have hψiD_irr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.subgroupOfClassFunction (T := Dm) (ψ i)) := by
    dsimp [ψ, HCm, HCD, Dm]
    exact isIrreducible_subgroupOfClassFunction_sec9 (T := Dm)
      (show (MF ⊔ C).subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M from by
        intro x hx
        change ((x : M) : G) ∈ ambientDerivedSubgroup M
        exact hHC_le_D (by simpa [Subgroup.mem_subgroupOf] using hx))
      hψi_irr
  have hθirr : Section1.IsIrreducibleCharacterOnGroup (θ i) := by
    dsimp [θ]
    exact inducedCF_isIrreducible_of_inertia_eq_self_sec9 HCD hψiD_irr (by
      simpa [ψ, θ, HCD, HCm, Dm] using hIeq i)
  have hψdeg : Section1.degree (ψ i) = (1 : ℂ) := by
    dsimp [ψ]
    rw [Section1.degree_subgroupOfClassFunction]
    exact hψdeg (rep i)
  have hθkerH0C : Section1.subgroupInKernel' (θ i) H0CD := by
    have hψiKerH0CM :
        Section1.subgroupInKernel' (ψ i)
          (((H0 ⊔ C).subgroupOf M).subgroupOf HCm) := by
      dsimp [ψ, HCm]
      exact subgroupInKernel'_subgroupOfClassFunction_sec9
        hH0C_le_M hH0C_le_HC (hψkerH0C (rep i))
    have hψiDKerH0CD :
        Section1.subgroupInKernel'
          (Section1.subgroupOfClassFunction (ψ i)) (H0CD.subgroupOf HCD) := by
      dsimp [H0CD, HCD, Dm, HCm]
      exact subgroupInKernel'_subgroupOfClassFunction_sec9
        hH0CM_le_Dm hH0CM_le_HCm hψiKerH0CM
    dsimp [θ]
    exact subgroupInKernel'_inducedCF_of_subgroupInKernel'_sec9
      HCD H0CD hH0CD_le_HCD hψiD_irr hψiDKerH0CD
  have hθnotMF : ¬ Section1.subgroupInKernel' (θ i) MFD := by
    intro hθkerMF
    have hψiDKerMFD :
        Section1.subgroupInKernel'
          (Section1.subgroupOfClassFunction (ψ i)) (MFD.subgroupOf HCD) := by
      dsimp [θ] at hθkerMF
      exact subgroupInKernel'_of_inducedCF_sec9
        HCD MFD hMFD_le_HCD hψiD_irr hθkerMF
    have hψiKerMFM :
        Section1.subgroupInKernel' (ψ i) ((MF.subgroupOf M).subgroupOf HCm) := by
      dsimp [MFD, HCD, Dm, HCm] at hψiDKerMFD
      exact subgroupInKernel'_of_subgroupOfClassFunction_sec9
        hMFM_le_Dm hMFM_le_HCm hψiDKerMFD
    have hψHCKerMF :
        Section1.subgroupInKernel' (ψHC (rep i)) (MF.subgroupOf (MF ⊔ C)) := by
      dsimp [ψ, HCm] at hψiKerMFM
      exact subgroupInKernel'_of_subgroupOfClassFunction_sec9
        hMF_le_M hMF_le_HC hψiKerMFM
    exact hψnotMF (rep i) hψHCKerMF
  exact ⟨hθirr, hθnotMF, hθkerH0C, hψi_irr, hψdeg⟩


private theorem
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_reverse_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (_hρcyc : ∀ i, IsCyclic (ρ i).range)
    (_hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (_hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (ψHC =
          (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
           let HC : Subgroup G := MF ⊔ C
           let H0C : Subgroup G := H0 ⊔ C
           let hMFHC : MF ≤ HC := le_sup_left
           let e : (MF ⧸ H0.subgroupOf MF) ≃*
               (HC ⧸ H0C.subgroupOf HC) :=
             quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
           let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
             fun f =>
               componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
                 f.down
           let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
             fun f => (θH f).comp e.symm.toMonoidHom
           fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
        let instAction : MulAction (U ⧸ C.subgroupOf U)
            (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U)
            (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
        ∀ hnormalHCD : (((MF ⊔ C).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).Normal,
          letI : (((MF ⊔ C).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hnormalHCD
          let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
          let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
          let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
          let HCD : Subgroup Dm := HCm.subgroupOf Dm
          let ψ : κ → Section1.ClassFunction HCm :=
            fun k => Section1.subgroupOfClassFunction (ψHC k)
          let θ : κ → Section1.ClassFunction Dm :=
            fun k => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ k));
            (∀ k : κ,
              Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ k)) =
                HCD) ∧
              ∀ k l : κ,
                θ k = θ l →
                  MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l := by
    classical
    intro hcase hψformula
    dsimp only
    intro hnormalHCD
    let instAction : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    letI : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
    letI : (((MF ⊔ C).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hnormalHCD
    let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
    let D : Subgroup G := ambientDerivedSubgroup M
    let Dm : Subgroup M := D.subgroupOf M
    let HC : Subgroup G := MF ⊔ C
    let HCm : Subgroup M := HC.subgroupOf M
    let HCD : Subgroup Dm := HCm.subgroupOf Dm
    let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
    let UD : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
    let ψ : κ → Section1.ClassFunction HCm :=
      fun k => Section1.subgroupOfClassFunction (ψHC k)
    let θ : κ → Section1.ClassFunction Dm :=
      fun k => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ k))
    letI : HCD.Normal := by
      simpa [HC, D, HCm, Dm, HCD] using hnormalHCD
    have h92 := case_9_7_a_hypothesis_9_2_sec9 hcase
    have hMFDnormal : MFD.Normal := by
      simpa [MFD, Dm, D] using
        theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
          M MF U W1 W2 H0 C p q a hcase
    have hsemi :
        Section2.IsInternalSemidirectProduct (⊤ : Subgroup Dm) MFD UD := by
      simpa [MFD, UD, Dm, D] using
        theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
          M MF U W1 W2 q h92 hMFDnormal
    rcases h92.typeP with ⟨_hMFtype, hcommon⟩
    rcases hcommon with
      ⟨_hDhall, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
        _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
        _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
    rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
    have hDleM : D ≤ M := by
      dsimp [D]
      exact section12_ambientDerivedSubgroup_le (E := M)
    have hUleM : U ≤ M := hUleD.trans hDleM
    have hC_le_U : C ≤ U :=
      (case_9_7_a_quotientCentralizerIn_sec9 hcase).1
    have hψclass : ∀ k : κ, Section1.IsClassFunction
        (Section1.subgroupOfClassFunction (T := Dm) (ψ k)) := by
      intro k
      dsimp [ψ, HCm, Dm]
      rw [hψformula]
      exact subgroupOfClassFunction_isClassFunction_sec9
        (subgroupOfClassFunction_isClassFunction_sec9
          (Section1.quotientCharacterInflation_isClassFunction (H0 ⊔ C) (MF ⊔ C) _))
    have hinertia : ∀ k : κ,
        Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ k)) = HCD := by
      intro k
      have hHCD_le_I :
          HCD ≤ Section1.inertiaSubgroup HCD
            (Section1.subgroupOfClassFunction (ψ k)) :=
        Section1.proposition_1_7_inertia_contains_H HCD
          (Section1.subgroupOfClassFunction (ψ k)) (hψclass k)
      apply le_antisymm
      · intro g hgI
        rcases hsemi.mul_surjective g (by trivial) with ⟨m0, hm0, u0, hu0, hg⟩
        let x : U ⧸ C.subgroupOf U :=
          QuotientGroup.mk' (C.subgroupOf U)
            ⟨(((u0 : Dm) : M) : G), by
              have huUM : ((u0 : Dm) : M) ∈ U.subgroupOf M := by
                simpa [UD, Dm, D, Subgroup.mem_subgroupOf] using hu0
              simpa [Subgroup.mem_subgroupOf] using huUM⟩
        let uU : U := ⟨(((u0 : Dm) : M) : G), by
          have huUM : ((u0 : Dm) : M) ∈ U.subgroupOf M := by
            simpa [UD, Dm, D, Subgroup.mem_subgroupOf] using hu0
          simpa [Subgroup.mem_subgroupOf] using huUM⟩
        have huD : (((u0 : Dm) : M) : G) = (uU : G) := rfl
        have hmHCD : m0 ∈ HCD := by
          have hmMF : ((m0 : Dm) : M) ∈ MF.subgroupOf M := by
            simpa [MFD, Dm, D, Subgroup.mem_subgroupOf] using hm0
          have hmHCG : (((m0 : Dm) : M) : G) ∈ HC := by
            exact (le_sup_left : MF ≤ HC) (by simpa [Subgroup.mem_subgroupOf] using hmMF)
          simpa [HCD, HCm, HC, Dm, D, Subgroup.mem_subgroupOf] using hmHCG
        have hu_fix :
            Section1.conjugateOnNormal HCD
                (Section1.subgroupOfClassFunction (ψ k)) u0 =
              Section1.subgroupOfClassFunction (ψ k) := by
          have hgfix :
              Section1.conjugateOnNormal HCD
                  (Section1.subgroupOfClassFunction (ψ k)) g =
                Section1.subgroupOfClassFunction (ψ k) := by
            simpa [Section1.inertiaSubgroup] using hgI
          have hmulfix :
              Section1.conjugateOnNormal HCD
                  (Section1.subgroupOfClassFunction (ψ k)) (m0 * u0) =
                Section1.subgroupOfClassFunction (ψ k) := by
            simpa [hg] using hgfix
          have herase :
              Section1.conjugateOnNormal HCD
                  (Section1.subgroupOfClassFunction (ψ k)) (m0 * u0) =
                Section1.conjugateOnNormal HCD
                  (Section1.subgroupOfClassFunction (ψ k)) u0 :=
            conjugateOnNormal_mul_left_of_mem_sec9
              (Section1.subgroupOfClassFunction (ψ k)) (hψclass k) hmHCD
          exact herase.symm.trans hmulfix
        have hxfix : x • k = k := by
          dsimp [x]
          exact rawCoordinateMulAction_eq_self_of_conjugateOnNormal_fixed_sec9
            M MF U W1 W2 H0 C p q a H hHcard hHnorm hHindep hHsup ρ hρaction
            hconj hH0CinfMF hsup ψHC hcase hψformula hnormalHCD
            (QuotientGroup.mk' (C.subgroupOf U) uU) uU u0 rfl huD k
            (by simpa [ψ, HCD, HCm, Dm, D] using hu_fix)
        have hxstab : x ∈ MulAction.stabilizer (U ⧸ C.subgroupOf U) k := by
          rw [MulAction.mem_stabilizer_iff]
          exact hxfix
        have hxone : x = 1 := by
          have hstab :=
            rawCoordinateMulAction_stabilizer_eq_bot_sec9
              (hcase := hcase) H hHcard hHnorm hHsup ρ hρaction k
          have hxbot : x ∈ (⊥ : Subgroup (U ⧸ C.subgroupOf U)) := by
            simpa [instAction] using (by simpa [hstab] using hxstab)
          exact Subgroup.mem_bot.mp hxbot
        have huC : (uU : G) ∈ C := by
          have huCsub : uU ∈ C.subgroupOf U :=
            (QuotientGroup.eq_one_iff (N := C.subgroupOf U) (x := uU)).1
              (by simpa [x] using hxone)
          simpa [Subgroup.mem_subgroupOf] using huCsub
        have huHCD : u0 ∈ HCD := by
          have huHCG : (((u0 : Dm) : M) : G) ∈ HC := by
            exact (le_sup_right : C ≤ HC) (by simpa [uU] using huC)
          simpa [HCD, HCm, HC, Dm, D, Subgroup.mem_subgroupOf] using huHCG
        have hgHCD : g ∈ HCD := by
          rw [hg]
          exact HCD.mul_mem hmHCD huHCD
        exact hgHCD
      · exact hHCD_le_I
    refine ⟨hinertia, ?_⟩
    intro k l hθeq
    have hHC_le_D : HC ≤ D := by
      dsimp [HC, D]
      exact theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
        M MF U W1 W2 H0 C p q a hcase
    have hHCm_le_Dm : HCm ≤ Dm := by
      intro x hx
      change ((x : M) : G) ∈ D
      exact hHC_le_D (by simpa [HCm, HC, Subgroup.mem_subgroupOf] using hx)
    have hHC_le_M : HC ≤ M :=
      hHC_le_D.trans hDleM
    have hψD_irr : ∀ r : κ,
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.subgroupOfClassFunction (T := Dm) (ψ r)) := by
      intro r
      have hψHC_irr :
          Section1.IsIrreducibleCharacterOnGroup (ψHC r) := by
        rw [hψformula]
        let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ (H0 ⊔ C).subgroupOf HC) :=
          quotientInfSupEquiv_sec9 MF H0 HC (H0 ⊔ C) le_sup_left hH0CinfMF hsup
        let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
          fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
        let θHC : κ → (HC ⧸ (H0 ⊔ C).subgroupOf HC) →* ℂˣ :=
          fun f => (θH f).comp e.symm.toMonoidHom
        change Section1.IsIrreducibleCharacterOnGroup
          (Section1.quotientCharacterInflation (H0 ⊔ C) HC (θHC r))
        exact Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
          (H0 ⊔ C) HC (θHC r)
      have hψM_irr :
          Section1.IsIrreducibleCharacterOnGroup (ψ r) := by
        dsimp [ψ, HCm]
        exact isIrreducible_subgroupOfClassFunction_sec9 (H := HC) (T := M)
          hHC_le_M hψHC_irr
      exact isIrreducible_subgroupOfClassFunction_sec9 (T := Dm)
        hHCm_le_Dm hψM_irr
    have hθeq' :
        Section1.inducedCF HCD
            (Section1.subgroupOfClassFunction (T := Dm) (ψ k)) =
          Section1.inducedCF HCD
            (Section1.subgroupOfClassFunction (T := Dm) (ψ l)) := by
      simpa [ψ, θ, HC, HCm, D, Dm, HCD] using hθeq
    rcases induced_eq_imp_conjugateOrbitConj_of_irreducible_sec9
        HCD (hψD_irr k) (hψD_irr l) hθeq' with ⟨i, hi⟩
    revert hi
    refine Quotient.inductionOn i ?_
    intro g hi
    have hconjG :
        Section1.subgroupOfClassFunction (T := Dm) (ψ k) =
          Section1.conjugateOnNormal HCD
            (Section1.subgroupOfClassFunction (T := Dm) (ψ l)) g := by
      simpa [Section1.conjugateOrbitConj] using hi
    rcases hsemi.mul_surjective g (by trivial) with ⟨m0, hm0, u0, hu0, hg⟩
    let x : U ⧸ C.subgroupOf U :=
      QuotientGroup.mk' (C.subgroupOf U)
        ⟨(((u0 : Dm) : M) : G), by
          have huUM : ((u0 : Dm) : M) ∈ U.subgroupOf M := by
            simpa [UD, Dm, D, Subgroup.mem_subgroupOf] using hu0
          simpa [Subgroup.mem_subgroupOf] using huUM⟩
    let uU : U := ⟨(((u0 : Dm) : M) : G), by
      have huUM : ((u0 : Dm) : M) ∈ U.subgroupOf M := by
        simpa [UD, Dm, D, Subgroup.mem_subgroupOf] using hu0
      simpa [Subgroup.mem_subgroupOf] using huUM⟩
    have huD : (((u0 : Dm) : M) : G) = (uU : G) := rfl
    have hmHCD : m0 ∈ HCD := by
      have hmMF : ((m0 : Dm) : M) ∈ MF.subgroupOf M := by
        simpa [MFD, Dm, D, Subgroup.mem_subgroupOf] using hm0
      have hmHCG : (((m0 : Dm) : M) : G) ∈ HC := by
        exact (le_sup_left : MF ≤ HC) (by simpa [Subgroup.mem_subgroupOf] using hmMF)
      simpa [HCD, HCm, HC, Dm, D, Subgroup.mem_subgroupOf] using hmHCG
    have hconjU :
        Section1.subgroupOfClassFunction (T := Dm) (ψ k) =
          Section1.conjugateOnNormal HCD
            (Section1.subgroupOfClassFunction (T := Dm) (ψ l)) u0 := by
      have hconjMU :
          Section1.subgroupOfClassFunction (T := Dm) (ψ k) =
            Section1.conjugateOnNormal HCD
              (Section1.subgroupOfClassFunction (T := Dm) (ψ l)) (m0 * u0) := by
        simpa [hg] using hconjG
      have herase :
          Section1.conjugateOnNormal HCD
              (Section1.subgroupOfClassFunction (T := Dm) (ψ l)) (m0 * u0) =
            Section1.conjugateOnNormal HCD
              (Section1.subgroupOfClassFunction (T := Dm) (ψ l)) u0 :=
        conjugateOnNormal_mul_left_of_mem_sec9
          (Section1.subgroupOfClassFunction (T := Dm) (ψ l)) (hψclass l) hmHCD
      exact hconjMU.trans herase
    have hψconj :
        Section1.subgroupOfClassFunction (T := Dm)
            (Section1.subgroupOfClassFunction (T := M) (ψHC (x • l))) =
          Section1.conjugateOnNormal HCD
            (Section1.subgroupOfClassFunction (T := Dm)
              (Section1.subgroupOfClassFunction (T := M) (ψHC l))) u0 := by
      rw [hψformula]
      simpa [instAction, x, HC, D, Dm, HCm, HCD] using
        quotientCharacterInflation_rawCoordinateMulAction_eq_conjugateOnNormal_sec9
          M MF U W1 W2 H0 C p q a H hHcard hHnorm hHindep hHsup ρ
          hρaction hconj hH0CinfMF hsup hcase hnormalHCD
          (QuotientGroup.mk' (C.subgroupOf U) uU) uU u0 rfl huD l
    have hres :
        Section1.subgroupOfClassFunction (T := Dm)
            (Section1.subgroupOfClassFunction (T := M) (ψHC k)) =
          Section1.subgroupOfClassFunction (T := Dm)
            (Section1.subgroupOfClassFunction (T := M) (ψHC (x • l))) := by
      have hku :
          Section1.subgroupOfClassFunction (T := Dm)
              (Section1.subgroupOfClassFunction (T := M) (ψHC k)) =
            Section1.conjugateOnNormal HCD
              (Section1.subgroupOfClassFunction (T := Dm)
                (Section1.subgroupOfClassFunction (T := M) (ψHC l))) u0 := by
        simpa [ψ, HCm, Dm, HCD] using hconjU
      exact hku.trans hψconj.symm
    have hk_eq_xl : k = x • l := by
      simpa [instAction, x, HC, D, Dm, HCm, HCD] using
        rawCoordinate_eq_of_restricted_quotientCharacterInflation_eq_sec9
          M MF U W1 W2 H0 C p q a H hHcard hHindep hHsup hH0CinfMF hsup
          ψHC hcase hψformula k (x • l) hres
    rw [MulAction.orbitRel_apply]
    exact MulAction.mem_orbit_iff.mpr ⟨x, hk_eq_xl.symm⟩

private theorem
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (ψHC =
          (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
           let HC : Subgroup G := MF ⊔ C
           let H0C : Subgroup G := H0 ⊔ C
           let hMFHC : MF ≤ HC := le_sup_left
           let e : (MF ⧸ H0.subgroupOf MF) ≃*
               (HC ⧸ H0C.subgroupOf HC) :=
             quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
           let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
             fun f =>
               componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
                 f.down
           let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
             fun f => (θH f).comp e.symm.toMonoidHom
           fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
        let instAction : MulAction (U ⧸ C.subgroupOf U)
            (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U)
            (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
        ∀ hnormalHCD : (((MF ⊔ C).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).Normal,
          letI : (((MF ⊔ C).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hnormalHCD
          let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
          let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
          let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
          let HCD : Subgroup Dm := HCm.subgroupOf Dm
          let ψ : κ → Section1.ClassFunction HCm :=
            fun k => Section1.subgroupOfClassFunction (ψHC k)
          let θ : κ → Section1.ClassFunction Dm :=
            fun k => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ k))
          (∀ k : κ,
            Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ k)) =
              HCD) ∧
            ∀ k l : κ,
              θ k = θ l ↔
                MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l := by
  classical
  intro hcase hψformula
  dsimp only
  intro hnormalHCD
  let instAction : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
  letI : (((MF ⊔ C).subgroupOf M).subgroupOf
      ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hnormalHCD
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let ψ : κ → Section1.ClassFunction HCm :=
    fun k => Section1.subgroupOfClassFunction (ψHC k)
  let θ : κ → Section1.ClassFunction Dm :=
    fun k => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ k))
  have hrev :=
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_reverse_source_core_sec9
      M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup ρ hρcyc hρcard
      hρaction hρker hconj hH0CinfMF hsup ψHC hcase hψformula hnormalHCD
  refine ⟨?_, ?_⟩
  · exact hrev.1
  · intro k l
    constructor
    · exact hrev.2 k l
    · intro hrel
      rw [hψformula]
      simpa [instAction, κ, Dm, HCm, HCD, ψ, θ] using
        induced_eq_of_rawCoordinateMulAction_orbitRel_sec9
          M MF U W1 W2 H0 C p q a H hHcard hHnorm hHindep hHsup ρ
          hρaction hconj hH0CinfMF hsup hcase hnormalHCD k l hrel

private theorem
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_core_of_raw_action_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (ψHC =
          (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
           let HC : Subgroup G := MF ⊔ C
           let H0C : Subgroup G := H0 ⊔ C
           let hMFHC : MF ≤ HC := le_sup_left
           let e : (MF ⧸ H0.subgroupOf MF) ≃*
               (HC ⧸ H0C.subgroupOf HC) :=
             quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
           let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
             fun f =>
               componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
                 f.down
           let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
             fun f => (θH f).comp e.symm.toMonoidHom
           fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
        let instAction : MulAction (U ⧸ C.subgroupOf U)
            (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U)
            (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
        H0CLinearCandidateXthetaThetaCoordinateActionCoreData_sec9
          M MF U H0 C p q ψHC := by
  classical
  intro hcase hψformula
  let instAction : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
  refine ⟨hnormalC, instAction, ?_, ?_⟩
  · exact
      rawCoordinateMulAction_stabilizer_eq_bot_sec9
        hcase H hHcard hHnorm hHsup ρ hρaction
  · exact
      theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup ρ hρcyc hρcard
        hρaction hρker hconj hH0CinfMF hsup ψHC hcase hψformula

private theorem
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_core_of_concrete_formula_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (hfac : ∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) aρ)
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (hnormalC : (C.subgroupOf U).Normal)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (ψHC =
          (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
           let HC : Subgroup G := MF ⊔ C
           let H0C : Subgroup G := H0 ⊔ C
           let hMFHC : MF ≤ HC := le_sup_left
           let e : (MF ⧸ H0.subgroupOf MF) ≃*
               (HC ⧸ H0C.subgroupOf HC) :=
             quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
           let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
             fun f =>
               componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
                 f.down
           let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
             fun f => (θH f).comp e.symm.toMonoidHom
           fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
        H0CLinearCandidateXthetaThetaCoordinateActionCoreData_sec9
          M MF U H0 C p q ψHC := by
  -- coordinates must be derived from the displayed product-coordinate formula.
  classical
  letI : (C.subgroupOf U).Normal := hnormalC
  choose hnormalC' ρ hρcyc hρcard hρaction hρker using hfac
  exact
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_core_of_raw_action_source_core_sec9
      M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup ρ hρcyc hρcard
      hρaction hρker hconj hH0CinfMF hsup ψHC


private theorem
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_orbit_of_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C : Subgroup G)
    (p q u : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    H0CLinearCandidateXthetaThetaCoordinateActionData_sec9 M MF U H0 C p q u ψHC →
      H0CLinearCandidateXthetaThetaCoordinateOrbitData_sec9 M MF U H0 C p q u ψHC := by
  classical
  intro hactionData
  rcases hactionData with
    ⟨hnormalC, instAction, hstab, hbarCard, hcoord⟩
  refine ⟨hnormalC, instAction, hstab, hbarCard, ?_⟩
  intro hnormalHCD
  letI : (C.subgroupOf U).Normal := hnormalC
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  letI : HCD.Normal := hnormalHCD
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let ψRaw : κ → Section1.ClassFunction HCm :=
    fun k => Section1.subgroupOfClassFunction (ψHC k)
  let θRaw : κ → Section1.ClassFunction Dm :=
    fun k => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψRaw k))
  rcases hcoord hnormalHCD with ⟨hIeq, hInd_iff⟩
  constructor
  · intro i j hij
    have hout :
        MulAction.orbitRel (U ⧸ C.subgroupOf U) κ (Quotient.out i) (Quotient.out j) := by
      rw [← hInd_iff]
      exact hij
    have hi : Quotient.mk'' (Quotient.out i : κ) = i :=
      Quotient.out_eq' i
    have hj : Quotient.mk'' (Quotient.out j : κ) = j :=
      Quotient.out_eq' j
    exact (hi.symm.trans (Quotient.sound hout)).trans hj
  · intro i
    exact hIeq (Quotient.out i)


private def H0CLinearCandidateXmuTransportedRawData_sec9
    {G : Type u} [Group G] [Finite G]
    (M W1 : Subgroup G)
    (p : ℕ)
    (κ : Type u)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (orbit : κ → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    Prop :=
  ∃ μraw : H0CLinearCandidateXmuRawIndex_sec9 p → κ,
    let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
      fun i => orbit (μraw i)
    H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9 M p ι
        μorbit θ ∧
      H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9 M W1 p ι
        μorbit θ

set_option maxHeartbeats 800000 in
private theorem H0CLinearCandidateXmu_transported_generator_raw_smul_source_core_sec9
    {G : Type u} [Group G] [Finite G]
    {MF U W1 H0 C : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hW1card : Nat.card W1 = q)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U))
    (hμrawOrderedData :
      H0CLinearCandidateXmuOrderedTransportedRawCoordinateData_sec9
        (MF := MF) (H0 := H0) (W1 := W1) p q H hHcard w0 μraw)
    (hqpos : 0 < q)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G))
    (x : U ⧸ C.subgroupOf U)
    {i j : H0CLinearCandidateXmuRawIndex_sec9 p} :
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
      quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
    let instAction : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    letI : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
    x • μraw j = μraw i →
      (w0 • x) • μraw j = μraw i := by
  classical
  intro _instAction hx
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  letI : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  rcases hμrawOrderedData with ⟨hqposμ, _hwμ, E, hE, hμraw_eq⟩
  let base : Fin q := ⟨0, hqposμ⟩
  rcases hsucc ⟨0, hqpos⟩ with ⟨hconjMF, action, haction, _hmap0⟩
  have hmap_each :
      ∀ k : Fin q,
        (H k).map action.toMonoidHom =
          H (theorem_9_7_fin_cyclic_succ_sec9 hqpos k) := by
    intro k
    rcases hsucc k with ⟨hconjMF_k, action_k, haction_k, hmap_k⟩
    have haction_eq : action_k = action := by
      ext z
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) z with ⟨m, rfl⟩
      calc
        action_k (QuotientGroup.mk' (H0.subgroupOf MF) m) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjMF_k m⟩ := haction_k m
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjMF m⟩ := by
              congr 1
        _ = action (QuotientGroup.mk' (H0.subgroupOf MF) m) := (haction m).symm
    simpa [haction_eq] using hmap_k.symm
  have hE_step :
      ∀ k : Fin q, ∀ z : H base,
        (E (theorem_9_7_fin_cyclic_succ_sec9 hqpos k) z :
            MF ⧸ H0.subgroupOf MF) =
          action (E k z : MF ⧸ H0.subgroupOf MF) := by
    intro k z
    let sk : Fin q := theorem_9_7_fin_cyclic_succ_sec9 hqpos k
    have hw0q : w0 ^ q = 1 := by
      rw [← hW1card, ← orderOf_eq_card_of_zpowers_eq_top hw0gen]
      exact pow_orderOf_eq_one w0
    have hpow_stepW1 : w0 ^ sk.1 = w0 ^ k.1 * w0 := by
      by_cases hnext : k.1 + 1 < q
      · simp [sk, theorem_9_7_fin_cyclic_succ_sec9, hnext, pow_succ]
      · have hkq : k.1 + 1 = q := by omega
        calc
          w0 ^ sk.1 = 1 := by
            simp [sk, theorem_9_7_fin_cyclic_succ_sec9, hnext]
          _ = w0 ^ k.1 * w0 := by
            symm
            calc
              w0 ^ k.1 * w0 = w0 ^ (k.1 + 1) := (pow_succ w0 k.1).symm
              _ = w0 ^ q := by rw [hkq]
              _ = 1 := hw0q
    have hpow_stepG :
        (((w0 ^ sk.1 : W1) : G) =
          (((w0 ^ k.1 : W1) : G) * (w0 : G))) := by
      simpa using congrArg Subtype.val hpow_stepW1
    rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF)
        (z : MF ⧸ H0.subgroupOf MF) with ⟨m, hm⟩
    have hmBase : QuotientGroup.mk' (H0.subgroupOf MF) m ∈ H base := by
      simp [base, hm]
    have hzmk :
        z = ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase⟩ := by
      apply Subtype.ext
      simpa using hm.symm
    rcases hE k with ⟨hconj_k, hE_k⟩
    rcases hE sk with ⟨hconj_sk, hE_sk⟩
    rw [hzmk]
    calc
      (E sk ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase⟩ :
          MF ⧸ H0.subgroupOf MF) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(((w0 ^ sk.1 : W1) : G))⁻¹ * (m : G) *
                (((w0 ^ sk.1 : W1) : G)), hconj_sk m⟩ :=
        hE_sk m hmBase
      _ = action
          (QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(((w0 ^ k.1 : W1) : G))⁻¹ * (m : G) *
                (((w0 ^ k.1 : W1) : G)), hconj_k m⟩) := by
        rw [haction]
        apply congrArg (QuotientGroup.mk' (H0.subgroupOf MF))
        apply Subtype.ext
        change (((w0 ^ sk.1 : W1) : G))⁻¹ * (m : G) *
            (((w0 ^ sk.1 : W1) : G)) =
          (w0 : G)⁻¹ *
            ((((w0 ^ k.1 : W1) : G))⁻¹ * (m : G) *
              (((w0 ^ k.1 : W1) : G))) * (w0 : G)
        rw [hpow_stepG]
        group
      _ = action
          (E k ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase⟩ :
            MF ⧸ H0.subgroupOf MF) := by
        rw [hE_k m hmBase]
  apply ULift.ext
  funext k
  apply (nonprincipalLinearCharacterEquivFin_sec9 (H k) p (hHcard k)).injective
  apply Subtype.ext
  apply MonoidHom.ext
  intro z
  let sk : Fin q := theorem_9_7_fin_cyclic_succ_sec9 hqpos k
  let eStep : H k ≃* H sk := (E k).symm.trans (E sk)
  have htransport :
      ∃ e0 : H k ≃* H sk,
        (∃ hconjW : ∀ h : MF, (w0 : G)⁻¹ * (h : G) * (w0 : G) ∈ MF,
          (∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H k,
            (e0 ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                MF ⧸ H0.subgroupOf MF) =
              QuotientGroup.mk' (H0.subgroupOf MF)
                ⟨(w0 : G)⁻¹ * (h : G) * (w0 : G), hconjW h⟩) ∧
          ∃ hconjWinv : ∀ h : MF, (w0 : G) * (h : G) * (w0 : G)⁻¹ ∈ MF,
            ∀ h : MF, ∀ hhR : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H sk,
              (e0.symm ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhR⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(w0 : G) * (h : G) * (w0 : G)⁻¹, hconjWinv h⟩) ∧
        theorem_9_7_successorTransportFactorAction_sec9 hnormalC hCinv w0 e0
            (ρ k) =
          ρ sk := by
    simpa [sk] using
      theorem_9_7_successorTransportFactorAction_eq_of_action_field_sec9
        hnormalC hCinv w0 (hsucc k) (ρ := ρ k)
        (σ := ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos k))
        (hρaction k)
        (hρaction (theorem_9_7_fin_cyclic_succ_sec9 hqpos k))
  let e0 : H k ≃* H sk := Classical.choose htransport
  have heData0 := (Classical.choose_spec htransport).1
  have heq0 := (Classical.choose_spec htransport).2
  rcases heData0 with ⟨hconjStep, he0, _hconjStepInv, _he0symm⟩
  have he0_eStep : e0 = eStep := by
    ext y
    rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF)
        (y : MF ⧸ H0.subgroupOf MF) with ⟨m, hm⟩
    have hmK : QuotientGroup.mk' (H0.subgroupOf MF) m ∈ H k := by
      simp [hm]
    have hymk : y = ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmK⟩ := by
      apply Subtype.ext
      simpa using hm.symm
    have he0val :
        (e0 y : MF ⧸ H0.subgroupOf MF) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjStep m⟩ := by
      rw [hymk]
      exact he0 m hmK
    have heStep_action :
        (eStep y : MF ⧸ H0.subgroupOf MF) =
          action (y : MF ⧸ H0.subgroupOf MF) := by
      dsimp [eStep]
      simpa [sk] using hE_step k ((E k).symm y)
    have heStep_val :
        (eStep y : MF ⧸ H0.subgroupOf MF) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjMF m⟩ := by
      calc
        (eStep y : MF ⧸ H0.subgroupOf MF) =
            action (y : MF ⧸ H0.subgroupOf MF) := heStep_action
        _ = action (QuotientGroup.mk' (H0.subgroupOf MF) m) := by rw [hm]
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjMF m⟩ := haction m
    exact he0val.trans heStep_val.symm
  have heqStep :
      theorem_9_7_successorTransportFactorAction_sec9 hnormalC hCinv w0 eStep
          (ρ k) =
        ρ sk := by
    rw [← he0_eStep]
    exact heq0
  have hfactor_eStep :
      ∀ y : H k, (ρ sk x) (eStep y) = eStep (ρ k (w0 • x) y) := by
    intro y
    rw [← heqStep]
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    simpa using theorem_9_7_successorTransportFactorAction_apply_mk_sec9
      hnormalC hCinv w0 eStep (ρ k) u (eStep y)
  let yk : H k := (ρ k (w0 • x)).symm z
  have hpre :
      (ρ sk x).symm (eStep z) = eStep yk := by
    apply (ρ sk x).injective
    simpa [yk] using (hfactor_eStep yk).symm
  have hβ :
      (E sk).symm ((ρ sk x).symm (eStep z)) =
        (E k).symm yk := by
    calc
      (E sk).symm ((ρ sk x).symm (eStep z)) =
          (E sk).symm (eStep yk) := by rw [hpre]
      _ = (E k).symm yk := by
          simp [eStep]
  have hsk :
      (x • μraw j).down sk = (μraw i).down sk := by
    exact congrArg
      (fun f : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q => f.down sk) hx
  have hsk_eval :
      ((nonprincipalLinearCharacterEquivFin_sec9 (H sk) p (hHcard sk))
          ((x • μraw j).down sk)).1 (eStep z) =
        ((nonprincipalLinearCharacterEquivFin_sec9 (H sk) p (hHcard sk))
          ((μraw i).down sk)).1 (eStep z) := by
    rw [hsk]
  have hbase_eval :
      ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
          (hHcard base)) j).1 ((E k).symm yk) =
        ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
          (hHcard base)) i).1 ((E k).symm z) := by
    have hleft :
        ((nonprincipalLinearCharacterEquivFin_sec9 (H sk) p (hHcard sk))
            ((x • μraw j).down sk)).1 (eStep z) =
          ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
            (hHcard base)) j).1 ((E k).symm yk) := by
      calc
        ((nonprincipalLinearCharacterEquivFin_sec9 (H sk) p (hHcard sk))
            ((x • μraw j).down sk)).1 (eStep z) =
            ((nonprincipalLinearCharacterEquivFin_sec9 (H sk) p (hHcard sk))
              ((μraw j).down sk)).1 ((ρ sk x).symm (eStep z)) := by
              simp [rawCoordinateMulAction_down_sec9,
                nonprincipalLinearCharacterIndexMulAction_spec_sec9,
                MonoidHom.comp_apply]
        _ = ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
              (hHcard base)) j).1 ((E k).symm yk) := by
              have hspec :=
                H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_component_spec_sec9
                  p q H hHcard base E j sk
              have happ := congrArg
                (fun χ : H sk →* ℂˣ => χ ((ρ sk x).symm (eStep z))) hspec
              simpa [base, hμraw_eq, MonoidHom.comp_apply, hβ] using happ
    have hright :
        ((nonprincipalLinearCharacterEquivFin_sec9 (H sk) p (hHcard sk))
            ((μraw i).down sk)).1 (eStep z) =
          ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
            (hHcard base)) i).1 ((E k).symm z) := by
      have hspec :=
        H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_component_spec_sec9
          p q H hHcard base E i sk
      have happ := congrArg (fun χ : H sk →* ℂˣ => χ (eStep z)) hspec
      simpa [base, hμraw_eq, MonoidHom.comp_apply, eStep] using happ
    exact hleft.symm.trans (hsk_eval.trans hright)
  simpa [base, hμraw_eq, rawCoordinateMulAction_down_sec9,
    nonprincipalLinearCharacterIndexMulAction_spec_sec9,
    H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_component_spec_sec9,
    MonoidHom.comp_apply, yk] using hbase_eval

private theorem H0CLinearCandidateXmu_transported_muorbit_injective_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (_hρcyc : ∀ i, IsCyclic (ρ i).range)
    (_hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (_hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (_hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (_horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hμrawOrderedActionData :
      H0CLinearCandidateXmuOrderedTransportedRawActionData_sec9
        (MF := MF) (U := U) (W1 := W1) (H0 := H0) (C := C)
        p q aρ H hHcard ρ μraw)
    (_hW1Inertia :
      let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
      let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
      let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
      let HCD : Subgroup Dm := HCm.subgroupOf Dm
      let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
        rawCoordinateMulAction_sec9 p q H hHcard ρ
      letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
      let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
      let instFintypeι : Fintype ι := Fintype.ofFinite ι
      let instDecidableEqι : DecidableEq ι := Classical.decEq ι
      letI : Fintype ι := instFintypeι
      letI : DecidableEq ι := instDecidableEqι
      let orbit : κ → ι := fun k => Quotient.mk'' k
      let ψ : ι → Section1.ClassFunction HCm :=
        fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
      let θ : ι → Section1.ClassFunction Dm :=
        fun i =>
          Section1.inducedCF HCD
            (Section1.subgroupOfClassFunction (ψ i))
      let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
        fun i => orbit (μraw i)
      H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9 M W1 p ι
        μorbit θ) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
        let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
        let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
        let instFintypeι : Fintype ι := Fintype.ofFinite ι
        let instDecidableEqι : DecidableEq ι := Classical.decEq ι
        letI : Fintype ι := instFintypeι
        letI : DecidableEq ι := instDecidableEqι
        let orbit : κ → ι := fun k => Quotient.mk'' k
        Function.Injective
          (fun i : H0CLinearCandidateXmuRawIndex_sec9 p => orbit (μraw i)) := by
  classical
  intro _hψformula hcase _hBarU
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  rcases hμrawOrderedActionData with
    ⟨hW1normU, w0, hw0gen, hμrawOrderedData, hqpos, hsucc, _χbar,
      _hχsep, _hχtransition⟩
  have hμraw_inj : Function.Injective μraw := by
    rcases hμrawOrderedData with ⟨hqposμ, _hwμ, E, _hEμ, hμraw_eq⟩
    rw [hμraw_eq]
    exact
      H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_injective_sec9
        p q H hHcard ⟨0, hqposμ⟩ E
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases case_9_7_a_hoReductionData_sec9 hcase with ⟨hp, _hp_eq, hpData⟩
  have hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G) := by
    exact le_sup_right.trans
      (theorem_9_3_action_normalizes_and_solvable_sec9 M MF U W1 W2 q h92).1
  have hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U) := by
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    exact theorem_9_7_quotientCentralizerIn_isInvariant_W1_sec9
      h92 hpData (case_9_7_a_quotientCentralizerIn_sec9 hcase)
      hW1normU hW1normMF
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  have hfixedBot :
      fixedPointSubgroup W1 (U ⧸ C.subgroupOf U) = ⊥ :=
    theorem_9_7_fixedPointSubgroup_W1_barU_eq_bot_of_isInvariant_sec9
      h92 hnormalC hW1normU hCinv
  change Function.Injective
    (fun i : H0CLinearCandidateXmuRawIndex_sec9 p => orbit (μraw i))
  intro i j hij
  have hrel :
      MulAction.orbitRel (U ⧸ C.subgroupOf U) κ (μraw i) (μraw j) := by
    exact Quotient.exact (by simpa [orbit] using hij)
  rw [MulAction.orbitRel_apply] at hrel
  rcases MulAction.mem_orbit_iff.mp hrel with ⟨x, hx⟩
  have hW1card : Nat.card W1 = q := h92.q_eq
  have hx_gen :
      (w0 • x) • μraw j = μraw i :=
    H0CLinearCandidateXmu_transported_generator_raw_smul_source_core_sec9
      (MF := MF) (U := U) (W1 := W1) (H0 := H0) (C := C)
      p q H hHcard ρ hρaction μraw w0 hw0gen hW1card hW1normU hCinv
      hμrawOrderedData hqpos hsucc x hx
  have hsame :
      (w0 • x) • μraw j = x • μraw j := hx_gen.trans hx.symm
  have hfix_delta :
      (x⁻¹ * (w0 • x)) • μraw j = μraw j := by
    calc
      (x⁻¹ * (w0 • x)) • μraw j =
          x⁻¹ • ((w0 • x) • μraw j) := by rw [mul_smul]
      _ = x⁻¹ • (x • μraw j) := by rw [hsame]
      _ = μraw j := by rw [inv_smul_smul]
  have hdelta_mem :
      x⁻¹ * (w0 • x) ∈
        MulAction.stabilizer (U ⧸ C.subgroupOf U) (μraw j) := by
    rw [MulAction.mem_stabilizer_iff]
    exact hfix_delta
  have hdelta_one : x⁻¹ * (w0 • x) = 1 := by
    have hstab :=
      rawCoordinateMulAction_stabilizer_eq_bot_sec9
        (hcase := hcase) H hHcard hHnorm hHsup ρ hρaction (μraw j)
    have hbot :
        x⁻¹ * (w0 • x) ∈ (⊥ : Subgroup (U ⧸ C.subgroupOf U)) := by
      simpa [instAction] using (by simpa [hstab] using hdelta_mem)
    exact Subgroup.mem_bot.mp hbot
  have hgen_fix :
      w0 • x = x := by
    have hmul := congrArg (fun y : U ⧸ C.subgroupOf U => x * y) hdelta_one
    simpa [mul_assoc] using hmul
  have hxfix :
      x ∈ fixedPointSubgroup W1 (U ⧸ C.subgroupOf U) := by
    intro w
    have hw : w ∈ Subgroup.zpowers w0 := by
      rw [hw0gen]
      exact Subgroup.mem_top w
    exact smul_eq_self_of_mem_zpowers hw hgen_fix
  have hxone : x = 1 := by
    have hxbot :
        x ∈ (⊥ : Subgroup (U ⧸ C.subgroupOf U)) := by
      simpa [hfixedBot] using hxfix
    exact Subgroup.mem_bot.mp hxbot
  have hraw_eq : μraw j = μraw i := by
    simpa [hxone] using hx
  exact (hμraw_inj hraw_eq).symm

private theorem H0CLinearCandidateXmu_transported_final_injective_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hμrawOrderedActionData :
      H0CLinearCandidateXmuOrderedTransportedRawActionData_sec9
        (MF := MF) (U := U) (W1 := W1) (H0 := H0) (C := C)
        p q aρ H hHcard ρ μraw)
    (hW1Inertia :
      let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
      let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
      let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
      let HCD : Subgroup Dm := HCm.subgroupOf Dm
      let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
        rawCoordinateMulAction_sec9 p q H hHcard ρ
      letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
      let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
      let instFintypeι : Fintype ι := Fintype.ofFinite ι
      let instDecidableEqι : DecidableEq ι := Classical.decEq ι
      letI : Fintype ι := instFintypeι
      letI : DecidableEq ι := instDecidableEqι
      let orbit : κ → ι := fun k => Quotient.mk'' k
      let ψ : ι → Section1.ClassFunction HCm :=
        fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
      let θ : ι → Section1.ClassFunction Dm :=
        fun i =>
          Section1.inducedCF HCD
            (Section1.subgroupOfClassFunction (ψ i))
      let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
        fun i => orbit (μraw i)
      H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9 M W1 p ι
        μorbit θ) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
        let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
        let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
        let HCD : Subgroup Dm := HCm.subgroupOf Dm
        let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
        let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
        let instFintypeι : Fintype ι := Fintype.ofFinite ι
        let instDecidableEqι : DecidableEq ι := Classical.decEq ι
        letI : Fintype ι := instFintypeι
        letI : DecidableEq ι := instDecidableEqι
        let orbit : κ → ι := fun k => Quotient.mk'' k
        let ψ : ι → Section1.ClassFunction HCm :=
          fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
        let θ : ι → Section1.ClassFunction Dm :=
          fun i =>
            Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction (ψ i))
        let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
          fun i => orbit (μraw i)
        H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9 M p ι
          μorbit θ := by
  classical
  intro hψformula hcase hBarU
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
    fun i => orbit (μraw i)
  have hμinj : Function.Injective μorbit := by
    simpa [κ, instAction, orbit, μorbit] using
      H0CLinearCandidateXmu_transported_muorbit_injective_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
        ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup μraw
        hμrawOrderedActionData
        (by simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ, μorbit] using hW1Inertia)
        hψformula hcase hBarU
  have hnormalHCD : HCD.Normal := by
    dsimp [HCD, HCm, Dm]
    exact theorem_9_8_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C p q a ubar hcase hBarU
  letI : HCD.Normal := hnormalHCD
  have hrawCoord :
      (∀ k : κ,
        Section1.inertiaSubgroup HCD
            (Section1.subgroupOfClassFunction
              ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k)) =
          HCD) ∧
        ∀ k l : κ,
          (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) k =
            (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) l ↔
              MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l := by
    simpa [instAction, κ, Dm, HCm, HCD] using
      theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup ρ hρcyc hρcard
        hρaction hρker hconj hH0CinfMF hsup ψHC hcase hψformula hnormalHCD
  have hIeq : ∀ i : ι,
      Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ i)) = HCD := by
    intro i
    simpa [ψ, HCm] using hrawCoord.1 (Quotient.out i)
  have hθinj : Function.Injective θ := by
    intro i j hij
    have hout :
        MulAction.orbitRel (U ⧸ C.subgroupOf U) κ (Quotient.out i) (Quotient.out j) := by
      rw [← hrawCoord.2]
      simpa [θ, ψ, Dm, HCm, HCD] using hij
    have hi : Quotient.mk'' (Quotient.out i : κ) = i :=
      Quotient.out_eq' i
    have hj : Quotient.mk'' (Quotient.out j : κ) = j :=
      Quotient.out_eq' j
    exact (hi.symm.trans (Quotient.sound hout)).trans hj
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let hMFHC : MF ≤ HC := le_sup_left
  let e : (MF ⧸ H0.subgroupOf MF) ≃*
      (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
  let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  have hψformula' : ψHC = fun f => Section1.quotientCharacterInflation H0C HC (θHC f) := by
    simpa [κ, HC, H0C, hMFHC, e, θH, θHC] using hψformula
  have hψirr : ∀ f : κ, Section1.IsIrreducibleCharacterOnGroup (ψHC f) := by
    intro f
    rw [hψformula']
    exact Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      H0C HC (θHC f)
  have hψdeg : ∀ f : κ, Section1.degree (ψHC f) = (1 : ℂ) := by
    intro f
    rw [hψformula']
    exact Section1.quotientCharacterInflation_degree H0C HC (θHC f)
  have hψker : ∀ f : κ,
      Section1.subgroupInKernel' (ψHC f) (H0C.subgroupOf HC) := by
    intro f
    rw [hψformula']
    exact Section1.subgroupInKernel'_quotientCharacterInflation H0C HC (θHC f)
  have hqpos : 0 < q := (case_9_7_a_q_prime_sec9 hcase).pos
  have hθHne : ∀ f : κ, θH f ≠ 1 := by
    intro f
    exact componentProductLinearCharacter_ne_one_sec9 p q H hHcard hHindep hHsup
      f.down ⟨0, hqpos⟩
  have hψnonker : ∀ f : κ,
      ¬ Section1.subgroupInKernel' (ψHC f) (MF.subgroupOf HC) := by
    intro f hkerMF
    exact hθHne f <| by
      ext x
      have hxker : ψHC f (Subgroup.inclusion hMFHC x) =
          Section1.degree (ψHC f) := by
        exact hkerMF ⟨Subgroup.inclusion hMFHC x, by
          simp [Subgroup.mem_subgroupOf, HC]⟩
      have hqval : θH f x = 1 := by
        have hxval := hxker
        rw [hψformula', Section1.quotientCharacterInflation_degree] at hxval
        have hxval' :
            ((θHC f) (QuotientGroup.mk' (H0C.subgroupOf HC)
                (Subgroup.inclusion hMFHC x)) : ℂˣ) = (1 : ℂˣ) := by
          exact Units.ext (by
            simpa [Section1.quotientCharacterInflation] using hxval)
        have heq : QuotientGroup.mk' (H0C.subgroupOf HC)
              (Subgroup.inclusion hMFHC x) = e x := rfl
        have hunit : (θHC f) (e x) = 1 := by
          simpa [heq] using hxval'
        have hunit' : θH f x = 1 := by
          simpa [θHC] using hunit
        exact hunit'
      exact congrArg Units.val (by simpa using hqval)
  have hθdata_full :
      ∀ i : ι,
        Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
          ¬ Section1.subgroupInKernel' (θ i)
            ((MF.subgroupOf M).subgroupOf Dm) ∧
          Section1.subgroupInKernel' (θ i)
            (((H0 ⊔ C).subgroupOf M).subgroupOf Dm) ∧
          Section1.IsIrreducibleCharacterOnGroup (ψ i) ∧
          Section1.degree (ψ i) = (1 : ℂ) :=
    H0CLinearCandidateXtheta_theta_orbit_entry_data_sec9
      M MF U W1 W2 H0 C p q a (ψHC := ψHC) (ι := ι) Quotient.out
      hcase hψirr hψdeg hψker hψnonker hnormalHCD hIeq
  have hθclass : ∀ i : ι, Section1.IsClassFunction (θ i) := by
    intro i
    dsimp [θ]
    exact Section1.inducedCF_isClassFunction HCD (Section1.subgroupOfClassFunction (ψ i))
  have hconstFinal :
      H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9 M MF H0 C p
        ι μorbit θ :=
    H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_of_W1InertiaData_sec9
      M MF U W1 W2 H0 C p q a μorbit θ hcase hθclass
      (by simpa [μorbit] using hW1Inertia)
  have hfinalInertia :
      H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9 M MF H0 C p
        ι μorbit θ := by
    dsimp [H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9] at hconstFinal
    refine ⟨hθinj, ?_, ?_⟩
    · simpa [μorbit, θ, Dm, HCm, HCD] using hconstFinal
    · intro i
      rcases hθdata_full i with ⟨hθirr, hθnotMF, hθker, _hψirr_i, _hψdeg_i⟩
      exact ⟨hθirr, hθnotMF, hθker⟩
  simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ, μorbit] using
    H0CLinearCandidateXmuFinalInjectiveDataWithRaw_of_finalInertiaData_sec9
      M MF H0 C p μorbit θ hμinj hfinalInertia


private theorem
    H0CLinearCandidateXmu_ordered_generator_quotient_product_rotation_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (_hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [_hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (_hρcyc : ∀ i, IsCyclic (ρ i).range)
    (_hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (_hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (_hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (_hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (_horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hW1M : W1 ≤ M)
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hμrawOrderedData :
      H0CLinearCandidateXmuOrderedTransportedRawCoordinateData_sec9
        (MF := MF) (H0 := H0) (W1 := W1) p q H hHcard w0 μraw)
    (hqpos : 0 < q)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G))
    (χbar : Fin q → (U ⧸ C.subgroupOf U) →*
      Multiplicative (ZMod aρ))
    (_hχsep :
      ∀ i, ∀ x y : U ⧸ C.subgroupOf U,
        χbar i x = χbar i y → ρ i x = ρ i y)
    (_hχtransition :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      ∀ x : U,
        ∀ i,
          χbar i (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) =
            χbar (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
              (QuotientGroup.mk' (C.subgroupOf U) x))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (_hBarU : quotientBarUCardinality U C ubar) :
    let HC : Subgroup G := MF ⊔ C
    let H0C : Subgroup G := H0 ⊔ C
    let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
      quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
    let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
      fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
    ∀ hconjHC : ∀ h : HC, (w0 : G) * (h : G) * (w0 : G)⁻¹ ∈ HC,
      ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
        ∀ h : HC,
          θH (μraw i)
              (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC)
                ⟨(w0 : G) * (h : G) * (w0 : G)⁻¹, hconjHC h⟩)) =
            θH (μraw i)
              (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) h)) := by
  -- restrictions: `w0` rotates the ordered internal-product factors of
  -- the transported `mu_f`, including the wraparound coordinate.
  classical
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  rcases hsucc ⟨0, hqpos⟩ with ⟨hconjMF, action, haction, _hmap0⟩
  have hmap_each :
      ∀ j : Fin q,
        (H j).map action.toMonoidHom =
          H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j) := by
    intro j
    rcases hsucc j with ⟨hconjMF_j, action_j, haction_j, hmap_j⟩
    have haction_eq : action_j = action := by
      ext x
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨m, rfl⟩
      calc
        action_j (QuotientGroup.mk' (H0.subgroupOf MF) m) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjMF_j m⟩ := haction_j m
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjMF m⟩ := by
              congr 1
        _ = action (QuotientGroup.mk' (H0.subgroupOf MF) m) := (haction m).symm
    simpa [haction_eq] using hmap_j.symm
  have hconjMFpos : ∀ h : MF, (w0 : G) * (h : G) * (w0 : G)⁻¹ ∈ MF :=
    conj_inv_mem_of_conj_mem_finite_sec9 hconjMF
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hCcent : quotientCentralizerIn MF H0 U C :=
    case_9_7_a_quotientCentralizerIn_sec9 hcase
  have hpprime : Nat.Prime p := case_9_7_a_p_prime_sec9 hcase
  have hpData :
      ∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
            quotientChiefFactorData_9_6 M MF H0 W1 hp := by
    rcases hcase with
      ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, hpData, _hrest⟩
    exact hpData
  have hH0CnormalM : (H0C.subgroupOf M).Normal := by
    dsimp [H0C]
    exact theorem_9_H0C_normal_M_source_core_sec9
      M MF U W1 W2 H0 C p q h92 hH0MF hCcent hpprime hpData
  have hH0CleD : H0C ≤ ambientDerivedSubgroup M := by
    dsimp [H0C]
    exact theorem_9_H0C_le_ambientDerived_of_source_sec9
      M MF U W1 W2 H0 C q h92 hH0MF hCcent
  have hDleM : ambientDerivedSubgroup M ≤ M :=
    section12_ambientDerivedSubgroup_le (E := M)
  have hH0CleM : H0C ≤ M := hH0CleD.trans hDleM
  let w0M : M := ⟨(w0 : G), hW1M w0.property⟩
  have hconjH0C : ∀ h : H0C, (w0 : G) * (h : G) * (w0 : G)⁻¹ ∈ H0C := by
    intro h
    let hM : M := ⟨(h : G), hH0CleM h.property⟩
    let hH0CM : H0C.subgroupOf M := ⟨hM, by
      simp [H0C, hM, Subgroup.mem_subgroupOf]⟩
    have hmem :
        w0M * hH0CM * w0M⁻¹ ∈ H0C.subgroupOf M :=
      hH0CnormalM.conj_mem hH0CM hH0CM.property w0M
    simpa [H0C, w0M, hM, hH0CM, Subgroup.mem_subgroupOf, mul_assoc] using hmem
  have haction_symm :
      ∀ h : MF,
        action.symm (QuotientGroup.mk' (H0.subgroupOf MF) h) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(w0 : G) * (h : G) * (w0 : G)⁻¹, hconjMFpos h⟩ := by
    rcases quotientSubgroupConjugateByElement_action_symm_apply_sec9
        (hsucc ⟨0, hqpos⟩) with
      ⟨_hconjMF', action', haction', _hmap', _hconjInvMF', hactionInv'⟩
    have haction_eq : action' = action := by
      ext x
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨m, rfl⟩
      calc
        action' (QuotientGroup.mk' (H0.subgroupOf MF) m) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), _hconjMF' m⟩ := haction' m
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjMF m⟩ := by
              congr 1
        _ = action (QuotientGroup.mk' (H0.subgroupOf MF) m) := (haction m).symm
    intro h
    have hval := hactionInv' h
    simpa [haction_eq] using hval
  have htheta_action :
      ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
        (θH (μraw i)).comp action.symm.toMonoidHom = θH (μraw i) := by
    have hsucc_surj :
        Function.Surjective (theorem_9_7_fin_cyclic_succ_sec9 hqpos) := by
      intro j
      by_cases hj0 : j.1 = 0
      · refine ⟨⟨q - 1, by omega⟩, ?_⟩
        apply Fin.ext
        have hwrap : ¬ q - 1 + 1 < q := by omega
        simp [theorem_9_7_fin_cyclic_succ_sec9, hwrap, hj0]
      · refine ⟨⟨j.1 - 1, by omega⟩, ?_⟩
        apply Fin.ext
        have hnext : j.1 - 1 + 1 < q := by omega
        simp [theorem_9_7_fin_cyclic_succ_sec9, hnext]
        omega
    have hiSup_succ :
        (iSup fun j : Fin q => H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)) =
          iSup H := by
      apply le_antisymm
      · refine iSup_le ?_
        intro j
        exact le_iSup H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)
      · refine iSup_le ?_
        intro j
        rcases hsucc_surj j with ⟨k, hk⟩
        simpa [hk] using
          (le_iSup
            (fun k : Fin q => H (theorem_9_7_fin_cyclic_succ_sec9 hqpos k)) k)
    have hsup_succ :
        (iSup fun j : Fin q => H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)) =
          ⊤ := by
      rw [hiSup_succ, hHsup]
    have hcomponent_step :
        ∀ idx : H0CLinearCandidateXmuRawIndex_sec9 p,
          ∀ j : Fin q,
            ∀ x : H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j),
              ∀ y : H j,
                action (y : MF ⧸ H0.subgroupOf MF) = x →
                  ((nonprincipalLinearCharacterEquivFin_sec9 (H j) p (hHcard j))
                      ((μraw idx).down j)).1 y =
                    ((nonprincipalLinearCharacterEquivFin_sec9
                        (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)) p
                        (hHcard (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)))
                      ((μraw idx).down
                        (theorem_9_7_fin_cyclic_succ_sec9 hqpos j))).1 x := by
      -- the wraparound case uses `w0 ^ q = 1` from `hw0gen`.
      rcases hμrawOrderedData with ⟨hqposμ, _hwμ, E, hE, hμraw_eq⟩
      let base : Fin q := ⟨0, hqposμ⟩
      intro idx j x y hyx
      let sj : Fin q := theorem_9_7_fin_cyclic_succ_sec9 hqpos j
      have hw0q : w0 ^ q = 1 := by
        rw [← h92.q_eq, ← orderOf_eq_card_of_zpowers_eq_top hw0gen]
        exact pow_orderOf_eq_one w0
      have hpow_stepW1 : w0 ^ sj.1 = w0 ^ j.1 * w0 := by
        by_cases hnext : j.1 + 1 < q
        · simp [sj, theorem_9_7_fin_cyclic_succ_sec9, hnext, pow_succ]
        · have hjq : j.1 + 1 = q := by omega
          calc
            w0 ^ sj.1 = 1 := by
              simp [sj, theorem_9_7_fin_cyclic_succ_sec9, hnext]
            _ = w0 ^ j.1 * w0 := by
              symm
              calc
                w0 ^ j.1 * w0 = w0 ^ (j.1 + 1) := (pow_succ w0 j.1).symm
                _ = w0 ^ q := by rw [hjq]
                _ = 1 := hw0q
      have hpow_stepG :
          (((w0 ^ sj.1 : W1) : G) =
            (((w0 ^ j.1 : W1) : G) * (w0 : G))) := by
        simpa using congrArg Subtype.val hpow_stepW1
      have hE_step :
          ∀ z : H base, (E sj z : MF ⧸ H0.subgroupOf MF) =
            action (E j z : MF ⧸ H0.subgroupOf MF) := by
        intro z
        rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF)
            (z : MF ⧸ H0.subgroupOf MF) with
          ⟨m, hm⟩
        have hmBase : QuotientGroup.mk' (H0.subgroupOf MF) m ∈ H base := by
          simp [base, hm]
        have hzmk :
            z = ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase⟩ := by
          apply Subtype.ext
          simpa using hm.symm
        rcases hE j with ⟨hconj_j, hE_j⟩
        rcases hE sj with ⟨hconj_sj, hE_sj⟩
        rw [hzmk]
        calc
          (E sj ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase⟩ :
              MF ⧸ H0.subgroupOf MF) =
              QuotientGroup.mk' (H0.subgroupOf MF)
                ⟨(((w0 ^ sj.1 : W1) : G))⁻¹ * (m : G) *
                    (((w0 ^ sj.1 : W1) : G)), hconj_sj m⟩ :=
            hE_sj m hmBase
          _ = action
              (QuotientGroup.mk' (H0.subgroupOf MF)
                ⟨(((w0 ^ j.1 : W1) : G))⁻¹ * (m : G) *
                    (((w0 ^ j.1 : W1) : G)), hconj_j m⟩) := by
            rw [haction]
            apply congrArg (QuotientGroup.mk' (H0.subgroupOf MF))
            apply Subtype.ext
            change (((w0 ^ sj.1 : W1) : G))⁻¹ * (m : G) *
                (((w0 ^ sj.1 : W1) : G)) =
              (w0 : G)⁻¹ *
                ((((w0 ^ j.1 : W1) : G))⁻¹ * (m : G) *
                  (((w0 ^ j.1 : W1) : G))) * (w0 : G)
            rw [hpow_stepG]
            group
          _ = action
              (E j ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase⟩ :
                MF ⧸ H0.subgroupOf MF) := by
            rw [hE_j m hmBase]
      let χbase :=
        ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p (hHcard base)) idx).1
      have hleft :
          ((nonprincipalLinearCharacterEquivFin_sec9 (H j) p (hHcard j))
              ((μraw idx).down j)).1 y =
            χbase ((E j).symm y) := by
        have hspec :=
          H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_component_spec_sec9
            p q H hHcard base E idx j
        have happ := congrArg (fun χ : H j →* ℂˣ => χ y) hspec
        simpa [χbase, hμraw_eq, MonoidHom.comp_apply] using happ
      have hright :
          ((nonprincipalLinearCharacterEquivFin_sec9 (H sj) p (hHcard sj))
              ((μraw idx).down sj)).1 x =
            χbase ((E sj).symm x) := by
        have hspec :=
          H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_component_spec_sec9
            p q H hHcard base E idx sj
        have happ := congrArg (fun χ : H sj →* ℂˣ => χ x) hspec
        simpa [χbase, hμraw_eq, sj, MonoidHom.comp_apply] using happ
      have harg :
          (E j).symm y = (E sj).symm x := by
        have hEz :
            E sj ((E j).symm y) = x := by
          apply Subtype.ext
          calc
            (E sj ((E j).symm y) : MF ⧸ H0.subgroupOf MF) =
                action
                  (E j ((E j).symm y) : MF ⧸ H0.subgroupOf MF) :=
              hE_step ((E j).symm y)
            _ = action (y : MF ⧸ H0.subgroupOf MF) := by
              simp
            _ = (x : MF ⧸ H0.subgroupOf MF) := hyx
        rw [← hEz]
        simp
      calc
        ((nonprincipalLinearCharacterEquivFin_sec9 (H j) p (hHcard j))
            ((μraw idx).down j)).1 y = χbase ((E j).symm y) := hleft
        _ = χbase ((E sj).symm x) := by rw [harg]
        _ = ((nonprincipalLinearCharacterEquivFin_sec9 (H sj) p (hHcard sj))
            ((μraw idx).down sj)).1 x := hright.symm
    intro idx
    apply monoidHom_ext_of_iSup_eq_top_sec9
      (fun j : Fin q => H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j))
      hsup_succ
    intro j x
    have hxmap :
        (x : MF ⧸ H0.subgroupOf MF) ∈ (H j).map action.toMonoidHom := by
      rw [hmap_each j]
      exact x.property
    rcases hxmap with ⟨y, hy, hyx⟩
    let yj : H j := ⟨y, hy⟩
    have hsymm_y :
        action.symm (x : MF ⧸ H0.subgroupOf MF) = (yj : MF ⧸ H0.subgroupOf MF) := by
      rw [← hyx]
      simp [yj]
    have hleft :
        θH (μraw idx) (action.symm (x : MF ⧸ H0.subgroupOf MF)) =
          ((nonprincipalLinearCharacterEquivFin_sec9 (H j) p (hHcard j))
              ((μraw idx).down j)).1 yj := by
      rw [hsymm_y]
      simpa [θH] using
        componentProductLinearCharacter_apply_subgroup_sec9
          p q H hHcard hHindep hHsup (μraw idx).down j yj
    have hright :
        θH (μraw idx) (x : MF ⧸ H0.subgroupOf MF) =
          ((nonprincipalLinearCharacterEquivFin_sec9
              (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)) p
              (hHcard (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)))
            ((μraw idx).down (theorem_9_7_fin_cyclic_succ_sec9 hqpos j))).1 x := by
      simpa [θH] using
        componentProductLinearCharacter_apply_subgroup_sec9
          p q H hHcard hHindep hHsup (μraw idx).down
          (theorem_9_7_fin_cyclic_succ_sec9 hqpos j) x
    calc
      θH (μraw idx) (action.symm (x : MF ⧸ H0.subgroupOf MF)) =
          ((nonprincipalLinearCharacterEquivFin_sec9 (H j) p (hHcard j))
              ((μraw idx).down j)).1 yj := hleft
      _ = ((nonprincipalLinearCharacterEquivFin_sec9
              (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)) p
              (hHcard (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)))
            ((μraw idx).down
              (theorem_9_7_fin_cyclic_succ_sec9 hqpos j))).1 x :=
          hcomponent_step idx j x yj (by simpa [yj] using hyx)
      _ = θH (μraw idx) (x : MF ⧸ H0.subgroupOf MF) := hright.symm
  dsimp only
  intro hconjHC i h
  have hquot_h :
      e.symm
          (QuotientGroup.mk' (H0C.subgroupOf HC)
            ⟨(w0 : G) * (h : G) * (w0 : G)⁻¹, hconjHC h⟩) =
        action.symm (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) h)) := by
    exact quotientInfSupEquiv_symm_conj_eq_mulAut_sec9
      MF H0 HC H0C le_sup_left hH0CinfMF hsup
      (w0 : G) hconjMFpos hconjH0C hconjHC action.symm haction_symm h
  rw [hquot_h]
  have happ := congrArg
    (fun χ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ =>
      χ (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) h))) (htheta_action i)
  simpa [MonoidHom.comp_apply, HC, H0C, e, θH] using happ

private theorem H0CLinearCandidateXmu_ordered_generator_source_conjugation_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hW1M : W1 ≤ M)
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hμrawOrderedData :
      H0CLinearCandidateXmuOrderedTransportedRawCoordinateData_sec9
        (MF := MF) (H0 := H0) (W1 := W1) p q H hHcard w0 μraw)
    (hqpos : 0 < q)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G))
    (χbar : Fin q → (U ⧸ C.subgroupOf U) →*
      Multiplicative (ZMod aρ))
    (hχsep :
      ∀ i, ∀ x y : U ⧸ C.subgroupOf U,
        χbar i x = χbar i y → ρ i x = ρ i y)
    (hχtransition :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      ∀ x : U,
        ∀ i,
          χbar i (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) =
            χbar (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
              (QuotientGroup.mk' (C.subgroupOf U) x)) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a) →
      (hBarU : quotientBarUCardinality U C ubar) →
        let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
        let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
        let HCD : Subgroup Dm := HCm.subgroupOf Dm
        let w0M : M := ⟨(w0 : G), hW1M w0.property⟩
        ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
          let hDnormal : Dm.Normal := by
            simpa [Dm] using
              (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
          let hHCnormal : HCm.Normal := by
            dsimp [HCm]
            exact theorem_9_8_HC_normal_M_of_case_a_sec9
              M MF U W1 W2 H0 C p q a ubar hcase hBarU
          let source : Section1.ClassFunction HCD :=
            Section1.subgroupOfClassFunction (T := Dm)
              (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i)))
          ∀ h : HCD,
            source
              ⟨⟨w0M * ((h : Dm) : M) * w0M⁻¹,
                  hDnormal.conj_mem ((h : Dm) : M) (h : Dm).property w0M⟩,
                by
                  change w0M * ((h : Dm) : M) * w0M⁻¹ ∈ HCm
                  exact hHCnormal.conj_mem ((h : Dm) : M) h.property w0M⟩ =
              source h := by
  -- conjugation to a rotation of the transported `mu_f` product, and
  -- `cfConjgBigdprod` identifies the rotated component factors.
  classical
  intro hψformula hcase hBarU
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := HC.subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let w0M : M := ⟨(w0 : G), hW1M w0.property⟩
  have hHCleM : HC ≤ M := by
    dsimp [HC]
    exact (theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase).trans
      (section12_ambientDerivedSubgroup_le (E := M))
  have hHCnormal : HCm.Normal := by
    dsimp [HCm, HC]
    exact theorem_9_8_HC_normal_M_of_case_a_sec9
      M MF U W1 W2 H0 C p q a ubar hcase hBarU
  have hconjHC : ∀ h : HC, (w0 : G) * (h : G) * (w0 : G)⁻¹ ∈ HC := by
    intro h
    let hM : M := ⟨(h : G), hHCleM h.property⟩
    let hHCm : HCm := ⟨hM, by
      simp [HCm, HC, hM, Subgroup.mem_subgroupOf]⟩
    have hmem : w0M * hHCm * w0M⁻¹ ∈ HCm :=
      hHCnormal.conj_mem hHCm hHCm.property w0M
    simpa [HCm, HC, hM, hHCm, w0M, Subgroup.mem_subgroupOf, mul_assoc] using hmem
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  have hrot :
      ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
        ∀ h : HC,
          θH (μraw i)
              (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC)
                ⟨(w0 : G) * (h : G) * (w0 : G)⁻¹, hconjHC h⟩)) =
            θH (μraw i)
              (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) h)) := by
    simpa [HC, H0C, e, θH] using
      H0CLinearCandidateXmu_ordered_generator_quotient_product_rotation_core_sec9
        M MF U W1 W2 H0 C p q a aρ ubar H hHcard hHnorm hHindep hHsup
        ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup μraw
        hW1M w0 hw0gen hW1normU hμrawOrderedData hqpos hsucc χbar hχsep hχtransition
        hcase hBarU hconjHC
  dsimp only
  intro i h
  let hDnormal : Dm.Normal := by
    simpa [Dm] using
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  let hHCnormal' : HCm.Normal := by
    exact hHCnormal
  let hDm : Dm := (h : HCD)
  let hM : M := hDm
  let hHC : HC := ⟨(hM : G), by
    have hhHCm : hM ∈ HCm := h.property
    simpa [HCm, HC, hM, Subgroup.mem_subgroupOf] using hhHCm⟩
  have htargetHC :
      (⟨(w0 : G) * (hHC : G) * (w0 : G)⁻¹, hconjHC hHC⟩ : HC) =
        ⟨((⟨w0M * ((h : Dm) : M) * w0M⁻¹,
            hDnormal.conj_mem ((h : Dm) : M) (h : Dm).property w0M⟩ : Dm) : M),
          by
            change w0M * ((h : Dm) : M) * w0M⁻¹ ∈ HCm
            exact hHCnormal'.conj_mem ((h : Dm) : M) h.property w0M⟩ := by
    apply Subtype.ext
    simp [hHC, hM, hDm, w0M, mul_assoc]
  have hrot_i := hrot i hHC
  have hψapp :
      ψHC (μraw i) =
        Section1.quotientCharacterInflation H0C HC (θHC (μraw i)) := by
    simpa [HC, H0C, e, θH, θHC] using congrFun hψformula (μraw i)
  rw [hψapp]
  change
    (θHC (μraw i)
        (QuotientGroup.mk' (H0C.subgroupOf HC)
          (⟨((⟨w0M * ((h : Dm) : M) * w0M⁻¹,
              hDnormal.conj_mem ((h : Dm) : M) (h : Dm).property w0M⟩ : Dm) : M),
            by
              change w0M * ((h : Dm) : M) * w0M⁻¹ ∈ HCm
              exact hHCnormal'.conj_mem ((h : Dm) : M) h.property w0M⟩ : HC)) : ℂ) =
      (θHC (μraw i) (QuotientGroup.mk' (H0C.subgroupOf HC) hHC) : ℂ)
  rw [← htargetHC]
  exact congrArg Units.val hrot_i

private theorem H0CLinearCandidateXmu_ordered_generator_inertia_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hW1M : W1 ≤ M)
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hμrawOrderedData :
      H0CLinearCandidateXmuOrderedTransportedRawCoordinateData_sec9
        (MF := MF) (H0 := H0) (W1 := W1) p q H hHcard w0 μraw)
    (hqpos : 0 < q)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G))
    (χbar : Fin q → (U ⧸ C.subgroupOf U) →*
      Multiplicative (ZMod aρ))
    (hχsep :
      ∀ i, ∀ x y : U ⧸ C.subgroupOf U,
        χbar i x = χbar i y → ρ i x = ρ i y)
    (hχtransition :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      ∀ x : U,
        ∀ i,
          χbar i (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) =
            χbar (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
              (QuotientGroup.mk' (C.subgroupOf U) x)) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
        let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
        let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
        let HCD : Subgroup Dm := HCm.subgroupOf Dm
        let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
        let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
        let instFintypeι : Fintype ι := Fintype.ofFinite ι
        let instDecidableEqι : DecidableEq ι := Classical.decEq ι
        letI : Fintype ι := instFintypeι
        letI : DecidableEq ι := instDecidableEqι
        let orbit : κ → ι := fun k => Quotient.mk'' k
        let ψ : ι → Section1.ClassFunction HCm :=
          fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
        let θ : ι → Section1.ClassFunction Dm :=
          fun i =>
            Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction (ψ i))
        let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
          fun i => orbit (μraw i)
        ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
          (⟨(w0 : G), hW1M w0.property⟩ : M) ∈
            let hDnormal : Dm.Normal := by
              simpa [Dm] using
                (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
            letI : Dm.Normal := hDnormal
            Section1.inertiaSubgroup Dm (θ (μorbit i)) := by
  -- transported `mu_f` component product, hence fixes its induced orbit class.
  classical
  intro hψformula hcase hBarU
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
    fun i => orbit (μraw i)
  have hDnormal : Dm.Normal := by
    simpa [Dm] using
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  have hHCnormal : HCm.Normal := by
    dsimp [HCm]
    exact theorem_9_8_HC_normal_M_of_case_a_sec9
      M MF U W1 W2 H0 C p q a ubar hcase hBarU
  letI : HCm.Normal := hHCnormal
  let w0M : M := ⟨(w0 : G), hW1M w0.property⟩
  dsimp only
  intro i
  change Section1.conjugateOnNormal Dm (θ (μorbit i)) w0M = θ (μorbit i)
  have hrel_out :
      MulAction.orbitRel (U ⧸ C.subgroupOf U) κ
        (Quotient.out (μorbit i)) (μraw i) := by
    rw [← Quotient.eq'']
    simp [μorbit, orbit]
  have htheta_out :
      θ (μorbit i) =
        Section1.inducedCF HCD
          (Section1.subgroupOfClassFunction
            (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i)))) := by
    have hθeq :
        let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
        let HC : Subgroup G := MF ⊔ C
        let H0C : Subgroup G := H0 ⊔ C
        let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
        let HCm : Subgroup M := HC.subgroupOf M
        let HCD : Subgroup Dm := HCm.subgroupOf Dm
        letI : HCD.Normal := by
          dsimp [HCD, HCm, Dm]
          exact theorem_9_8_HC_normal_ambientDerived_subgroupOf_sec9
            M MF U W1 W2 H0 C p q a ubar hcase hBarU
        let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
          quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
        let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
            (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
          fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
        let θHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
            (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
          fun f => (θH f).comp e.symm.toMonoidHom
        let ψHC0 : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
            Section1.ClassFunction HC :=
          fun f => Section1.quotientCharacterInflation H0C HC (θHC f)
        let ψ0 : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
            Section1.ClassFunction HCm :=
          fun f => Section1.subgroupOfClassFunction (ψHC0 f)
        let θ0 : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
            Section1.ClassFunction Dm :=
          fun f => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ0 f))
        θ0 (Quotient.out (μorbit i)) = θ0 (μraw i) :=
      induced_eq_of_rawCoordinateMulAction_orbitRel_sec9
        M MF U W1 W2 H0 C p q a H hHcard hHnorm hHindep hHsup ρ hρaction hconj
        hH0CinfMF hsup hcase
        (by
          exact theorem_9_8_HC_normal_ambientDerived_subgroupOf_sec9
            M MF U W1 W2 H0 C p q a ubar hcase hBarU)
        (Quotient.out (μorbit i)) (μraw i)
        (by simpa [instAction, κ] using hrel_out)
    have hψformula_out : ψHC (Quotient.out (μorbit i)) =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))
          (Quotient.out (μorbit i)) := by
      simpa using congrFun hψformula (Quotient.out (μorbit i))
    have hψformula_app : ψHC (μraw i) =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f)) (μraw i) := by
      simpa using congrFun hψformula (μraw i)
    simpa [κ, Dm, HCm, HCD, instAction, orbit, μorbit, ψ, θ, hψformula_out,
      hψformula_app] using hθeq
  have hsource :
      Section1.conjugateOnNormal Dm
          (Section1.inducedCF HCD
            (Section1.subgroupOfClassFunction
              (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i))))) w0M =
        Section1.inducedCF HCD
          (Section1.subgroupOfClassFunction
            (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i)))) := by
    refine conjugateOnNormal_inducedCF_eq_of_subgroupOf_source_conjugation_sec9
      Dm HCm
      (Section1.subgroupOfClassFunction
        (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i))))
      (Section1.subgroupOfClassFunction
        (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i))))
      w0M ?_
    intro h
    exact H0CLinearCandidateXmu_ordered_generator_source_conjugation_core_sec9
      M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
      ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup μraw hW1M w0
      hw0gen hW1normU hμrawOrderedData hqpos hsucc χbar hχsep hχtransition
      hψformula hcase hBarU i h
  calc
    Section1.conjugateOnNormal Dm (θ (μorbit i)) w0M =
        Section1.conjugateOnNormal Dm
          (Section1.inducedCF HCD
            (Section1.subgroupOfClassFunction
              (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i))))) w0M := by
          rw [htheta_out]
    _ = Section1.inducedCF HCD
          (Section1.subgroupOfClassFunction
            (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i)))) := hsource
    _ = θ (μorbit i) := htheta_out.symm

private theorem H0CLinearCandidateXmu_transported_W1_generator_inertia_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hμrawOrderedActionData :
      H0CLinearCandidateXmuOrderedTransportedRawActionData_sec9
        (MF := MF) (U := U) (W1 := W1) (H0 := H0) (C := C)
        p q aρ H hHcard ρ μraw) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        ∃ hW1M : W1 ≤ M,
          ∃ w0 : W1,
            Subgroup.zpowers w0 = ⊤ ∧
              let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
              let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
              let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
              let HCD : Subgroup Dm := HCm.subgroupOf Dm
              let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
                rawCoordinateMulAction_sec9 p q H hHcard ρ
              letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
              let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
              let instFintypeι : Fintype ι := Fintype.ofFinite ι
              let instDecidableEqι : DecidableEq ι := Classical.decEq ι
              letI : Fintype ι := instFintypeι
              letI : DecidableEq ι := instDecidableEqι
              let orbit : κ → ι := fun k => Quotient.mk'' k
              let ψ : ι → Section1.ClassFunction HCm :=
                fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
              let θ : ι → Section1.ClassFunction Dm :=
                fun i =>
                  Section1.inducedCF HCD
                    (Section1.subgroupOfClassFunction (ψ i))
              let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
                fun i => orbit (μraw i)
              ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
                (⟨(w0 : G), hW1M w0.property⟩ : M) ∈
                  let hDnormal : Dm.Normal := by
                    simpa [Dm] using
                      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
                  letI : Dm.Normal := hDnormal
                  Section1.inertiaSubgroup Dm (θ (μorbit i)) := by
  -- rotates the transported component product and fixes the resulting
  -- induced `mu_f` character.
  classical
  intro hψformula hcase hBarU
  rcases hμrawOrderedActionData with
    ⟨hW1normU, w0, hw0gen, hμrawOrderedData, hqpos, hsucc, χbar,
      hχsep, hχtransition⟩
  refine ⟨W1_le_M_of_hypothesis_9_2_sec9 M MF U W1 W2 q hcase.1, w0,
    hw0gen, ?_⟩
  simpa using
    H0CLinearCandidateXmu_ordered_generator_inertia_bridge_sec9
      M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
      ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup μraw
      (W1_le_M_of_hypothesis_9_2_sec9 M MF U W1 W2 q hcase.1) w0 hw0gen
      hW1normU hμrawOrderedData hqpos hsucc χbar hχsep hχtransition
      hψformula hcase hBarU

private theorem H0CLinearCandidateXmu_transported_W1_inertia_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hμrawOrderedActionData :
      H0CLinearCandidateXmuOrderedTransportedRawActionData_sec9
        (MF := MF) (U := U) (W1 := W1) (H0 := H0) (C := C)
        p q aρ H hHcard ρ μraw) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
        let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
        let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
        let HCD : Subgroup Dm := HCm.subgroupOf Dm
        let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
        let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
        let instFintypeι : Fintype ι := Fintype.ofFinite ι
        let instDecidableEqι : DecidableEq ι := Classical.decEq ι
        letI : Fintype ι := instFintypeι
        letI : DecidableEq ι := instDecidableEqι
        let orbit : κ → ι := fun k => Quotient.mk'' k
        let ψ : ι → Section1.ClassFunction HCm :=
          fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
        let θ : ι → Section1.ClassFunction Dm :=
          fun i =>
            Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction (ψ i))
        let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
          fun i => orbit (μraw i)
        H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9 M W1 p ι
          μorbit θ := by
  classical
  intro hψformula hcase hBarU
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
    fun i => orbit (μraw i)
  rcases H0CLinearCandidateXmu_transported_W1_generator_inertia_source_core_sec9
      M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
      ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup μraw
      hμrawOrderedActionData
      hψformula hcase hBarU with
    ⟨hW1M, w0, hw0gen, hw0I⟩
  dsimp [H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9]
  intro i
  simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ, μorbit] using
    subgroupOf_le_inertiaSubgroup_of_zpowers_generator_mem_sec9
      Dm (θ (μorbit i)) w0 hW1M hw0gen
      (by
        simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ, μorbit] using
          hw0I i)

private theorem H0CLinearCandidateXmu_transported_orbit_W1_data_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
        let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
        let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
        let HCD : Subgroup Dm := HCm.subgroupOf Dm
        let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
        let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
        let instFintypeι : Fintype ι := Fintype.ofFinite ι
        let instDecidableEqι : DecidableEq ι := Classical.decEq ι
        letI : Fintype ι := instFintypeι
        letI : DecidableEq ι := instDecidableEqι
        let orbit : κ → ι := fun k => Quotient.mk'' k
        let ψ : ι → Section1.ClassFunction HCm :=
          fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
        let θ : ι → Section1.ClassFunction Dm :=
          fun i =>
            Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction (ψ i))
        H0CLinearCandidateXmuTransportedRawData_sec9 M W1 p κ ι orbit θ := by
  classical
  intro hψformula hcase hBarU
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  have horderedXmu_saved := horderedXmu
  rcases horderedXmu_saved with ⟨hW1normU, w0, hw0gen, hqpos, hsucc, χbar,
    hχsep, hχtransition⟩
  rcases H0CLinearCandidateXmuOrderedTransportedRawCoordinate_data_sec9
      (MF := MF) (H0 := H0) (W1 := W1) p q H hHcard w0 hqpos hsucc with
    ⟨μraw, hμrawOrderedData, hμrawData, _hμraw⟩
  refine ⟨μraw, ?_⟩
  have hμrawOrderedActionData :
      H0CLinearCandidateXmuOrderedTransportedRawActionData_sec9
        (MF := MF) (U := U) (W1 := W1) (H0 := H0) (C := C)
        p q aρ H hHcard ρ μraw := by
    exact ⟨hW1normU, w0, hw0gen, hμrawOrderedData, hqpos, hsucc, χbar,
      hχsep, hχtransition⟩
  have hW1Inertia :
      H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9 M W1 p ι
        (fun i : H0CLinearCandidateXmuRawIndex_sec9 p => orbit (μraw i)) θ := by
    simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ] using
      H0CLinearCandidateXmu_transported_W1_inertia_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
        ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup μraw
        hμrawOrderedActionData
        hψformula hcase hBarU
  have hfinalInjective :
      H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9 M p ι
        (fun i : H0CLinearCandidateXmuRawIndex_sec9 p => orbit (μraw i)) θ := by
    simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ] using
      H0CLinearCandidateXmu_transported_final_injective_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
        ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup μraw
        hμrawOrderedActionData
        (by simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ] using hW1Inertia)
        hψformula hcase hBarU
  exact ⟨hfinalInjective, hW1Inertia⟩

private theorem H0CLinearCandidateXmu_transported_raw_data_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
        let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
        let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
        let HCD : Subgroup Dm := HCm.subgroupOf Dm
        let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
        let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
        let instFintypeι : Fintype ι := Fintype.ofFinite ι
        let instDecidableEqι : DecidableEq ι := Classical.decEq ι
        letI : Fintype ι := instFintypeι
        letI : DecidableEq ι := instDecidableEqι
        let orbit : κ → ι := fun k => Quotient.mk'' k
        let ψ : ι → Section1.ClassFunction HCm :=
          fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
        let θ : ι → Section1.ClassFunction Dm :=
          fun i =>
            Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction (ψ i))
        H0CLinearCandidateXmuTransportedRawData_sec9 M W1 p κ ι orbit θ := by
  classical
  intro hψformula hcase hBarU
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ] using
    H0CLinearCandidateXmu_transported_orbit_W1_data_source_core_sec9
      M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
      ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup
      hψformula hcase hBarU

private theorem H0CLinearCandidateXmu_transported_final_image_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
          let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
          let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
          let HCD : Subgroup Dm := HCm.subgroupOf Dm
          let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
            rawCoordinateMulAction_sec9 p q H hHcard ρ
          letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
          let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
          let instFintypeι : Fintype ι := Fintype.ofFinite ι
          let instDecidableEqι : DecidableEq ι := Classical.decEq ι
          letI : Fintype ι := instFintypeι
          letI : DecidableEq ι := instDecidableEqι
          let ψ : ι → Section1.ClassFunction HCm :=
            fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
          let θ : ι → Section1.ClassFunction Dm :=
            fun i =>
              Section1.inducedCF HCD
                (Section1.subgroupOfClassFunction (ψ i))
          H0CLinearCandidateXmuFinalImageData_sec9 M MF H0 C p SH0C ι θ := by
  classical
  intro hψformula hcase hBarU hSH0C
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  let orbit : κ → ι := fun k => Quotient.mk'' k
  have htransport :
      H0CLinearCandidateXmuTransportedRawData_sec9 M W1 p κ ι orbit θ :=
    H0CLinearCandidateXmu_transported_raw_data_source_core_sec9
      M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
      ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup
      hψformula hcase hBarU
  rcases htransport with ⟨μraw, hfinalInjective, hW1Inertia⟩
  let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
    fun i => orbit (μraw i)
  have hnormalHCD : HCD.Normal := by
    dsimp [HCD, HCm, Dm]
    exact theorem_9_8_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C p q a ubar hcase hBarU
  letI : HCD.Normal := hnormalHCD
  have hrawCoord :
      (∀ k : κ,
        Section1.inertiaSubgroup HCD
            (Section1.subgroupOfClassFunction
              ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k)) =
          HCD) ∧
        ∀ k l : κ,
          (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) k =
            (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) l ↔
              MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l := by
    simpa [instAction, κ, Dm, HCm, HCD] using
      theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup ρ hρcyc hρcard
        hρaction hρker hconj hH0CinfMF hsup ψHC hcase hψformula hnormalHCD
  have hIeq : ∀ i : ι,
      Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ i)) = HCD := by
    intro i
    simpa [ψ, HCm] using hrawCoord.1 (Quotient.out i)
  have hθinj : Function.Injective θ := by
    intro i j hij
    have hout :
        MulAction.orbitRel (U ⧸ C.subgroupOf U) κ (Quotient.out i) (Quotient.out j) := by
      rw [← hrawCoord.2]
      simpa [θ, ψ, Dm, HCm, HCD] using hij
    have hi : Quotient.mk'' (Quotient.out i : κ) = i :=
      Quotient.out_eq' i
    have hj : Quotient.mk'' (Quotient.out j : κ) = j :=
      Quotient.out_eq' j
    exact (hi.symm.trans (Quotient.sound hout)).trans hj
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let hMFHC : MF ≤ HC := le_sup_left
  let e : (MF ⧸ H0.subgroupOf MF) ≃*
      (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
  let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  have hψformula' : ψHC = fun f => Section1.quotientCharacterInflation H0C HC (θHC f) := by
    simpa [κ, HC, H0C, hMFHC, e, θH, θHC] using hψformula
  have hψirr : ∀ f : κ, Section1.IsIrreducibleCharacterOnGroup (ψHC f) := by
    intro f
    rw [hψformula']
    exact Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      H0C HC (θHC f)
  have hψdeg : ∀ f : κ, Section1.degree (ψHC f) = (1 : ℂ) := by
    intro f
    rw [hψformula']
    exact Section1.quotientCharacterInflation_degree H0C HC (θHC f)
  have hψker : ∀ f : κ,
      Section1.subgroupInKernel' (ψHC f) (H0C.subgroupOf HC) := by
    intro f
    rw [hψformula']
    exact Section1.subgroupInKernel'_quotientCharacterInflation H0C HC (θHC f)
  have hqpos : 0 < q := (case_9_7_a_q_prime_sec9 hcase).pos
  have hθHne : ∀ f : κ, θH f ≠ 1 := by
    intro f
    exact componentProductLinearCharacter_ne_one_sec9 p q H hHcard hHindep hHsup
      f.down ⟨0, hqpos⟩
  have hψnonker : ∀ f : κ,
      ¬ Section1.subgroupInKernel' (ψHC f) (MF.subgroupOf HC) := by
    intro f hkerMF
    exact hθHne f <| by
      ext x
      have hxker : ψHC f (Subgroup.inclusion hMFHC x) =
          Section1.degree (ψHC f) := by
        exact hkerMF ⟨Subgroup.inclusion hMFHC x, by
          simp [Subgroup.mem_subgroupOf, HC]⟩
      have hqval : θH f x = 1 := by
        have hxval := hxker
        rw [hψformula', Section1.quotientCharacterInflation_degree] at hxval
        have hxval' :
            ((θHC f) (QuotientGroup.mk' (H0C.subgroupOf HC)
                (Subgroup.inclusion hMFHC x)) : ℂˣ) = (1 : ℂˣ) := by
          exact Units.ext (by
            simpa [Section1.quotientCharacterInflation] using hxval)
        have heq : QuotientGroup.mk' (H0C.subgroupOf HC)
              (Subgroup.inclusion hMFHC x) = e x := rfl
        have hunit : (θHC f) (e x) = 1 := by
          simpa [heq] using hxval'
        have hunit' : θH f x = 1 := by
          simpa [θHC] using hunit
        exact hunit'
      exact congrArg Units.val (by simpa using hqval)
  have hθdata_full :
      ∀ i : ι,
        Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
          ¬ Section1.subgroupInKernel' (θ i)
            ((MF.subgroupOf M).subgroupOf Dm) ∧
          Section1.subgroupInKernel' (θ i)
            (((H0 ⊔ C).subgroupOf M).subgroupOf Dm) ∧
          Section1.IsIrreducibleCharacterOnGroup (ψ i) ∧
          Section1.degree (ψ i) = (1 : ℂ) :=
    H0CLinearCandidateXtheta_theta_orbit_entry_data_sec9
      M MF U W1 W2 H0 C p q a (ψHC := ψHC) (ι := ι) Quotient.out
      hcase hψirr hψdeg hψker hψnonker hnormalHCD hIeq
  have hθclass : ∀ i : ι, Section1.IsClassFunction (θ i) := by
    intro i
    dsimp [θ]
    exact Section1.inducedCF_isClassFunction HCD (Section1.subgroupOfClassFunction (ψ i))
  have hconstFinal :
      H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9 M MF H0 C p
        ι μorbit θ :=
    H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_of_W1InertiaData_sec9
      M MF U W1 W2 H0 C p q a μorbit θ hcase hθclass
      (by simpa [μorbit] using hW1Inertia)
  have hfinalInertia :
      H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9 M MF H0 C p
        ι μorbit θ := by
    dsimp [H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9] at hconstFinal
    refine ⟨hθinj, ?_, ?_⟩
    · simpa [μorbit, θ, Dm, HCm, HCD] using hconstFinal
    · intro i
      rcases hθdata_full i with ⟨hθirr, hθnotMF, hθker, _hψirr_i, _hψdeg_i⟩
      exact ⟨hθirr, hθnotMF, hθker⟩
  have hcore :
      H0CLinearCandidateXmuSmuCoreDataWithRaw_sec9 M MF H0 C p SH0C
        ι μorbit θ :=
    H0CLinearCandidateXmuSmuCoreDataWithRaw_of_finalInertiaData_sec9
      M MF U W1 W2 H0 C p q a SH0C μorbit θ hcase hSH0C
      hfinalInertia hfinalInjective
  have hsmu :
      H0CLinearCandidateXmuSmuDataWithRaw_sec9 M MF H0 C p SH0C
        ι μorbit θ :=
    H0CLinearCandidateXmuSmuDataWithRaw_of_coreData_sec9
      M MF H0 C p SH0C ι μorbit θ hcore
  have hsep :
      H0CLinearCandidateXmuFinalSeparationDataWithRaw_sec9 M MF H0 C p
        SH0C ι μorbit θ :=
    H0CLinearCandidateXmuFinalSeparationDataWithRaw_of_smuData_sec9
      M MF H0 C p SH0C ι μorbit θ hsmu
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hC : quotientCentralizerIn MF H0 U C :=
    case_9_7_a_quotientCentralizerIn_sec9 hcase
  have hpprime : Nat.Prime p := case_9_7_a_p_prime_sec9 hcase
  have hpData :
      ∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
            quotientChiefFactorData_9_6 M MF H0 W1 hp := by
    rcases hcase with
      ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, hpData, _hrest⟩
    exact hpData
  have hH0CnormalM : ((H0 ⊔ C).subgroupOf M).Normal :=
    theorem_9_H0C_normal_M_source_core_sec9 M MF U W1 W2 H0 C p q
      h92 hH0MF hC hpprime hpData
  have hH0CD : H0 ⊔ C ≤ ambientDerivedSubgroup M :=
    theorem_9_H0C_le_ambientDerived_of_source_sec9 M MF U W1 W2 H0 C q
      h92 hH0MF hC
  have hredCard :
      (reducibleCharacterFilter_sec9 M SH0C).card = p - 1 :=
    theorem_9_nb_redM_count_of_normal_le_inter_source_core_sec9
      M MF U W1 W2 H0 (H0 ⊔ C) p q SH0C h92 hH0MF hpprime hpData
      hH0CnormalM hH0CD hH0CinfMF hSH0C
  have hconcrete :
      H0CLinearCandidateXmuConcreteFinalImageDataWithRaw_sec9 M MF H0 C p
        SH0C ι μorbit θ :=
    H0CLinearCandidateXmuConcreteFinalImageDataWithRaw_of_final_separation_sec9
      M MF H0 C p SH0C ι μorbit θ hredCard hsep
  exact H0CLinearCandidateXmuFinalImageData_of_concrete_final_image_withRaw_sec9
    M MF H0 C p SH0C ι μorbit θ hconcrete

private theorem H0CLinearCandidateXmu_transported_residual_data_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          H0CLinearCandidateXmuResidualData_sec9 M MF H0 C p SH0C := by
  classical
  intro hψformula hcase hBarU hSH0C
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  let orbit : κ → ι := fun k => Quotient.mk'' k
  have htransport :
      H0CLinearCandidateXmuTransportedRawData_sec9 M W1 p κ ι orbit θ :=
    H0CLinearCandidateXmu_transported_raw_data_source_core_sec9
      M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
      ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup
      hψformula hcase hBarU
  rcases htransport with ⟨μraw, hfinalInjective, hW1Inertia⟩
  let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
    fun i => orbit (μraw i)
  have hnormalHCD : HCD.Normal := by
    dsimp [HCD, HCm, Dm]
    exact theorem_9_8_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C p q a ubar hcase hBarU
  letI : HCD.Normal := hnormalHCD
  have hrawCoord :
      (∀ k : κ,
        Section1.inertiaSubgroup HCD
            (Section1.subgroupOfClassFunction
              ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k)) =
          HCD) ∧
        ∀ k l : κ,
          (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) k =
            (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) l ↔
              MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l := by
    simpa [instAction, κ, Dm, HCm, HCD] using
      theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup ρ hρcyc hρcard
        hρaction hρker hconj hH0CinfMF hsup ψHC hcase hψformula hnormalHCD
  have hIeq : ∀ i : ι,
      Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ i)) = HCD := by
    intro i
    simpa [ψ, HCm] using hrawCoord.1 (Quotient.out i)
  have hθinj : Function.Injective θ := by
    intro i j hij
    have hout :
        MulAction.orbitRel (U ⧸ C.subgroupOf U) κ (Quotient.out i) (Quotient.out j) := by
      rw [← hrawCoord.2]
      simpa [θ, ψ, Dm, HCm, HCD] using hij
    have hi : Quotient.mk'' (Quotient.out i : κ) = i :=
      Quotient.out_eq' i
    have hj : Quotient.mk'' (Quotient.out j : κ) = j :=
      Quotient.out_eq' j
    exact (hi.symm.trans (Quotient.sound hout)).trans hj
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let hMFHC : MF ≤ HC := le_sup_left
  let e : (MF ⧸ H0.subgroupOf MF) ≃*
      (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
  let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  have hψformula' : ψHC = fun f => Section1.quotientCharacterInflation H0C HC (θHC f) := by
    simpa [κ, HC, H0C, hMFHC, e, θH, θHC] using hψformula
  have hψirr : ∀ f : κ, Section1.IsIrreducibleCharacterOnGroup (ψHC f) := by
    intro f
    rw [hψformula']
    exact Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      H0C HC (θHC f)
  have hψdeg : ∀ f : κ, Section1.degree (ψHC f) = (1 : ℂ) := by
    intro f
    rw [hψformula']
    exact Section1.quotientCharacterInflation_degree H0C HC (θHC f)
  have hψker : ∀ f : κ,
      Section1.subgroupInKernel' (ψHC f) (H0C.subgroupOf HC) := by
    intro f
    rw [hψformula']
    exact Section1.subgroupInKernel'_quotientCharacterInflation H0C HC (θHC f)
  have hqpos : 0 < q := (case_9_7_a_q_prime_sec9 hcase).pos
  have hθHne : ∀ f : κ, θH f ≠ 1 := by
    intro f
    exact componentProductLinearCharacter_ne_one_sec9 p q H hHcard hHindep hHsup
      f.down ⟨0, hqpos⟩
  have hψnonker : ∀ f : κ,
      ¬ Section1.subgroupInKernel' (ψHC f) (MF.subgroupOf HC) := by
    intro f hkerMF
    exact hθHne f <| by
      ext x
      have hxker : ψHC f (Subgroup.inclusion hMFHC x) =
          Section1.degree (ψHC f) := by
        exact hkerMF ⟨Subgroup.inclusion hMFHC x, by
          simp [Subgroup.mem_subgroupOf, HC]⟩
      have hqval : θH f x = 1 := by
        have hxval := hxker
        rw [hψformula', Section1.quotientCharacterInflation_degree] at hxval
        have hxval' :
            ((θHC f) (QuotientGroup.mk' (H0C.subgroupOf HC)
                (Subgroup.inclusion hMFHC x)) : ℂˣ) = (1 : ℂˣ) := by
          exact Units.ext (by
            simpa [Section1.quotientCharacterInflation] using hxval)
        have heq : QuotientGroup.mk' (H0C.subgroupOf HC)
              (Subgroup.inclusion hMFHC x) = e x := rfl
        have hunit : (θHC f) (e x) = 1 := by
          simpa [heq] using hxval'
        have hunit' : θH f x = 1 := by
          simpa [θHC] using hunit
        exact hunit'
      exact congrArg Units.val (by simpa using hqval)
  have hθdata_full :
      ∀ i : ι,
        Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
          ¬ Section1.subgroupInKernel' (θ i)
            ((MF.subgroupOf M).subgroupOf Dm) ∧
          Section1.subgroupInKernel' (θ i)
            (((H0 ⊔ C).subgroupOf M).subgroupOf Dm) ∧
          Section1.IsIrreducibleCharacterOnGroup (ψ i) ∧
          Section1.degree (ψ i) = (1 : ℂ) :=
    H0CLinearCandidateXtheta_theta_orbit_entry_data_sec9
      M MF U W1 W2 H0 C p q a (ψHC := ψHC) (ι := ι) Quotient.out
      hcase hψirr hψdeg hψker hψnonker hnormalHCD hIeq
  have hθclass : ∀ i : ι, Section1.IsClassFunction (θ i) := by
    intro i
    dsimp [θ]
    exact Section1.inducedCF_isClassFunction HCD (Section1.subgroupOfClassFunction (ψ i))
  have hconstFinal :
      H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9 M MF H0 C p
        ι μorbit θ :=
    H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_of_W1InertiaData_sec9
      M MF U W1 W2 H0 C p q a μorbit θ hcase hθclass
      (by simpa [μorbit] using hW1Inertia)
  have hfinalInertia :
      H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9 M MF H0 C p
        ι μorbit θ := by
    dsimp [H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9] at hconstFinal
    refine ⟨hθinj, ?_, ?_⟩
    · simpa [μorbit, θ, Dm, HCm, HCD] using hconstFinal
    · intro i
      rcases hθdata_full i with ⟨hθirr, hθnotMF, hθker, _hψirr_i, _hψdeg_i⟩
      exact ⟨hθirr, hθnotMF, hθker⟩
  have hcore :
      H0CLinearCandidateXmuSmuCoreDataWithRaw_sec9 M MF H0 C p SH0C
        ι μorbit θ :=
    H0CLinearCandidateXmuSmuCoreDataWithRaw_of_finalInertiaData_sec9
      M MF U W1 W2 H0 C p q a SH0C μorbit θ hcase hSH0C
      hfinalInertia hfinalInjective
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hC : quotientCentralizerIn MF H0 U C :=
    case_9_7_a_quotientCentralizerIn_sec9 hcase
  have hpprime : Nat.Prime p := case_9_7_a_p_prime_sec9 hcase
  have hpData :
      ∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
            quotientChiefFactorData_9_6 M MF H0 W1 hp := by
    rcases hcase with
      ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, hpData, _hrest⟩
    exact hpData
  have hH0CnormalM : ((H0 ⊔ C).subgroupOf M).Normal :=
    theorem_9_H0C_normal_M_source_core_sec9 M MF U W1 W2 H0 C p q
      h92 hH0MF hC hpprime hpData
  have hH0CD : H0 ⊔ C ≤ ambientDerivedSubgroup M :=
    theorem_9_H0C_le_ambientDerived_of_source_sec9 M MF U W1 W2 H0 C q
      h92 hH0MF hC
  have hredCard :
      (reducibleCharacterFilter_sec9 M SH0C).card = p - 1 :=
    theorem_9_nb_redM_count_of_normal_le_inter_source_core_sec9
      M MF U W1 W2 H0 (H0 ⊔ C) p q SH0C h92 hH0MF hpprime hpData
      hH0CnormalM hH0CD hH0CinfMF hSH0C
  dsimp [H0CLinearCandidateXmuSmuCoreDataWithRaw_sec9] at hcore
  rcases hcore with ⟨hfinalInj, htop, hred, _himage⟩
  refine ⟨ULift.{u} (H0CLinearCandidateXmuRawIndex_sec9 p), inferInstance,
    Classical.decEq _, ?_⟩
  refine ⟨fun i => θ (μorbit i.down), ?_, ?_, ?_, ?_⟩
  · simp
  · intro i j hij
    apply ULift.ext
    apply hfinalInj
    simpa [Dm] using hij
  · intro i
    rcases hθdata_full (μorbit i.down) with
      ⟨hθirr, hθnotMF, hθker, _hψirr_i, _hψdeg_i⟩
    exact ⟨hθirr, hθnotMF, hθker, by simpa [Dm] using htop i.down,
      by simpa [Dm] using hred i.down⟩
  · intro χ hχred
    let μfinal :
        ULift.{u} (H0CLinearCandidateXmuRawIndex_sec9 p) →
          Section1.ClassFunction M :=
      fun i => Section1.inducedCF Dm (θ (μorbit i.down))
    let Smu : Finset (Section1.ClassFunction M) := Finset.univ.image μfinal
    have hSmuSub : Smu ⊆ reducibleCharacterFilter_sec9 M SH0C := by
      intro χ hχ
      rcases Finset.mem_image.mp hχ with ⟨i, _hi, rfl⟩
      simpa [μfinal, Dm] using hred i.down
    have hfinalInjLift : Function.Injective μfinal := by
      intro i j hij
      apply ULift.ext
      apply hfinalInj
      simpa [μfinal, Dm] using hij
    have hSmuCard : Smu.card = p - 1 := by
      rw [Finset.card_image_of_injective _ hfinalInjLift]
      simp
    have hSmuEq : Smu = reducibleCharacterFilter_sec9 M SH0C :=
      Finset.eq_of_subset_of_card_le hSmuSub (by rw [hredCard, hSmuCard])
    have hχSmu : χ ∈ Smu := by
      rw [hSmuEq]
      exact hχred
    rcases Finset.mem_image.mp hχSmu with ⟨i, _hi, hiχ⟩
    exact ⟨i, hiχ.symm⟩

private theorem H0CLinearCandidateXmu_final_subfamily_of_orbit_data_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (_hfac : ∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) aρ)
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (hnormalC : (C.subgroupOf U).Normal)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          Function.Injective ψHC →
            (∀ f, Section1.IsIrreducibleCharacterOnGroup (ψHC f)) →
              (∀ f, Section1.degree (ψHC f) = (1 : ℂ)) →
                (∀ f, Section1.subgroupInKernel' (ψHC f)
                  ((H0 ⊔ C).subgroupOf (MF ⊔ C))) →
                  (∀ f, ¬ Section1.subgroupInKernel' (ψHC f)
                    (MF.subgroupOf (MF ⊔ C))) →
                      H0CLinearCandidateXthetaThetaCoordinateOrbitData_sec9
                        M MF U H0 C p q ubar ψHC →
                      H0CLinearCandidateXmuDmuData_sec9 M MF H0 C p q ubar SH0C := by
  classical
  intro hψformula hcase hBarU hSH0C _hψinj hψirr hψdeg hψker hψnonker _hcoord
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  have hnormalHCD : HCD.Normal := by
    dsimp [HCD, HCm, Dm]
    exact theorem_9_8_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C p q a ubar hcase hBarU
  letI : (C.subgroupOf U).Normal := hnormalC
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  letI : HCD.Normal := hnormalHCD
  have hstab : ∀ k : κ, MulAction.stabilizer (U ⧸ C.subgroupOf U) k = ⊥ :=
    rawCoordinateMulAction_stabilizer_eq_bot_sec9
      hcase H hHcard hHnorm hHsup ρ hρaction
  have hbarCard : Nat.card (U ⧸ C.subgroupOf U) = ubar := by
    rcases hBarU with ⟨_hC_le_U, _hnormalBarC, hbarCard⟩
    simpa using hbarCard
  have hrawCoord :
      (∀ k : κ,
        Section1.inertiaSubgroup HCD
            (Section1.subgroupOfClassFunction
              ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k)) =
          HCD) ∧
        ∀ k l : κ,
          (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) k =
            (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) l ↔
              MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l := by
    simpa [instAction, κ, Dm, HCm, HCD] using
      theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup ρ hρcyc hρcard
        hρaction hρker hconj hH0CinfMF hsup ψHC hcase hψformula hnormalHCD
  have hIeq : ∀ i : ι,
      Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ i)) = HCD := by
    intro i
    simpa [ψ, HCm] using hrawCoord.1 (Quotient.out i)
  have hθinj : Function.Injective θ := by
    intro i j hij
    have hout :
        MulAction.orbitRel (U ⧸ C.subgroupOf U) κ (Quotient.out i) (Quotient.out j) := by
      rw [← hrawCoord.2]
      simpa [θ, ψ, Dm, HCm, HCD] using hij
    have hi : Quotient.mk'' (Quotient.out i : κ) = i :=
      Quotient.out_eq' i
    have hj : Quotient.mk'' (Quotient.out j : κ) = j :=
      Quotient.out_eq' j
    exact (hi.symm.trans (Quotient.sound hout)).trans hj
  have hfiber : ∀ i : ι, Fintype.card {k : κ // orbit k = i} = ubar := by
    intro i
    rw [← hbarCard]
    rw [← Nat.card_eq_fintype_card]
    exact freeAction_orbitQuotient_fiber_natCard_sec9 (A := U ⧸ C.subgroupOf U)
      (κ := κ) hstab i
  have hκcard :
      Fintype.card κ = (p - 1) ^ q :=
    theorem_9_8_Ftheta_raw_choice_card_sec9 p q
  have hcardκ :
      Fintype.card κ = ubar * Fintype.card ι :=
    card_eq_mul_card_of_fiber_card_sec9 orbit ubar hfiber
  have hθcard : ubar * Fintype.card ι = (p - 1) ^ q := by
    rw [← hcardκ]
    exact hκcard
  have hθdata :
      ∀ i : ι,
        Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
          ¬ Section1.subgroupInKernel' (θ i)
            ((MF.subgroupOf M).subgroupOf Dm) ∧
          Section1.subgroupInKernel' (θ i)
            (((H0 ⊔ C).subgroupOf M).subgroupOf Dm) ∧
          Section1.IsIrreducibleCharacterOnGroup (ψ i) ∧
          Section1.degree (ψ i) = (1 : ℂ) :=
    H0CLinearCandidateXtheta_theta_orbit_entry_data_sec9
      M MF U W1 W2 H0 C p q a (ψHC := ψHC) (ι := ι) Quotient.out
      hcase hψirr hψdeg hψker hψnonker hnormalHCD hIeq
  have hXmu :
      H0CLinearCandidateXmuFinalImageData_sec9 M MF H0 C p SH0C ι θ := by
    exact
      H0CLinearCandidateXmu_transported_final_image_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ ubar SH0C ψHC H hHcard hHnorm hHindep hHsup
        ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup
        hψformula hcase hBarU hSH0C
  dsimp [H0CLinearCandidateXmuFinalImageData_sec9] at hXmu
  rcases hXmu with ⟨Xmu, hXmucard, hXmu_red, hred_sub_Xmu, hXmu_sep⟩
  refine ⟨ι, instFintypeι, instDecidableEqι, θ, ψ, ?_, hθcard, ?_,
    Xmu, hXmucard, hXmu_red, hred_sub_Xmu, hXmu_sep⟩
  · simpa [θ, ψ, Dm, HCm, HCD] using hθinj
  · intro i
    rcases hθdata i with ⟨hθirr, hθnotMF, hθkerH0C, hψirr_i, hψdeg_i⟩
    exact ⟨hθirr, hθnotMF, hθkerH0C, hψirr_i, hψdeg_i, rfl⟩

private theorem theorem_9_8_H0C_linear_candidate_Xmu_final_subfamily_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          H0COrderedComponentCharacterFamilyData_sec9 MF U W1 H0 C p q →
            H0CLinearCandidateXmuDmuData_sec9 M MF H0 C p q u SH0C := by
  intro hcase hBarU hSH0C hordered
  rcases H0COrderedXmuCoordinateData_of_ordered_sec9 MF U W1 H0 C p q hordered with
    ⟨aρ, hnormalH0, hnormalC, H, hHcard, hHnorm, hHindep, hHsup, hfac,
      hconj, ρ, hρcyc, hρcard, hρaction, hρker, horderedXmu⟩
  rcases theorem_9_8_H0C_linear_candidate_Xtheta_thetaHC_concrete_fields_source_core_sec9
      M MF U W1 W2 H0 C p q a H hHcard hHindep hHsup hcase with
    ⟨hcomm, hnormalH0C, hH0CinfMF, hsup, ψHC, hψformula, hψinj, hψirr,
      hψdeg, hψker, hψnonker⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : IsMulCommutative (MF ⧸ H0.subgroupOf MF) := hcomm
  letI : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal := hnormalH0C
  have hcore :
      H0CLinearCandidateXthetaThetaCoordinateActionCoreData_sec9
        M MF U H0 C p q ψHC :=
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_core_of_concrete_formula_source_core_sec9
      M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup hfac hconj
      hnormalC hH0CinfMF hsup ψHC hcase hψformula
  have haction :
      H0CLinearCandidateXthetaThetaCoordinateActionData_sec9
        M MF U H0 C p q u ψHC :=
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_of_core_data_sec9
      M MF U H0 C p q u ψHC hBarU hcore
  have horbitData :
      H0CLinearCandidateXthetaThetaCoordinateOrbitData_sec9
        M MF U H0 C p q u ψHC :=
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_orbit_of_action_data_sec9
      M MF U H0 C p q u ψHC haction
  exact H0CLinearCandidateXmu_final_subfamily_of_orbit_data_source_core_sec9
    M MF U W1 W2 H0 C p q a aρ u SH0C ψHC H hHcard hHnorm hHindep hHsup
    hfac hconj hnormalC ρ hρcyc hρcard hρaction hρker horderedXmu hH0CinfMF hsup hψformula
    hcase hBarU hSH0C hψinj hψirr hψdeg hψker hψnonker horbitData

private theorem theorem_9_8_H0C_linear_candidate_Xmu_residual_data_ordered_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          H0COrderedComponentCharacterFamilyData_sec9 MF U W1 H0 C p q →
            H0CLinearCandidateXmuResidualData_sec9 M MF H0 C p SH0C := by
  intro hcase hBarU hSH0C hordered
  rcases H0COrderedXmuCoordinateData_of_ordered_sec9 MF U W1 H0 C p q hordered with
    ⟨aρ, hnormalH0, hnormalC, H, hHcard, hHnorm, hHindep, hHsup, _hfac,
      hconj, ρ, hρcyc, hρcard, hρaction, hρker, horderedXmu⟩
  rcases theorem_9_8_H0C_linear_candidate_Xtheta_thetaHC_concrete_fields_source_core_sec9
      M MF U W1 W2 H0 C p q a H hHcard hHindep hHsup hcase with
    ⟨hcomm, hnormalH0C, hH0CinfMF, hsup, ψHC, hψformula, _hψinj, _hψirr,
      _hψdeg, _hψker, _hψnonker⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : IsMulCommutative (MF ⧸ H0.subgroupOf MF) := hcomm
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal := hnormalH0C
  exact H0CLinearCandidateXmu_transported_residual_data_source_core_sec9
    M MF U W1 W2 H0 C p q a aρ u SH0C ψHC H hHcard hHnorm hHindep hHsup
    ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup hψformula
    hcase hBarU hSH0C

public theorem theorem_9_8_H0C_linear_candidate_Xmu_Dmu_data_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          H0CLinearCandidateXmuDmuData_sec9 M MF H0 C p q u SH0C := by
  classical
  intro hcase hBarU hSH0C
  have hordered :
      H0COrderedComponentCharacterFamilyData_sec9 MF U W1 H0 C p q :=
    theorem_9_7_orderedCaseAComponentTransitionData_of_case_a_sec9
      M MF U W1 W2 H0 C p q a u hcase hBarU
  exact theorem_9_8_H0C_linear_candidate_Xmu_final_subfamily_source_core_sec9
    M MF U W1 W2 H0 C p q a u SH0C hcase hBarU hSH0C hordered

public theorem theorem_9_8_H0C_linear_candidate_Xmu_residual_data_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          H0CLinearCandidateXmuResidualData_sec9 M MF H0 C p SH0C := by
  classical
  intro hcase hBarU hSH0C
  have hordered :
      H0COrderedComponentCharacterFamilyData_sec9 MF U W1 H0 C p q :=
    theorem_9_7_orderedCaseAComponentTransitionData_of_case_a_sec9
      M MF U W1 W2 H0 C p q a u hcase hBarU
  exact theorem_9_8_H0C_linear_candidate_Xmu_residual_data_ordered_source_core_sec9
    M MF U W1 W2 H0 C p q a u SH0C hcase hBarU hSH0C hordered

private theorem theorem_9_8_H0C_linear_candidate_Xmu_Dmu_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          reducibleCharacterFilter_sec9 M SH0C ⊆
              linearHCCharacterFilter_sec9 M MF C SH0C ∧
            ∃ χ : Section1.ClassFunction M,
              χ ∈ SH0C ∧
                Section1.IsIrreducibleCharacterOnGroup χ ∧
                Section1.degree χ = (q * u : ℂ) ∧
                inducedFromLinearCharacterOfHC M MF C χ := by
  classical
  intro hcase hBarU hSH0C
  rcases theorem_9_8_H0C_linear_candidate_Xmu_Dmu_data_source_core_sec9
      M MF U W1 W2 H0 C p q a u SH0C hcase hBarU hSH0C with
    ⟨ι, instFintype, instDecidableEq, θ, ψ, hθinj, hθcard, hθdata, Xmu,
      hXmucard, _hXmu_red, hred_sub_Xmu, hXmu_sep⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let H0CD : Subgroup Dm := ((H0 ⊔ C).subgroupOf M).subgroupOf Dm
  let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
  have hHCm_le_Dm : HCm ≤ Dm := by
    have hHC_le_D : MF ⊔ C ≤ ambientDerivedSubgroup M :=
      theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
        M MF U W1 W2 H0 C p q a hcase
    intro x hx
    change ((x : M) : G) ∈ ambientDerivedSubgroup M
    exact hHC_le_D (by simpa [HCm, Subgroup.mem_subgroupOf] using hx)
  have hlinear_induced :
      ∀ i : ι, inducedFromLinearCharacterOfHC M MF C (Section1.inducedCF Dm (θ i)) := by
    intro i
    dsimp [inducedFromLinearCharacterOfHC, inducedFromLinearCharacter]
    refine ⟨ψ i, (hθdata i).2.2.2.1, (hθdata i).2.2.2.2.1, ?_⟩
    calc
      Section1.inducedCF Dm (θ i) =
          Section1.inducedCF Dm
            (Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))) := by
            rw [(hθdata i).2.2.2.2.2]
      _ = Section1.inducedCF HCm (ψ i) := by
            simpa [Dm, HCm, HCD] using
              Section1.inducedCF_trans HCm Dm hHCm_le_Dm (ψ i)
  have hred_linear :
      reducibleCharacterFilter_sec9 M SH0C ⊆
        linearHCCharacterFilter_sec9 M MF C SH0C := by
    intro χ hχred
    rcases hred_sub_Xmu χ hχred with ⟨i, _hiXmu, hχeq⟩
    have hχSH0C : χ ∈ SH0C := by
      have hχpair : χ ∈ SH0C ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
        simpa [reducibleCharacterFilter_sec9] using hχred
      exact hχpair.1
    have hlin : inducedFromLinearCharacterOfHC M MF C χ := by
      rw [hχeq]
      exact hlinear_induced i
    exact Finset.mem_filter.mpr ⟨hχSH0C, hlin⟩
  have hnot_all_Xmu : ¬ Finset.univ ⊆ Xmu := by
    intro hall
    have hXmu_eq_univ : Xmu = Finset.univ :=
      Finset.eq_univ_of_forall fun i => hall (by simp)
    have hcard_univ : Fintype.card ι = p - 1 := by
      calc
        Fintype.card ι = (Finset.univ : Finset ι).card := by simp
        _ = Xmu.card := by rw [hXmu_eq_univ]
        _ = p - 1 := hXmucard
    have hcount_eq : ((p - 1) ^ q) / u = p - 1 := by
      have hdiv_eq : Fintype.card ι = ((p - 1) ^ q) / u :=
        card_eq_div_of_left_mul_card_eq_sec9
        (quotientBarUCardinality_pos_sec9 U C u hBarU) hθcard
      exact hdiv_eq.symm.trans hcard_univ
    exact theorem_9_8_H0C_linear_candidate_count_ne_core_sec9
      M MF U W1 W2 H0 C p q a u hcase hBarU hcount_eq
  have hex_not_Xmu : ∃ j : ι, j ∉ Xmu := by
    by_contra hno
    apply hnot_all_Xmu
    intro j _hj
    by_contra hj_not
    exact hno ⟨j, hj_not⟩
  rcases hex_not_Xmu with ⟨j, hj_not_Xmu⟩
  have hχred_not :
      Section1.inducedCF Dm (θ j) ∉ reducibleCharacterFilter_sec9 M SH0C := by
    intro hχred
    rcases hred_sub_Xmu (Section1.inducedCF Dm (θ j)) hχred with ⟨i, hiXmu, hij⟩
    exact hXmu_sep i hiXmu j hj_not_Xmu hij.symm
  have hχSH0C : Section1.inducedCF Dm (θ j) ∈ SH0C := by
    rcases hSH0C with ⟨_hYle, _hMFle, hmem⟩
    rw [hmem]
    exact ⟨θ j, (hθdata j).1, (hθdata j).2.1, (hθdata j).2.2.1, rfl⟩
  have hχirr : Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF Dm (θ j)) := by
    by_contra hnot
    exact hχred_not (by
      simp [reducibleCharacterFilter_sec9, hχSH0C, hnot])
  have hχlin : inducedFromLinearCharacterOfHC M MF C (Section1.inducedCF Dm (θ j)) :=
    hlinear_induced j
  have hχdeg : Section1.degree (Section1.inducedCF Dm (θ j)) = (q * u : ℂ) := by
    have hidx : Subgroup.index ((MF ⊔ C).subgroupOf M) = q * u :=
      HC_index_eq_q_mul_u_of_hypothesis_9_2_sec9 M MF U W1 W2 C q u
        (case_9_7_a_hypothesis_9_2_sec9 hcase) hBarU
    exact degree_eq_q_mul_u_of_linear_HC_sec9
      M MF C q u (Section1.inducedCF Dm (θ j)) hidx hχlin
  exact ⟨hred_linear, ⟨Section1.inducedCF Dm (θ j), hχSH0C, hχirr, hχdeg, hχlin⟩⟩

private theorem theorem_9_8_H0C_linear_candidate_Xmu_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          ∃ L : Finset (Section1.ClassFunction M),
            L.card = p - 1 ∧
              L ⊆ SH0C ∧
              (∀ χ : Section1.ClassFunction M, χ ∈ L →
                inducedFromLinearCharacterOfHC M MF C χ) ∧
              reducibleCharacterFilter_sec9 M SH0C ⊆ L ∧
              ∃ χ : Section1.ClassFunction M,
                χ ∈ SH0C ∧
                  Section1.IsIrreducibleCharacterOnGroup χ ∧
                  Section1.degree χ = (q * u : ℂ) ∧
                  inducedFromLinearCharacterOfHC M MF C χ := by
  classical
  intro hcase hBarU hSH0C
  let R : Finset (Section1.ClassFunction M) := reducibleCharacterFilter_sec9 M SH0C
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hC : quotientCentralizerIn MF H0 U C :=
    case_9_7_a_quotientCentralizerIn_sec9 hcase
  have hpprime : Nat.Prime p := case_9_7_a_p_prime_sec9 hcase
  have hpData :
      ∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
            quotientChiefFactorData_9_6 M MF H0 W1 hp := by
    rcases hcase with
      ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, hpData, _hrest⟩
    exact hpData
  have hH0CnormalM : ((H0 ⊔ C).subgroupOf M).Normal :=
    theorem_9_H0C_normal_M_source_core_sec9 M MF U W1 W2 H0 C p q
      h92 hH0MF hC hpprime hpData
  have hH0CD : H0 ⊔ C ≤ ambientDerivedSubgroup M :=
    theorem_9_H0C_le_ambientDerived_of_source_sec9 M MF U W1 W2 H0 C q
      h92 hH0MF hC
  have hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0 :=
    theorem_9_H0C_inf_MF_eq_H0_source_core_sec9 M MF U W1 W2 H0 C p q
      h92 hH0MF hC hpprime hpData
  have hRcard : R.card = p - 1 := by
    simpa [R] using
      theorem_9_nb_redM_count_of_normal_le_inter_source_core_sec9
        M MF U W1 W2 H0 (H0 ⊔ C) p q SH0C h92 hH0MF hpprime hpData
        hH0CnormalM hH0CD hH0CinfMF hSH0C
  rcases theorem_9_8_H0C_linear_candidate_Xmu_Dmu_source_core_sec9
      M MF U W1 W2 H0 C p q a u SH0C hcase hBarU hSH0C with
    ⟨hred_linear, hwitness⟩
  have hRsubSH0C : R ⊆ SH0C := by
    intro χ hχR
    have hχ : χ ∈ SH0C ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
      simpa [R, reducibleCharacterFilter_sec9] using hχR
    exact hχ.1
  have hRlin :
      ∀ χ : Section1.ClassFunction M, χ ∈ R →
        inducedFromLinearCharacterOfHC M MF C χ := by
    intro χ hχR
    have hχlinFilter : χ ∈ linearHCCharacterFilter_sec9 M MF C SH0C :=
      hred_linear (by simpa [R] using hχR)
    have hχlin :
        χ ∈ SH0C ∧ inducedFromLinearCharacterOfHC M MF C χ := by
      simpa [linearHCCharacterFilter_sec9] using hχlinFilter
    exact hχlin.2
  exact ⟨R, hRcard, hRsubSH0C, hRlin, by intro χ hχ; simpa [R] using hχ,
    hwitness⟩

private theorem theorem_9_8_H0C_linear_candidate_reducible_subset_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          reducibleCharacterFilter_sec9 M SH0C ⊆
            linearHCCharacterFilter_sec9 M MF C SH0C := by
  classical
  intro hcase hBarU hSH0C
  rcases theorem_9_8_H0C_linear_candidate_Xmu_source_core_sec9
      M MF U W1 W2 H0 C p q a u SH0C hcase hBarU hSH0C with
    ⟨L, _hLcard, _hLsubSH0C, hLlin, hred_mem_L, _hwitness⟩
  intro χ hχred
  have hχred_pair :
      χ ∈ SH0C ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
    simpa [reducibleCharacterFilter_sec9] using hχred
  rcases hχred_pair with
    ⟨hχSH0C, hχred'⟩
  have hχL : χ ∈ L := hred_mem_L hχred
  exact Finset.mem_filter.mpr ⟨hχSH0C, hLlin χ hχL⟩


private theorem theorem_9_8_reducible_filter_count_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                ∃ R0 RC : Finset (Section1.ClassFunction M),
                  R0.card = p - 1 ∧
                    RC.card = p - 1 ∧
                    (∀ χ : Section1.ClassFunction M,
                      χ ∈ R0 ↔
                        χ ∈ SH0 ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ) ∧
                    ∀ χ : Section1.ClassFunction M,
                      χ ∈ RC ↔
                        χ ∈ SH0C ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
  intro hcase _hBarU _hUprime hSH0 hSH0C _hSH0U
  rcases hcase with ⟨h92, hH0MF, hC, hpprime, _hqprime, hpData, _hrest⟩
  exact theorem_9_reducible_filter_count_source_bridge_sec9
      M MF U W1 W2 H0 C p q SH0 SH0C h92 hH0MF hC hpprime hpData
      hSH0 hSH0C

private theorem theorem_9_8_reducible_filter_count_linear_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                ∃ R0 RC : Finset (Section1.ClassFunction M),
                  R0.card = p - 1 ∧
                    RC.card = p - 1 ∧
                    (∀ χ : Section1.ClassFunction M,
                      χ ∈ R0 ↔
                        χ ∈ SH0 ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ) ∧
                    (∀ χ : Section1.ClassFunction M,
                      χ ∈ RC ↔
                        χ ∈ SH0C ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ) ∧
                    ∀ χ : Section1.ClassFunction M, χ ∈ RC →
                      inducedFromLinearCharacterOfHC M MF C χ := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  rcases theorem_9_8_reducible_filter_count_source_bridge_sec9
      M MF U W1 W2 H0 C Uprime p q a u SH0 SH0C SH0U hcase hBarU
      hUprime hSH0 hSH0C hSH0U with
    ⟨R0, RC, hR0card, hRCcard, hR0mem, hRCmem⟩
  have hred_sub_linear :
      reducibleCharacterFilter_sec9 M SH0C ⊆
        linearHCCharacterFilter_sec9 M MF C SH0C :=
    theorem_9_8_H0C_linear_candidate_reducible_subset_source_bridge_sec9
      M MF U W1 W2 H0 C p q a u SH0C hcase hBarU hSH0C
  have hRClin :
      ∀ χ : Section1.ClassFunction M, χ ∈ RC →
        inducedFromLinearCharacterOfHC M MF C χ := by
    intro χ hχRC
    rcases (hRCmem χ).1 hχRC with ⟨hχSH0C, hχred⟩
    have hχredMem : χ ∈ reducibleCharacterFilter_sec9 M SH0C := by
      simp [reducibleCharacterFilter_sec9, hχSH0C, hχred]
    have hχlinMem : χ ∈ linearHCCharacterFilter_sec9 M MF C SH0C :=
      hred_sub_linear hχredMem
    have hmem :
        χ ∈ SH0C ∧ inducedFromLinearCharacterOfHC M MF C χ := by
      simpa [linearHCCharacterFilter_sec9] using hχlinMem
    exact hmem.2
  exact ⟨R0, RC, hR0card, hRCcard, hR0mem, hRCmem, hRClin⟩

private theorem theorem_9_8_reducible_subfamily_linear_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                ∃ R : Finset (Section1.ClassFunction M),
                  R.card = p - 1 ∧
                    R ⊆ SH0 ∧
                    (∀ χ : Section1.ClassFunction M, χ ∈ R →
                      ¬ Section1.IsIrreducibleCharacterOnGroup χ) ∧
                    (∀ χ : Section1.ClassFunction M, χ ∈ SH0 →
                      ¬ Section1.IsIrreducibleCharacterOnGroup χ → χ ∈ R) ∧
                    R ⊆ SH0C ∧
                    ∀ χ : Section1.ClassFunction M, χ ∈ R →
                      inducedFromLinearCharacterOfHC M MF C χ := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  rcases theorem_9_8_reducible_filter_count_linear_source_bridge_sec9
      M MF U W1 W2 H0 C Uprime p q a u SH0 SH0C SH0U hcase hBarU
      hUprime hSH0 hSH0C hSH0U with
    ⟨R0, RC, hR0card, hRCcard, hR0mem, hRCmem, hRClin⟩
  have hSH0CsubSH0 : SH0C ⊆ SH0 :=
    kernelInducedFamily_subset_of_le_sec9 M (ambientDerivedSubgroup M) MF
      H0 (H0 ⊔ C) SH0 SH0C le_sup_left hSH0 hSH0C
  have hRCsubR0 : RC ⊆ R0 := by
    intro χ hχRC
    rcases (hRCmem χ).1 hχRC with ⟨hχSH0C, hχred⟩
    exact (hR0mem χ).2 ⟨hSH0CsubSH0 hχSH0C, hχred⟩
  have hRCeqR0 : RC = R0 :=
    Finset.eq_of_subset_of_card_le hRCsubR0 (by rw [hR0card, hRCcard])
  have hR0subSH0 : R0 ⊆ SH0 := by
    intro χ hχR0
    exact ((hR0mem χ).1 hχR0).1
  have hR0nonirr :
      ∀ χ : Section1.ClassFunction M, χ ∈ R0 →
        ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
    intro χ hχR0
    exact ((hR0mem χ).1 hχR0).2
  have hR0all :
      ∀ χ : Section1.ClassFunction M, χ ∈ SH0 →
        ¬ Section1.IsIrreducibleCharacterOnGroup χ → χ ∈ R0 := by
    intro χ hχSH0 hχred
    exact (hR0mem χ).2 ⟨hχSH0, hχred⟩
  have hR0subSH0C : R0 ⊆ SH0C := by
    intro χ hχR0
    have hχRC : χ ∈ RC := by
      rw [hRCeqR0]
      exact hχR0
    exact ((hRCmem χ).1 hχRC).1
  have hR0lin :
      ∀ χ : Section1.ClassFunction M, χ ∈ R0 →
        inducedFromLinearCharacterOfHC M MF C χ := by
    intro χ hχR0
    have hχRC : χ ∈ RC := by
      rw [hRCeqR0]
      exact hχR0
    exact hRClin χ hχRC
  exact ⟨R0, hR0card, hR0subSH0, hR0nonirr, hR0all, hR0subSH0C, hR0lin⟩

private theorem theorem_9_8_reducible_subfamily_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                ∃ R : Finset (Section1.ClassFunction M),
                  R.card = p - 1 ∧
                    reducibleCharacterSubfamilyData M SH0 R (q * u) ∧
                    R ⊆ SH0C ∧
                    ∀ χ : Section1.ClassFunction M, χ ∈ R →
                      inducedFromLinearCharacterOfHC M MF C χ := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  rcases theorem_9_8_reducible_subfamily_linear_source_bridge_sec9
      M MF U W1 W2 H0 C Uprime p q a u SH0 SH0C SH0U hcase hBarU
      hUprime hSH0 hSH0C hSH0U with
    ⟨R, hRcard, hRsubSH0, hRnonirr, hRall, hRsubSH0C, hRlin⟩
  have hidx : Subgroup.index ((MF ⊔ C).subgroupOf M) = q * u :=
    HC_index_eq_q_mul_u_of_hypothesis_9_2_sec9 M MF U W1 W2 C q u hcase.1
      hBarU
  have hRdata : reducibleCharacterSubfamilyData M SH0 R (q * u) := by
    refine ⟨hRsubSH0, ?_, hRall⟩
    intro χ hχR
    have hdeg :
        Section1.degree χ = (q * u : ℂ) :=
      degree_eq_q_mul_u_of_linear_HC_sec9 M MF C q u χ hidx (hRlin χ hχR)
    exact ⟨hRnonirr χ hχR, by simpa [Nat.cast_mul] using hdeg⟩
  exact ⟨R, hRcard, hRdata, hRsubSH0C, hRlin⟩

private theorem theorem_9_8_irreducible_H0C_linear_witness_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                ∃ χ : Section1.ClassFunction M,
                  χ ∈ SH0C ∧
                    Section1.IsIrreducibleCharacterOnGroup χ ∧
                    inducedFromLinearCharacterOfHC M MF C χ := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  rcases theorem_9_8_H0C_linear_candidate_Xmu_source_core_sec9
      M MF U W1 W2 H0 C p q a u SH0C hcase hBarU hSH0C with
    ⟨_L, _hLcard, _hLsub, _hLlin, _hred_sub, χ, hχSH0C, hχirr, _hχdeg, hχlin⟩
  exact ⟨χ, hχSH0C, hχirr, hχlin⟩

private theorem theorem_9_8_irreducible_H0C_linear_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                ∃ χ : Section1.ClassFunction M,
                  χ ∈ SH0C ∧
                    Section1.IsIrreducibleCharacterOnGroup χ ∧
                    Section1.degree χ = (q * u : ℂ) ∧
                    inducedFromLinearCharacterOfHC M MF C χ := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  rcases theorem_9_8_irreducible_H0C_linear_witness_source_bridge_sec9
      M MF U W1 W2 H0 C Uprime p q a u SH0 SH0C SH0U hcase hBarU
      hUprime hSH0 hSH0C hSH0U with
    ⟨χ, hχSH0C, hχirr, hχlin⟩
  have hidx : Subgroup.index ((MF ⊔ C).subgroupOf M) = q * u :=
    HC_index_eq_q_mul_u_of_hypothesis_9_2_sec9 M MF U W1 W2 C q u hcase.1
      hBarU
  exact ⟨χ, hχSH0C, hχirr,
    degree_eq_q_mul_u_of_linear_HC_sec9 M MF C q u χ hidx hχlin, hχlin⟩

private noncomputable def theorem_9_8_initial_degree_subfamily_sec9
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (q a : ℕ)
    (SH0U : Finset (Section1.ClassFunction M)) :
    Finset (Section1.ClassFunction M) := by
  classical
  exact SH0U.filter fun χ =>
    Section1.IsIrreducibleCharacterOnGroup χ ∧
      Section1.degree χ = (q * a : ℂ)

private def theorem_9_8_initial_constituent_family_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) : Prop :=
  ∃ ι : Type u, ∃ instFintype : Fintype ι, ∃ instDecidableEq : DecidableEq ι,
    letI : Fintype ι := instFintype
    letI : DecidableEq ι := instDecidableEq
    ∃ θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
      Function.Injective
          (fun i : ι =>
            Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i)) ∧
        ((p - 1) / a) * (Nat.card U / (a * Nat.card Uprime)) ≤ Fintype.card ι ∧
        ∀ i : ι,
          Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
            ¬ Section1.subgroupInKernel' (θ i)
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) ∧
            Section1.subgroupInKernel' (θ i)
              (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) ∧
            Section1.degree (θ i) = (a : ℂ) ∧
            Section1.IsIrreducibleCharacterOnGroup
              (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i))

private theorem theorem_9_8_initial_degree_count_of_constituent_family_data_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 Uprime : Subgroup G)
    (p q a : ℕ)
    (SH0U : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
        theorem_9_8_initial_constituent_family_data_sec9 M MF U H0 Uprime p a →
          (theorem_9_8_initial_degree_subfamily_sec9 M q a SH0U).card ≥
            ((p - 1) / a) * (Nat.card U / (a * Nat.card Uprime)) := by
  intro h92 hSH0U hfamily
  classical
  rcases hfamily with ⟨ι, instFintype, instDecidableEq, θ, hθinj, hcard, hθdata⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let μ : ι → Section1.ClassFunction M := fun i => Section1.inducedCF Dm (θ i)
  let image : Finset (Section1.ClassFunction M) := Finset.univ.image μ
  have hDindex : Subgroup.index Dm = q :=
    ambientDerived_subgroupOf_index_eq_q_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92
  have himage_card : image.card = Fintype.card ι := by
    simpa [image, μ, Dm] using
      Finset.card_image_of_injective (s := (Finset.univ : Finset ι)) hθinj
  have himage_sub :
      image ⊆ theorem_9_8_initial_degree_subfamily_sec9 M q a SH0U := by
    intro χ hχ
    rcases Finset.mem_image.mp hχ with ⟨i, _hi, rfl⟩
    rcases hθdata i with ⟨hθirr, hθnot, hθker, hθdegree, hμirr⟩
    have hμSH0U : μ i ∈ SH0U := by
      rcases hSH0U with ⟨_hYle, _hMFle, hmem⟩
      rw [hmem (μ i)]
      exact ⟨θ i, hθirr, by simpa [Dm] using hθnot, by simpa [Dm] using hθker, rfl⟩
    have hμdegree : Section1.degree (μ i) = (q * a : ℂ) := by
      change Section1.degree (Section1.inducedCF Dm (θ i)) = (q * a : ℂ)
      rw [Section1.degree_inducedClassFunction, hθdegree, hDindex]
    simpa [theorem_9_8_initial_degree_subfamily_sec9, μ] using
      (show μ i ∈ SH0U ∧
          Section1.IsIrreducibleCharacterOnGroup (μ i) ∧
          Section1.degree (μ i) = (q * a : ℂ) from
        ⟨hμSH0U, hμirr, hμdegree⟩)
  have himage_le :
      image.card ≤ (theorem_9_8_initial_degree_subfamily_sec9 M q a SH0U).card :=
    Finset.card_le_card himage_sub
  exact hcard.trans (by simpa [himage_card] using himage_le)

private def theorem_9_8_initial_constituent_orbit_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) : Prop :=
  ∃ κ : Type u, ∃ instFintypeκ : Fintype κ, ∃ instDecidableEqκ : DecidableEq κ,
    ∃ ι : Type u, ∃ instFintypeι : Fintype ι, ∃ instDecidableEqι : DecidableEq ι,
      letI : Fintype κ := instFintypeκ
      letI : DecidableEq κ := instDecidableEqκ
      letI : Fintype ι := instFintypeι
      letI : DecidableEq ι := instDecidableEqι
      ∃ orbit : κ → ι,
        (((p - 1) / a) * (Nat.card U / (a * Nat.card Uprime))) * a ≤
          Fintype.card κ ∧
        (∀ i : ι, Fintype.card {k : κ // orbit k = i} = a) ∧
        ∃ θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
          Function.Injective
              (fun i : ι =>
                Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i)) ∧
            ∀ i : ι,
              Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                ¬ Section1.subgroupInKernel' (θ i)
                  ((MF.subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                Section1.subgroupInKernel' (θ i)
                  (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                Section1.degree (θ i) = (a : ℂ) ∧
                Section1.IsIrreducibleCharacterOnGroup
                  (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i))

private def theorem_9_8_initial_constituent_Mtheta_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) : Prop :=
  ∃ κ : Type u, ∃ instFintypeκ : Fintype κ, ∃ instDecidableEqκ : DecidableEq κ,
    ∃ ι : Type u, ∃ instFintypeι : Fintype ι, ∃ instDecidableEqι : DecidableEq ι,
      letI : Fintype κ := instFintypeκ
      letI : DecidableEq κ := instDecidableEqκ
      letI : Fintype ι := instFintypeι
      letI : DecidableEq ι := instDecidableEqι
      ∃ orbit : κ → ι,
        Fintype.card κ = (p - 1) * (Nat.card U / (a * Nat.card Uprime)) ∧
        (∀ i : ι, Fintype.card {k : κ // orbit k = i} = a) ∧
        ∃ θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
          Function.Injective
              (fun i : ι =>
                Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i)) ∧
            ∀ i : ι,
              Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                ¬ Section1.subgroupInKernel' (θ i)
                  ((MF.subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                Section1.subgroupInKernel' (θ i)
                  (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                Section1.degree (θ i) = (a : ℂ) ∧
                Section1.IsIrreducibleCharacterOnGroup
                  (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i))

private def theorem_9_8_initial_constituent_Mtheta_raw_product_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) : Prop :=
  ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
    ∃ instDecidableEqLam : DecidableEq Lam,
    letI : Fintype Lam := instFintypeLam
    letI : DecidableEq Lam := instDecidableEqLam
    Fintype.card Lam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ ι : Type u, ∃ instFintypeι : Fintype ι, ∃ instDecidableEqι : DecidableEq ι,
        letI : Fintype ι := instFintypeι
        letI : DecidableEq ι := instDecidableEqι
        ∃ orbit : (Fin (p - 1) × Lam) → ι,
          (∀ i : ι, Fintype.card {k : Fin (p - 1) × Lam // orbit k = i} = a) ∧
          ∃ θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
            Function.Injective
                (fun i : ι =>
                  Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i)) ∧
              ∀ i : ι,
                Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                  ¬ Section1.subgroupInKernel' (θ i)
                    ((MF.subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.subgroupInKernel' (θ i)
                    (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.degree (θ i) = (a : ℂ) ∧
                  Section1.IsIrreducibleCharacterOnGroup
                    (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i))

private def theorem_9_8_initial_constituent_Mtheta_free_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) : Prop :=
  ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
    ∃ instDecidableEqLam : DecidableEq Lam,
    letI : Fintype Lam := instFintypeLam
    letI : DecidableEq Lam := instDecidableEqLam
    Fintype.card Lam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ A : Type u, ∃ instGroupA : Group A, ∃ instFintypeA : Fintype A,
        letI : Group A := instGroupA
        letI : Fintype A := instFintypeA
        Nat.card A = a ∧
          ∃ instAction : MulAction A (Fin (p - 1) × Lam),
            letI : MulAction A (Fin (p - 1) × Lam) := instAction
            (∀ k : Fin (p - 1) × Lam, MulAction.stabilizer A k = ⊥) ∧
              ∃ θ :
                Quotient (MulAction.orbitRel A (Fin (p - 1) × Lam)) →
                  Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
                Function.Injective
                    (fun i : Quotient (MulAction.orbitRel A (Fin (p - 1) × Lam)) =>
                      Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                        (θ i)) ∧
                  ∀ i : Quotient (MulAction.orbitRel A (Fin (p - 1) × Lam)),
                    Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                      ¬ Section1.subgroupInKernel' (θ i)
                        ((MF.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                      Section1.subgroupInKernel' (θ i)
                        (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                      Section1.degree (θ i) = (a : ℂ) ∧
                      Section1.IsIrreducibleCharacterOnGroup
                        (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                          (θ i))

private def theorem_9_8_initial_constituent_Mtheta_cyclic_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) [NeZero a] : Prop :=
  ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
    ∃ instDecidableEqLam : DecidableEq Lam,
    letI : Fintype Lam := instFintypeLam
    letI : DecidableEq Lam := instDecidableEqLam
    Fintype.card Lam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ instAction :
        MulAction (ULift.{u,0} (Multiplicative (ZMod a))) (Fin (p - 1) × Lam),
        letI : MulAction (ULift.{u,0} (Multiplicative (ZMod a)))
            (Fin (p - 1) × Lam) := instAction
        (∀ k : Fin (p - 1) × Lam,
          MulAction.stabilizer (ULift.{u,0} (Multiplicative (ZMod a))) k = ⊥) ∧
          ∃ θ :
            Quotient
                (MulAction.orbitRel
                  (ULift.{u,0} (Multiplicative (ZMod a))) (Fin (p - 1) × Lam)) →
              Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
            Function.Injective
                (fun i : Quotient
                    (MulAction.orbitRel
                      (ULift.{u,0} (Multiplicative (ZMod a))) (Fin (p - 1) × Lam)) =>
                  Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                    (θ i)) ∧
              ∀ i : Quotient
                  (MulAction.orbitRel
                    (ULift.{u,0} (Multiplicative (ZMod a))) (Fin (p - 1) × Lam)),
                Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                  ¬ Section1.subgroupInKernel' (θ i)
                    ((MF.subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.subgroupInKernel' (θ i)
                    (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.degree (θ i) = (a : ℂ) ∧
                  Section1.IsIrreducibleCharacterOnGroup
                    (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θ i))

private theorem orbitRel_compHom_mulEquiv_iff_sec9
    {A : Type u} {B : Type v} {κ : Type w}
    [Group A] [Group B] [MulAction B κ]
    (e : A ≃* B) :
    let instAction : MulAction A κ := MulAction.compHom κ e.toMonoidHom
    letI : MulAction A κ := instAction
    ∀ x y : κ,
      (MulAction.orbitRel A κ) x y ↔ (MulAction.orbitRel B κ) x y := by
  intro instAction
  letI : MulAction A κ := instAction
  intro x y
  constructor
  · intro h
    rw [MulAction.orbitRel_apply] at h ⊢
    rcases MulAction.mem_orbit_iff.mp h with ⟨g, hg⟩
    exact MulAction.mem_orbit_iff.mpr
      ⟨e g, by simpa [instAction, MulAction.compHom_smul_def] using hg⟩
  · intro h
    rw [MulAction.orbitRel_apply] at h ⊢
    rcases MulAction.mem_orbit_iff.mp h with ⟨b, hb⟩
    exact MulAction.mem_orbit_iff.mpr
      ⟨e.symm b, by simpa [instAction, MulAction.compHom_smul_def] using hb⟩

private theorem stabilizer_compHom_mulEquiv_eq_bot_sec9
    {A : Type u} {B : Type v} {κ : Type w}
    [Group A] [Group B] [MulAction B κ]
    (e : A ≃* B)
    (hfree : ∀ k : κ, MulAction.stabilizer B k = ⊥) :
    let instAction : MulAction A κ := MulAction.compHom κ e.toMonoidHom
    letI : MulAction A κ := instAction
    ∀ k : κ, MulAction.stabilizer A k = ⊥ := by
  intro instAction
  letI : MulAction A κ := instAction
  intro k
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_bot]
    have hbg : e g ∈ MulAction.stabilizer B k := by
      rw [MulAction.mem_stabilizer_iff]
      rw [MulAction.mem_stabilizer_iff] at hg
      simpa [instAction, MulAction.compHom_smul_def] using hg
    have hbg1 : e g = 1 := by
      simpa [hfree k] using hbg
    exact e.injective (by simpa using hbg1)
  · intro hg
    rw [Subgroup.mem_bot] at hg
    rw [hg]
    simp

private def theorem_9_8_initial_constituent_Mtheta_abstract_cyclic_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) : Prop :=
  ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
    ∃ instDecidableEqLam : DecidableEq Lam,
    letI : Fintype Lam := instFintypeLam
    letI : DecidableEq Lam := instDecidableEqLam
    Fintype.card Lam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ A : Type u, ∃ instGroupA : Group A, ∃ instFintypeA : Fintype A,
        letI : Group A := instGroupA
        letI : Fintype A := instFintypeA
        IsCyclic A ∧ Nat.card A = a ∧
          ∃ instAction : MulAction A (Fin (p - 1) × Lam),
            letI : MulAction A (Fin (p - 1) × Lam) := instAction
            (∀ k : Fin (p - 1) × Lam, MulAction.stabilizer A k = ⊥) ∧
              ∃ θ :
                Quotient (MulAction.orbitRel A (Fin (p - 1) × Lam)) →
                  Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
                Function.Injective
                    (fun i : Quotient (MulAction.orbitRel A (Fin (p - 1) × Lam)) =>
                      Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                        (θ i)) ∧
                  ∀ i : Quotient (MulAction.orbitRel A (Fin (p - 1) × Lam)),
                    Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                      ¬ Section1.subgroupInKernel' (θ i)
                        ((MF.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                      Section1.subgroupInKernel' (θ i)
                        (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                      Section1.degree (θ i) = (a : ℂ) ∧
                      Section1.IsIrreducibleCharacterOnGroup
                        (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                          (θ i))

private theorem theorem_9_8_initial_constituent_Mtheta_cyclic_action_data_of_abstract_cyclic_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) [NeZero a] :
    theorem_9_8_initial_constituent_Mtheta_abstract_cyclic_action_data_sec9
      M MF U H0 Uprime p a →
        theorem_9_8_initial_constituent_Mtheta_cyclic_action_data_sec9
          M MF U H0 Uprime p a := by
  intro habstract
  classical
  rcases habstract with
    ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard,
      A, instGroupA, instFintypeA, hcyclicA, hAcard, instActionA, hfreeA,
      θA, hθinjA, hθdataA⟩
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  letI : Group A := instGroupA
  letI : Fintype A := instFintypeA
  let κ : Type u := Fin (p - 1) × Lam
  let eZ : Multiplicative (ZMod a) ≃* A :=
    (AddEquiv.toMultiplicative
        (ZMod.ringEquivCongr hAcard.symm).toAddEquiv).trans
      (zmodCyclicMulEquiv hcyclicA)
  let eCanon : ULift.{u,0} (Multiplicative (ZMod a)) ≃* A :=
    MulEquiv.ulift.trans eZ
  let instActionCanon :
      MulAction (ULift.{u,0} (Multiplicative (ZMod a))) κ :=
    MulAction.compHom κ eCanon.toMonoidHom
  letI : MulAction (ULift.{u,0} (Multiplicative (ZMod a))) κ := instActionCanon
  have hrel : ∀ x y : κ,
      (MulAction.orbitRel (ULift.{u,0} (Multiplicative (ZMod a))) κ) x y ↔
        (MulAction.orbitRel A κ) x y := by
    intro x y
    simpa [instActionCanon] using
      orbitRel_compHom_mulEquiv_iff_sec9
        (A := ULift.{u,0} (Multiplicative (ZMod a))) (B := A) (κ := κ)
        eCanon x y
  let orbitToA :
      Quotient (MulAction.orbitRel (ULift.{u,0} (Multiplicative (ZMod a))) κ) →
        Quotient (MulAction.orbitRel A κ) :=
    Quotient.map (fun x : κ => x) (by
      intro x y hxy
      exact (hrel x y).mp hxy)
  have hOrbitMap_inj : Function.Injective orbitToA := by
    intro i j hij
    refine Quotient.inductionOn₂ i j ?_ hij
    intro x y hxy
    apply Quotient.sound
    exact (hrel x y).mpr (Quotient.exact hxy)
  let θCanon :
      Quotient (MulAction.orbitRel
        (ULift.{u,0} (Multiplicative (ZMod a))) κ) →
          Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M) :=
    fun i => θA (orbitToA i)
  refine ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard,
    instActionCanon, ?_, θCanon, ?_, ?_⟩
  · have hfreeA' : ∀ k : κ, MulAction.stabilizer A k = ⊥ := by
      intro k
      simpa [κ] using hfreeA k
    simpa [κ, instActionCanon] using
      stabilizer_compHom_mulEquiv_eq_bot_sec9
        (A := ULift.{u,0} (Multiplicative (ZMod a))) (B := A) (κ := κ)
        eCanon hfreeA'
  · intro i j hij
    exact hOrbitMap_inj (hθinjA (by simpa [θCanon] using hij))
  · intro i
    simpa [θCanon] using hθdataA (orbitToA i)

private theorem theorem_9_8_initial_constituent_Mtheta_free_action_data_of_cyclic_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) [NeZero a] :
    theorem_9_8_initial_constituent_Mtheta_cyclic_action_data_sec9
      M MF U H0 Uprime p a →
        theorem_9_8_initial_constituent_Mtheta_free_action_data_sec9
          M MF U H0 Uprime p a := by
  intro hcyc
  classical
  rcases hcyc with
    ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard, instAction, hfree,
      θ, hθinj, hθdata⟩
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  let A : Type u := ULift.{u,0} (Multiplicative (ZMod a))
  let instGroupA : Group A := inferInstance
  letI : Fintype (ZMod a) := ZMod.fintype a
  let instFintypeA : Fintype A :=
    Fintype.ofEquiv (Multiplicative (ZMod a)) Equiv.ulift.symm
  have hAcard : Nat.card A = a := by
    calc
      Nat.card A = Nat.card (Multiplicative (ZMod a)) :=
        Nat.card_congr Equiv.ulift
      _ = a :=
        (Nat.card_congr
          (Multiplicative.toAdd : Multiplicative (ZMod a) ≃ ZMod a)).trans
          (Nat.card_zmod a)
  exact ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard,
    A, instGroupA, instFintypeA, hAcard, instAction, hfree, θ, hθinj, hθdata⟩

private theorem theorem_9_8_initial_constituent_Mtheta_raw_product_data_of_free_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) :
    theorem_9_8_initial_constituent_Mtheta_free_action_data_sec9
      M MF U H0 Uprime p a →
        theorem_9_8_initial_constituent_Mtheta_raw_product_data_sec9
          M MF U H0 Uprime p a := by
  intro hfreeData
  classical
  rcases hfreeData with
    ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard,
      A, instGroupA, instFintypeA, hAcard, instAction, hfree, θ, hθinj,
      hθdata⟩
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  letI : Group A := instGroupA
  letI : Fintype A := instFintypeA
  let κ : Type u := Fin (p - 1) × Lam
  letI : MulAction A κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel A κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  refine ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard,
    ι, instFintypeι, instDecidableEqι, orbit, ?_, θ, ?_, ?_⟩
  · intro i
    rw [← hAcard]
    rw [← Nat.card_eq_fintype_card]
    exact freeAction_orbitQuotient_fiber_natCard_sec9 (A := A) (κ := κ)
      hfree i
  · simpa [κ, ι] using hθinj
  · intro i
    simpa [κ, ι] using hθdata i

private theorem theorem_9_8_initial_constituent_Mtheta_data_of_raw_product_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) :
    theorem_9_8_initial_constituent_Mtheta_raw_product_data_sec9
      M MF U H0 Uprime p a →
        theorem_9_8_initial_constituent_Mtheta_data_sec9 M MF U H0 Uprime p a := by
  intro hraw
  classical
  rcases hraw with
    ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard,
      ι, instFintypeι, instDecidableEqι, orbit, hfiber, θ, hθinj, hθdata⟩
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let κ : Type u := Fin (p - 1) × Lam
  let instFintypeκ : Fintype κ := inferInstance
  let instDecidableEqκ : DecidableEq κ := inferInstance
  refine ⟨κ, instFintypeκ, instDecidableEqκ,
    ι, instFintypeι, instDecidableEqι, orbit, ?_, hfiber, θ, hθinj, hθdata⟩
  calc
    Fintype.card κ = (p - 1) * Fintype.card Lam := by
      simp [κ]
    _ = (p - 1) * (Nat.card U / (a * Nat.card Uprime)) := by
      rw [hLamcard]

private theorem theorem_9_8_initial_constituent_orbit_data_of_Mtheta_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) :
    a ∣ p - 1 →
      theorem_9_8_initial_constituent_Mtheta_data_sec9 M MF U H0 Uprime p a →
        theorem_9_8_initial_constituent_orbit_data_sec9 M MF U H0 Uprime p a := by
  intro hdiv hMtheta
  classical
  rcases hMtheta with
    ⟨κ, instFintypeκ, instDecidableEqκ,
      ι, instFintypeι, instDecidableEqι, orbit, hκcard, hfiber,
      θ, hθinj, hθdata⟩
  letI : Fintype κ := instFintypeκ
  letI : DecidableEq κ := instDecidableEqκ
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  refine ⟨κ, instFintypeκ, instDecidableEqκ,
    ι, instFintypeι, instDecidableEqι, orbit, ?_, hfiber, θ, hθinj, hθdata⟩
  let b : ℕ := Nat.card U / (a * Nat.card Uprime)
  have hrawEq :
      (((p - 1) / a) * b) * a = Fintype.card κ := by
    calc
      (((p - 1) / a) * b) * a = (p - 1) * b := by
        rw [Nat.mul_assoc, Nat.mul_comm b a, ← Nat.mul_assoc,
          Nat.div_mul_cancel hdiv]
      _ = Fintype.card κ := hκcard.symm
  simpa [b] using le_of_eq hrawEq

private theorem theorem_9_8_initial_constituent_family_data_of_orbit_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) :
    0 < a →
      theorem_9_8_initial_constituent_orbit_data_sec9 M MF U H0 Uprime p a →
        theorem_9_8_initial_constituent_family_data_sec9 M MF U H0 Uprime p a := by
  intro ha horbit
  classical
  rcases horbit with
    ⟨κ, instFintypeκ, _instDecidableEqκ,
      ι, instFintypeι, instDecidableEqι, orbit, hrawCard, hfiber,
      θ, hθinj, hθdata⟩
  letI : Fintype κ := instFintypeκ
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  refine ⟨ι, instFintypeι, instDecidableEqι, θ, hθinj, ?_, hθdata⟩
  have hκcard :
      Fintype.card κ = a * Fintype.card ι :=
    card_eq_mul_card_of_fiber_card_sec9 orbit a hfiber
  have hmul :
      (((p - 1) / a) * (Nat.card U / (a * Nat.card Uprime))) * a ≤
        Fintype.card ι * a := by
    calc
      (((p - 1) / a) * (Nat.card U / (a * Nat.card Uprime))) * a
          ≤ Fintype.card κ := hrawCard
      _ = a * Fintype.card ι := hκcard
      _ = Fintype.card ι * a := Nat.mul_comm a (Fintype.card ι)
  exact le_of_mul_le_mul_right hmul ha

private def theorem_9_8_initial_constituent_Mtheta_base_range_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩)) : Prop :=
  ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
    ∃ instDecidableEqLam : DecidableEq Lam,
    letI : Fintype Lam := instFintypeLam
    letI : DecidableEq Lam := instDecidableEqLam
    Fintype.card Lam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ instAction : MulAction ρBase.range (Fin (p - 1) × Lam),
        letI : MulAction ρBase.range (Fin (p - 1) × Lam) := instAction
        (∀ k : Fin (p - 1) × Lam, MulAction.stabilizer ρBase.range k = ⊥) ∧
          ∃ θ :
            Quotient (MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam)) →
              Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
            Function.Injective
                (fun i : Quotient
                    (MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam)) =>
                  Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                    (θ i)) ∧
              ∀ i : Quotient
                  (MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam)),
                Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                  ¬ Section1.subgroupInKernel' (θ i)
                    ((MF.subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.subgroupInKernel' (θ i)
                    (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.degree (θ i) = (a : ℂ) ∧
                  Section1.IsIrreducibleCharacterOnGroup
                    (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θ i))

private theorem theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
    {G : Type u} [Group G] [Finite G]
    (U Uprime : Subgroup G)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    (Uprime.subgroupOf U).Normal := by
  classical
  rw [hUprimeEq]
  have hsub :
      ((Subgroup.map U.subtype (_root_.commutator U)).subgroupOf U) =
        _root_.commutator U := by
    ext x
    constructor
    · intro hx
      change (x : G) ∈ Subgroup.map U.subtype (_root_.commutator U) at hx
      rcases hx with ⟨y, hy, hyx⟩
      have hxy : x = y := Subtype.ext (by simpa using hyx.symm)
      simpa [hxy]
    · intro hx
      change (x : G) ∈ Subgroup.map U.subtype (_root_.commutator U)
      exact ⟨x, hx, rfl⟩
  rw [hsub]
  infer_instance

private theorem theorem_9_8_initial_constituent_Mtheta_baseActionKernel_uprime_le_sec9
    {G Q : Type u} [Group G] [Finite G] [Group Q]
    (U C Uprime : Subgroup G)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut Q)
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    let f : U →* ρBase.range :=
      ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
    Uprime.subgroupOf U ≤ f.ker := by
  classical
  intro f x hx
  have hxG : (x : G) ∈ Uprime := by
    simpa [Subgroup.mem_subgroupOf] using hx
  rw [hUprimeEq] at hxG
  rcases hxG with ⟨y, hy, hy_eq⟩
  have hxy : x = y := Subtype.ext (by simpa using hy_eq.symm)
  letI : IsCyclic ρBase.range := hρcycBase
  letI : CommGroup ρBase.range := IsCyclic.commGroup
  have hyker : y ∈ f.ker := Abelianization.commutator_subset_ker f hy
  simpa [hxy]

private theorem theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
    {G Q : Type u} [Group G] [Finite G] [Group Q]
    (U C Uprime : Subgroup G)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut Q)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    let f : U →* ρBase.range :=
      ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
    let K : Subgroup U := f.ker
    let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
    letI : Hsub.Normal :=
      (theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
        U Uprime hUprimeEq).subgroupOf K
    IsMulCommutative (K ⧸ Hsub) := by
  classical
  intro f K Hsub
  letI : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  letI : Hsub.Normal :=
    (theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq).subgroupOf K
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  intro x hx
  change (x : U) ∈ Uprime.subgroupOf U
  rw [hUprimeEq]
  have hsub :
      ((Subgroup.map U.subtype (_root_.commutator U)).subgroupOf U) =
        _root_.commutator U := by
    ext y
    constructor
    · intro hy
      change (y : G) ∈ Subgroup.map U.subtype (_root_.commutator U) at hy
      rcases hy with ⟨z, hz, hzy⟩
      have hyz : y = z := Subtype.ext (by simpa using hzy.symm)
      simpa [hyz]
    · intro hy
      change (y : G) ∈ Subgroup.map U.subtype (_root_.commutator U)
      exact ⟨y, hy, rfl⟩
  rw [hsub]
  have hxmap : (x : U) ∈ (_root_.commutator K).map K.subtype := by
    exact ⟨x, hx, rfl⟩
  rw [Subgroup.map_subtype_commutator] at hxmap
  exact Subgroup.commutator_mono (show K ≤ (⊤ : Subgroup U) by exact le_top)
    (show K ≤ (⊤ : Subgroup U) by exact le_top) hxmap

private theorem theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_card_sec9
    {G Q : Type u} [Group G] [Finite G] [Group Q]
    (U C Uprime : Subgroup G)
    (a : ℕ) [NeZero a]
    [hnormalC : (C.subgroupOf U).Normal]
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut Q)
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    let f : U →* ρBase.range :=
      ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
    let K : Subgroup U := f.ker
    let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
    letI : Hsub.Normal :=
      (theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
        U Uprime hUprimeEq).subgroupOf K
    Nat.card (K ⧸ Hsub) = Nat.card U / (a * Nat.card Uprime) := by
  classical
  intro f K Hsub
  letI : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  letI : Hsub.Normal :=
    (theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq).subgroupOf K
  have hf_range_top : f.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  have hKindex : K.index = a := by
    calc
      K.index = Nat.card f.range := by simpa [K] using Subgroup.index_ker f
      _ = Nat.card (⊤ : Subgroup ρBase.range) := by rw [hf_range_top]
      _ = Nat.card ρBase.range := by simp
      _ = a := hρcardBase
  have hKmul : a * Nat.card K = Nat.card U := by
    simpa [hKindex] using (Subgroup.index_mul_card (H := K))
  have hUprimeU : Uprime ≤ U := by
    rw [hUprimeEq, Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_le_self U
  have hUprime_le_K : Uprime.subgroupOf U ≤ K := by
    simpa [K] using
      theorem_9_8_initial_constituent_Mtheta_baseActionKernel_uprime_le_sec9
        U C Uprime ρBase hρcycBase hUprimeEq
  have hHsub_card : Nat.card Hsub = Nat.card Uprime := by
    calc
      Nat.card Hsub = Nat.card (Uprime.subgroupOf U) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUprime_le_K).toEquiv
      _ = Nat.card Uprime :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUprimeU).toEquiv
  have hquot_mul : Nat.card K = Nat.card (K ⧸ Hsub) * Nat.card Hsub := by
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup Hsub
  have hmain : (a * Nat.card Uprime) * Nat.card (K ⧸ Hsub) = Nat.card U := by
    calc
      (a * Nat.card Uprime) * Nat.card (K ⧸ Hsub)
          = a * (Nat.card (K ⧸ Hsub) * Nat.card Uprime) := by ac_rfl
      _ = a * (Nat.card (K ⧸ Hsub) * Nat.card Hsub) := by rw [hHsub_card]
      _ = a * Nat.card K := by rw [← hquot_mul]
      _ = Nat.card U := hKmul
  have hden_ne : a * Nat.card Uprime ≠ 0 := by
    exact Nat.ne_of_gt
      (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne a)) (Nat.card_pos))
  exact Nat.eq_div_of_mul_eq_right hden_ne hmain

private def theorem_9_8_initial_constituent_Mtheta_clam_parameter_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩)) : Prop :=
  ∃ Clam : Type u, ∃ instGroupClam : Group Clam,
    ∃ instFintypeClam : Fintype Clam, ∃ instDecidableEqClam : DecidableEq Clam,
    letI : Group Clam := instGroupClam
    letI : Fintype Clam := instFintypeClam
    letI : DecidableEq Clam := instDecidableEqClam
    letI : Finite Clam := Finite.of_fintype Clam
    IsMulCommutative Clam ∧
      Fintype.card Clam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
        ∃ instDecidableEqLam : DecidableEq Lam,
        letI : Fintype Lam := instFintypeLam
        letI : DecidableEq Lam := instDecidableEqLam
        ∃ lam : Lam → Clam →* ℂˣ,
          Function.Injective lam ∧
            Fintype.card Lam = Fintype.card Clam ∧
            (∀ j : Lam,
              Section1.IsIrreducibleCharacterOnGroup
                (fun x : Clam => (lam j x : ℂ)) ∧
                Section1.degree (fun x : Clam => (lam j x : ℂ)) = 1) ∧
            ∃ instAction : MulAction ρBase.range (Fin (p - 1) × Lam),
              letI : MulAction ρBase.range (Fin (p - 1) × Lam) := instAction
              (∀ k : Fin (p - 1) × Lam, MulAction.stabilizer ρBase.range k = ⊥) ∧
                ∃ θ :
                  Quotient (MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam)) →
                    Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
                  Function.Injective
                      (fun i : Quotient
                          (MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam)) =>
                        Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                          (θ i)) ∧
                    ∀ i : Quotient
                        (MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam)),
                      Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                        ¬ Section1.subgroupInKernel' (θ i)
                          ((MF.subgroupOf M).subgroupOf
                            ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                        Section1.subgroupInKernel' (θ i)
                          (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                            ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                        Section1.degree (θ i) = (a : ℂ) ∧
                        Section1.IsIrreducibleCharacterOnGroup
                          (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                            (θ i))

private def theorem_9_8_initial_constituent_Mtheta_clam_raw_theta_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩)) : Prop :=
  ∃ Clam : Type u, ∃ instGroupClam : Group Clam,
    ∃ instFintypeClam : Fintype Clam, ∃ instDecidableEqClam : DecidableEq Clam,
    letI : Group Clam := instGroupClam
    letI : Fintype Clam := instFintypeClam
    letI : DecidableEq Clam := instDecidableEqClam
    letI : Finite Clam := Finite.of_fintype Clam
    IsMulCommutative Clam ∧
      Fintype.card Clam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
        ∃ instDecidableEqLam : DecidableEq Lam,
        letI : Fintype Lam := instFintypeLam
        letI : DecidableEq Lam := instDecidableEqLam
        ∃ lam : Lam → Clam →* ℂˣ,
          Function.Injective lam ∧
            Fintype.card Lam = Fintype.card Clam ∧
            (∀ j : Lam,
              Section1.IsIrreducibleCharacterOnGroup
                (fun x : Clam => (lam j x : ℂ)) ∧
                Section1.degree (fun x : Clam => (lam j x : ℂ)) = 1) ∧
            ∃ instAction : MulAction ρBase.range (Fin (p - 1) × Lam),
              letI : MulAction ρBase.range (Fin (p - 1) × Lam) := instAction
              (∀ k : Fin (p - 1) × Lam, MulAction.stabilizer ρBase.range k = ⊥) ∧
                ∃ θraw : Fin (p - 1) × Lam →
                    Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
                  (∀ k : Fin (p - 1) × Lam,
                    Section1.IsIrreducibleCharacterOnGroup (θraw k) ∧
                      ¬ Section1.subgroupInKernel' (θraw k)
                        ((MF.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                      Section1.subgroupInKernel' (θraw k)
                        (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                      Section1.degree (θraw k) = (a : ℂ) ∧
                      Section1.IsIrreducibleCharacterOnGroup
                        (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                          (θraw k))) ∧
                    ∀ k l : Fin (p - 1) × Lam,
                      Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                          (θraw k) =
                        Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                          (θraw l) →
                        MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l

private def theorem_9_8_initial_constituent_Mtheta_clam_index_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩)) : Prop :=
  ∃ Clam : Type u, ∃ instGroupClam : Group Clam,
    ∃ instFintypeClam : Fintype Clam, ∃ instDecidableEqClam : DecidableEq Clam,
    letI : Group Clam := instGroupClam
    letI : Fintype Clam := instFintypeClam
    letI : DecidableEq Clam := instDecidableEqClam
    letI : Finite Clam := Finite.of_fintype Clam
    IsMulCommutative Clam ∧
      Fintype.card Clam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
        ∃ instDecidableEqLam : DecidableEq Lam,
        letI : Fintype Lam := instFintypeLam
        letI : DecidableEq Lam := instDecidableEqLam
        ∃ lam : Lam → Clam →* ℂˣ,
          Function.Injective lam ∧
            Fintype.card Lam = Fintype.card Clam ∧
            (∀ j : Lam,
              Section1.IsIrreducibleCharacterOnGroup
                (fun x : Clam => (lam j x : ℂ)) ∧
                Section1.degree (fun x : Clam => (lam j x : ℂ)) = 1) ∧
            ∃ instLamAction : MulAction ρBase.range Lam,
              let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
                Subgroup.subtype ρBase.range
              let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
                nonprincipalLinearCharacterIndexMulAction_sec9 p
                  (hHcard ⟨0, hqpos⟩) ρRange
              letI : MulAction ρBase.range Lam := instLamAction
              letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
              ∃ θraw : Fin (p - 1) × Lam →
                  Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
                (∀ k : Fin (p - 1) × Lam,
                  Section1.IsIrreducibleCharacterOnGroup (θraw k) ∧
                    ¬ Section1.subgroupInKernel' (θraw k)
                      ((MF.subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                    Section1.subgroupInKernel' (θraw k)
                      (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                    Section1.degree (θraw k) = (a : ℂ) ∧
                    Section1.IsIrreducibleCharacterOnGroup
                      (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                        (θraw k))) ∧
                  ∀ k l : Fin (p - 1) × Lam,
                    Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                        (θraw k) =
                    Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θraw l) →
                      MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l

private def theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) : Prop :=
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  letI : Fintype Clam := Fintype.ofFinite Clam
  letI : DecidableEq Clam := Classical.decEq Clam
  ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
    ∃ instDecidableEqLam : DecidableEq Lam,
      letI : Fintype Lam := instFintypeLam
      letI : DecidableEq Lam := instDecidableEqLam
      ∃ lam : Lam → Clam →* ℂˣ,
        Function.Injective lam ∧
          Fintype.card Lam = Fintype.card Clam ∧
          (∀ j : Lam,
            Section1.IsIrreducibleCharacterOnGroup
              (fun x : Clam => (lam j x : ℂ)) ∧
              Section1.degree (fun x : Clam => (lam j x : ℂ)) = 1) ∧
          ∃ instLamAction : MulAction ρBase.range Lam,
            let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
              Subgroup.subtype ρBase.range
            let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
              nonprincipalLinearCharacterIndexMulAction_sec9 p
                (hHcard ⟨0, hqpos⟩) ρRange
            letI : MulAction ρBase.range Lam := instLamAction
            letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
            ∃ θraw : Fin (p - 1) × Lam →
                Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
              (∀ k : Fin (p - 1) × Lam,
                Section1.IsIrreducibleCharacterOnGroup (θraw k) ∧
                  ¬ Section1.subgroupInKernel' (θraw k)
                    ((MF.subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.subgroupInKernel' (θraw k)
                    (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.degree (θraw k) = (a : ℂ) ∧
                  Section1.IsIrreducibleCharacterOnGroup
                    (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θraw k))) ∧
                ∀ k l : Fin (p - 1) × Lam,
                  Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θraw k) =
                    Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θraw l) →
                    MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l

private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_index_action_data_of_clam_kernel_quotient_theta_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hUprimeEq →
        theorem_9_8_initial_constituent_Mtheta_clam_index_action_data_sec9
          M MF U H0 C Uprime p q a H hqpos hHcard ρBase := by
  intro hkernel
  classical
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_data_sec9]
    at hkernel
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  letI : Fintype Clam := Fintype.ofFinite Clam
  letI : DecidableEq Clam := Classical.decEq Clam
  rcases hkernel with
    ⟨Lam, instFintypeLam, instDecidableEqLam, lam, hlaminj, hLamClamcard,
      hlamdata, instLamAction, θraw, hθrawdata, hθraworbit⟩
  let instGroupClam : Group Clam := inferInstance
  let instFintypeClam : Fintype Clam := inferInstance
  let instDecidableEqClam : DecidableEq Clam := inferInstance
  have hClamComm : IsMulCommutative Clam := by
    simpa [Clam, Hsub, K, f] using
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
        U C Uprime ρBase hUprimeEq
  have hClamcard : Fintype.card Clam = Nat.card U / (a * Nat.card Uprime) := by
    rw [← Nat.card_eq_fintype_card]
    simpa [Clam, Hsub, K, f] using
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_card_sec9
        U C Uprime a ρBase hρcycBase hρcardBase hUprimeEq
  exact ⟨Clam, instGroupClam, instFintypeClam, instDecidableEqClam,
    hClamComm, hClamcard, Lam, instFintypeLam, instDecidableEqLam, lam,
    hlaminj, hLamClamcard, hlamdata, instLamAction, θraw, hθrawdata,
    hθraworbit⟩

private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_raw_theta_data_of_clam_index_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hp : Nat.Prime p) :
    theorem_9_8_initial_constituent_Mtheta_clam_index_action_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase →
        theorem_9_8_initial_constituent_Mtheta_clam_raw_theta_data_sec9
          M MF U H0 C Uprime p q a H hqpos ρBase := by
  intro hindex
  classical
  rcases hindex with
    ⟨Clam, instGroupClam, instFintypeClam, instDecidableEqClam,
      hClamComm, hClamcard, Lam, instFintypeLam, instDecidableEqLam,
      lam, hlaminj, hLamClamcard, hlamdata, instLamAction, θraw,
      hθrawdata, hθraworbit⟩
  letI : Group Clam := instGroupClam
  letI : Fintype Clam := instFintypeClam
  letI : DecidableEq Clam := instDecidableEqClam
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let instPairAction : MulAction ρBase.range (Fin (p - 1) × Lam) := inferInstance
  refine ⟨Clam, instGroupClam, instFintypeClam, instDecidableEqClam,
    hClamComm, hClamcard, Lam, instFintypeLam, instDecidableEqLam, lam,
    hlaminj, hLamClamcard, hlamdata, instPairAction, ?_, θraw, ?_, ?_⟩
  · letI : MulAction ρBase.range (Fin (p - 1) × Lam) := instPairAction
    intro k
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_bot]
      rw [MulAction.mem_stabilizer_iff] at hx
      have hfirst : x • k.1 = k.1 := by
        exact congrArg Prod.fst hx
      let e := nonprincipalLinearCharacterEquivFin_sec9
        (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)
      have hcharfixed :
          nonprincipalLinearCharacterDualEquiv_sec9 (ρRange x) (e k.1) =
            e k.1 := by
        apply Subtype.ext
        have hspec :=
          nonprincipalLinearCharacterIndexMulAction_spec_sec9
            p (hHcard ⟨0, hqpos⟩) ρRange x k.1
        have hleft : (e (x • k.1)).1 = (e k.1).1 := by
          exact congrArg Subtype.val (congrArg e hfirst)
        exact hspec.symm.trans hleft
      have hxval : (x : MulAut (H ⟨0, hqpos⟩)) = 1 :=
        mulAut_eq_one_of_nonprincipalLinearCharacterDualEquiv_eq_self_sec9
          (hHcard ⟨0, hqpos⟩) hp (ρRange x) (e k.1) hcharfixed
      exact Subtype.ext hxval
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [MulAction.mem_stabilizer_iff]
      simp [hx]
  · intro k
    simpa [instPairAction] using hθrawdata k
  · intro k l
    simpa [instPairAction] using hθraworbit k l

private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_parameter_data_of_clam_raw_theta_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩)) :
    theorem_9_8_initial_constituent_Mtheta_clam_raw_theta_data_sec9
      M MF U H0 C Uprime p q a H hqpos ρBase →
        theorem_9_8_initial_constituent_Mtheta_clam_parameter_data_sec9
          M MF U H0 C Uprime p q a H hqpos ρBase := by
  intro hraw
  classical
  rcases hraw with
    ⟨Clam, instGroupClam, instFintypeClam, instDecidableEqClam,
      hClamComm, hClamcard, Lam, instFintypeLam, instDecidableEqLam,
      lam, hlaminj, hLamClamcard, hlamdata, instAction, hfree, θraw,
      hθrawdata, hθraworbit⟩
  letI : Group Clam := instGroupClam
  letI : Fintype Clam := instFintypeClam
  letI : DecidableEq Clam := instDecidableEqClam
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  letI : MulAction ρBase.range (Fin (p - 1) × Lam) := instAction
  let κ : Type u := Fin (p - 1) × Lam
  let θ : Quotient (MulAction.orbitRel ρBase.range κ) →
      Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M) :=
    fun i => θraw i.out
  refine ⟨Clam, instGroupClam, instFintypeClam, instDecidableEqClam,
    hClamComm, hClamcard, Lam, instFintypeLam, instDecidableEqLam, lam,
    hlaminj, hLamClamcard, hlamdata, instAction, hfree, θ, ?_, ?_⟩
  · intro i j hij
    have hrel :
        MulAction.orbitRel ρBase.range κ i.out j.out := by
      exact hθraworbit i.out j.out hij
    calc
      i = Quotient.mk (MulAction.orbitRel ρBase.range κ) i.out :=
        (Quotient.out_eq i).symm
      _ = Quotient.mk (MulAction.orbitRel ρBase.range κ) j.out :=
        Quotient.sound hrel
      _ = j := Quotient.out_eq j
  · intro i
    simpa [θ, κ] using hθrawdata i.out

private theorem
    theorem_9_8_initial_constituent_Mtheta_base_range_action_data_of_clam_parameter_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩)) :
    theorem_9_8_initial_constituent_Mtheta_clam_parameter_data_sec9
      M MF U H0 C Uprime p q a H hqpos ρBase →
        theorem_9_8_initial_constituent_Mtheta_base_range_action_data_sec9
          M MF U H0 C Uprime p q a H hqpos ρBase := by
  intro hclam
  classical
  rcases hclam with
    ⟨Clam, instGroupClam, instFintypeClam, instDecidableEqClam,
      _hClamComm, hClamcard, Lam, instFintypeLam, instDecidableEqLam,
      _lam, _hlaminj, hLamClamcard, _hlamdata, instAction, hfree, θ, hθinj,
      hθdata⟩
  letI : Group Clam := instGroupClam
  letI : Fintype Clam := instFintypeClam
  letI : DecidableEq Clam := instDecidableEqClam
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  refine ⟨Lam, instFintypeLam, instDecidableEqLam, ?_, instAction, hfree, θ,
    hθinj, hθdata⟩
  exact hLamClamcard.trans hClamcard

private theorem theorem_9_8_initial_constituent_Mtheta_abstract_cyclic_action_data_of_base_range_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a) :
    theorem_9_8_initial_constituent_Mtheta_base_range_action_data_sec9
      M MF U H0 C Uprime p q a H hqpos ρBase →
        theorem_9_8_initial_constituent_Mtheta_abstract_cyclic_action_data_sec9
          M MF U H0 Uprime p a := by
  intro hrange
  classical
  rcases hrange with
    ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard, instAction, hfree,
      θ, hθinj, hθdata⟩
  let A : Type u := ρBase.range
  let instGroupA : Group A := inferInstance
  let instFintypeA : Fintype A := Fintype.ofFinite A
  exact ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard,
    A, instGroupA, instFintypeA, by simpa [A] using hρcycBase,
    by simpa [A] using hρcardBase, instAction, hfree, θ, hθinj, hθdata⟩

private def
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) : Prop := by
  classical
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  exact
    ∃ θraw : Fin (p - 1) × Lam →
        Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
      (∀ k : Fin (p - 1) × Lam,
        Section1.IsIrreducibleCharacterOnGroup (θraw k) ∧
          ¬ Section1.subgroupInKernel' (θraw k)
            ((MF.subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M)) ∧
          Section1.subgroupInKernel' (θraw k)
            (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M)) ∧
          Section1.degree (θraw k) = (a : ℂ) ∧
          Section1.IsIrreducibleCharacterOnGroup
            (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
              (θraw k))) ∧
                ∀ k l : Fin (p - 1) × Lam,
                  Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θraw k) =
                    Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θraw l) →
                    MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l

private def
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) : Prop := by
  classical
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  exact
    ∃ B : Subgroup Dm,
      ∃ hBnormal : B.Normal,
      ∃ hAnormal : A.Normal,
      A ≤ B ∧
        Subgroup.index B = a ∧
        letI : B.Normal := hBnormal
        letI : A.Normal := hAnormal
        ∃ ψraw : Fin (p - 1) × Lam → Section1.ClassFunction B,
          (∀ k : Fin (p - 1) × Lam,
            Section1.IsIrreducibleCharacterOnGroup (ψraw k) ∧
              Section1.inertiaSubgroup B (ψraw k) = B ∧
              Section1.subgroupInKernel' (ψraw k) (A.subgroupOf B) ∧
              Section1.degree (ψraw k) = 1) ∧
            (∀ k : Fin (p - 1) × Lam,
              ¬ Section1.subgroupInKernel'
                (Section1.inducedCF B (ψraw k)) MFD) ∧
            (∀ k : Fin (p - 1) × Lam,
              Section1.IsIrreducibleCharacterOnGroup
                (Section1.inducedCF Dm (Section1.inducedCF B (ψraw k)))) ∧
            ∀ k l : Fin (p - 1) × Lam,
              Section1.inducedCF Dm (Section1.inducedCF B (ψraw k)) =
                Section1.inducedCF Dm (Section1.inducedCF B (ψraw l)) →
              MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l

private def
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) : Prop := by
  classical
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  exact
    ∃ B : Subgroup Dm,
      ∃ hBnormal : B.Normal,
      ∃ hAnormal : A.Normal,
      A ≤ B ∧
        Subgroup.index B = a ∧
        letI : B.Normal := hBnormal
        letI : A.Normal := hAnormal
        letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
        ∃ ψlin : Fin (p - 1) × Lam → (B ⧸ A.subgroupOf B) →* ℂˣ,
          (∀ k : Fin (p - 1) × Lam,
            Section1.inertiaSubgroup B
              (Section1.quotientCharacterInflation A B (ψlin k)) = B) ∧
            (∀ k : Fin (p - 1) × Lam,
              ¬ Section1.subgroupInKernel'
                (Section1.inducedCF B
                  (Section1.quotientCharacterInflation A B (ψlin k))) MFD) ∧
            (∀ k : Fin (p - 1) × Lam,
              Section1.IsIrreducibleCharacterOnGroup
                (Section1.inducedCF Dm
                  (Section1.inducedCF B
                    (Section1.quotientCharacterInflation A B (ψlin k))))) ∧
            ∀ k l : Fin (p - 1) × Lam,
              Section1.inducedCF Dm
                  (Section1.inducedCF B
                    (Section1.quotientCharacterInflation A B (ψlin k))) =
                Section1.inducedCF Dm
                  (Section1.inducedCF B
                    (Section1.quotientCharacterInflation A B (ψlin l))) →
              MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l

private def theorem_9_8_MFDSubgroupOf_to_MF_sec9
    {G : Type u} [Group G] (M MF : Subgroup G) :
    ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →* MF where
  toFun x :=
    ⟨(((x : (ambientDerivedSubgroup M).subgroupOf M) : M) : G), by
      change ((x : (ambientDerivedSubgroup M).subgroupOf M) : M) ∈ MF.subgroupOf M
      exact x.property⟩
  map_one' := by
    ext
    rfl
  map_mul' := by
    intro x y
    ext
    rfl

private def
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_structure_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [_hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (_hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (_hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) : Prop := by
  classical
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  let W : Subgroup Dm := ((U.subgroupOf M).subgroupOf Dm)
  exact
    ∃ B : Subgroup Dm,
      ∃ hBnormal : B.Normal,
      ∃ hAnormal : A.Normal,
      A ≤ B ∧
        Subgroup.index B = a ∧
        MFD ≤ B ∧
        ∃ hBsemi : Section2.IsInternalSemidirectProduct B MFD (W ⊓ B),
        ∃ eWBK : ↥(W ⊓ B) ≃* K,
          (∀ x : ↥(W ⊓ B),
            (((eWBK x : K) : U) : G) = ((((x : Dm) : M) : G))) ∧
        letI : B.Normal := hBnormal
        letI : A.Normal := hAnormal
        letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
        let Q : Type u := B ⧸ A.subgroupOf B
        letI : Group Q := inferInstance
        let MFDsubB : Subgroup B := MFD.subgroupOf B
        ∃ QMF : Subgroup Q,
        ∃ QH1c : Subgroup Q,
        ∃ QH1 : Subgroup Q,
        ∃ QClam : Subgroup Q,
        ∃ QH1CH1 : Subgroup Q,
        ∃ hsemi : Section2.IsInternalSemidirectProduct
            (⊤ : Subgroup Q) QH1c QH1CH1,
        ∃ hprod : Section2.IsInternalDirectProduct QH1CH1 QH1 QClam,
        ∃ eH1 : QH1 ≃* H ⟨0, hqpos⟩,
        ∃ eClam : QClam ≃* Clam,
          (∀ m : MFDsubB,
            ∀ hmH1 :
              QuotientGroup.mk' (H0.subgroupOf MF)
                  (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                    ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
                H ⟨0, hqpos⟩,
              ∃ hmQH1 : QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1,
                eH1
                    ⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ =
                  ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                      (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                        ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)),
                    hmH1⟩) ∧
          (∀ m : MFDsubB,
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
              (⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i) →
            QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1c) ∧
          (∀ w : (W ⊓ B).subgroupOf B,
            ∃ hwQClam : QuotientGroup.mk' (A.subgroupOf B) w ∈ QClam,
              eClam
                  ⟨QuotientGroup.mk' (A.subgroupOf B) w, hwQClam⟩ =
                QuotientGroup.mk' Hsub
                    (eWBK
                      (⟨((w : B) : Dm), by
                        simpa [W, Subgroup.mem_subgroupOf] using w.property⟩ :
                        ↥(W ⊓ B)))) ∧
          QMF =
              ((MFD.subgroupOf B).map (QuotientGroup.mk' (A.subgroupOf B))) ∧
          Section2.IsInternalDirectProduct QMF QH1c QH1 ∧
            QH1 ≤ QMF

private def
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) : Prop := by
  classical
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  exact
    ∃ B : Subgroup Dm,
      ∃ hBnormal : B.Normal,
      ∃ hAnormal : A.Normal,
      A ≤ B ∧
        Subgroup.index B = a ∧
        letI : B.Normal := hBnormal
        letI : A.Normal := hAnormal
        letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
        let Q : Type u := B ⧸ A.subgroupOf B
        letI : Group Q := inferInstance
        ∃ QH1c : Subgroup Q,
        ∃ QH1 : Subgroup Q,
        ∃ QClam : Subgroup Q,
        ∃ QH1CH1 : Subgroup Q,
        ∃ hsemi : Section2.IsInternalSemidirectProduct
            (⊤ : Subgroup Q) QH1c QH1CH1,
        ∃ hprod : Section2.IsInternalDirectProduct QH1CH1 QH1 QClam,
        ∃ eH1 : QH1 ≃* H ⟨0, hqpos⟩,
        ∃ eClam : QClam ≃* Clam,
          let ψlin : Fin (p - 1) × Lam → Q →* ℂˣ := fun k =>
            semidirectProductOfInternalDirectProductLinearCharacter_sec9
              hsemi hprod
              (((nonprincipalLinearCharacterEquivFin_sec9
                    (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1.comp
                eH1.toMonoidHom)
              (k.2.comp eClam.toMonoidHom)
          (∀ k : Fin (p - 1) × Lam,
            Section1.inertiaSubgroup B
              (Section1.quotientCharacterInflation A B (ψlin k)) = B) ∧
            (∀ k : Fin (p - 1) × Lam,
              ¬ Section1.subgroupInKernel'
                (Section1.inducedCF B
                  (Section1.quotientCharacterInflation A B (ψlin k))) MFD) ∧
            (∀ k : Fin (p - 1) × Lam,
              Section1.IsIrreducibleCharacterOnGroup
                (Section1.inducedCF Dm
                  (Section1.inducedCF B
                    (Section1.quotientCharacterInflation A B (ψlin k))))) ∧
            ∀ k l : Fin (p - 1) × Lam,
              Section1.inducedCF Dm
                  (Section1.inducedCF B
                    (Section1.quotientCharacterInflation A B (ψlin k))) =
                Section1.inducedCF Dm
                  (Section1.inducedCF B
                    (Section1.quotientCharacterInflation A B (ψlin l))) →
              MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l

private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_of_semidirect_product_formula_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq →
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  intro hformula
  classical
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_data_sec9]
    at hformula
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_sec9]
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  rcases hformula with
    ⟨B, hBnormal, hAnormal, hA_le_B, hBindex, QH1c, QH1, QClam,
      QH1CH1, hsemi, hprod, eH1, eClam, hIeq, hθnotMF, hθfinalIrr,
      hθorbit⟩
  letI : B.Normal := hBnormal
  letI : A.Normal := hAnormal
  letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
  let Q : Type u := B ⧸ A.subgroupOf B
  letI : Group Q := inferInstance
  let ψlin : Fin (p - 1) × Lam → Q →* ℂˣ := fun k =>
    semidirectProductOfInternalDirectProductLinearCharacter_sec9
      hsemi hprod
      (((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1.comp
        eH1.toMonoidHom)
      (k.2.comp eClam.toMonoidHom)
  refine ⟨B, hBnormal, hAnormal, hA_le_B, hBindex, ψlin, ?_, ?_, ?_, ?_⟩
  · exact hIeq
  · exact hθnotMF
  · exact hθfinalIrr
  · exact hθorbit

private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_of_quotient_linear_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq →
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  intro hquotData
  classical
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_sec9]
    at hquotData
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_sec9]
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  rcases hquotData with
    ⟨B, hBnormal, hAnormal, hA_le_B, hBindex, ψlin, hIeq,
      hθnotMF, hθfinalIrr, hθorbit⟩
  letI : B.Normal := hBnormal
  letI : A.Normal := hAnormal
  letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
  refine
    ⟨B, hBnormal, hAnormal, hA_le_B, hBindex,
      (fun k => Section1.quotientCharacterInflation A B (ψlin k)), ?_, ?_, ?_, ?_⟩
  · intro k
    exact
      ⟨Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
          A B (ψlin k),
        hIeq k,
        Section1.subgroupInKernel'_quotientCharacterInflation A B (ψlin k),
        Section1.quotientCharacterInflation_degree A B (ψlin k)⟩
  · intro k
    exact hθnotMF k
  · intro k
    exact hθfinalIrr k
  · intro k l
    exact hθorbit k l

private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_of_semidirect_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq →
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  intro hsemiData
  classical
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_sec9]
    at hsemiData
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_sec9]
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  rcases hsemiData with
    ⟨B, hBnormal, hAnormal, hA_le_B, hBindex, ψraw, hψdata,
      hθnotMF, hθfinalIrr, hθorbit⟩
  letI : B.Normal := hBnormal
  letI : A.Normal := hAnormal
  refine ⟨fun k => Section1.inducedCF B (ψraw k), ?_, ?_⟩
  · intro k
    rcases hψdata k with ⟨hψirr, hIeq, hψker, hψdegree⟩
    have hθirr :
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.inducedCF B (ψraw k)) :=
      inducedCF_isIrreducible_of_inertia_eq_self_sec9 B hψirr hIeq
    have hθker :
        Section1.subgroupInKernel' (Section1.inducedCF B (ψraw k)) A :=
      subgroupInKernel'_inducedCF_of_subgroupInKernel'_sec9
        B A hA_le_B hψirr hψker
    have hθdegree :
        Section1.degree (Section1.inducedCF B (ψraw k)) = (a : ℂ) := by
      rw [Section1.degree_inducedClassFunction, hψdegree, hBindex]
      simp
    exact ⟨hθirr, hθnotMF k, hθker, hθdegree, hθfinalIrr k⟩
  · intro k l
    exact hθorbit k l

private def
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_right_factor_quotient_bridge_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype)
    (B : Subgroup ((ambientDerivedSubgroup M).subgroupOf M))
    (eWBK :
      let W : Subgroup ((ambientDerivedSubgroup M).subgroupOf M) :=
        (U.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)
      let f : U →* ρBase.range :=
        ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
      let K : Subgroup U := f.ker
      ↥(W ⊓ B) ≃* K) : Prop := by
  classical
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let UprimeD : Subgroup Dm := (Uprime.subgroupOf M).subgroupOf Dm
  let WBUprime : Subgroup ↥(W ⊓ B) := UprimeD.subgroupOf (W ⊓ B)
  let e : ↥(W ⊓ B) ≃* K := eWBK
  let WBHsub : Subgroup ↥(W ⊓ B) := Hsub.comap e.toMonoidHom
  letI : WBHsub.Normal := (hUprimeNormal.subgroupOf K).comap e.toMonoidHom
  exact ∃ eWBHsub : (↥(W ⊓ B) ⧸ WBHsub) ≃* (K ⧸ Hsub),
    WBUprime = WBHsub ∧
      ∀ x : ↥(W ⊓ B),
        eWBHsub (QuotientGroup.mk' WBHsub x) =
          QuotientGroup.mk' Hsub (e x)

private theorem theorem_9_8_mem_right_of_mem_sup_inf_and_left_inf_eq_bot_sec9
    {L : Type u} [Group L]
    (H U W B MFD : Subgroup L)
    [H.Normal]
    (hH_le_MFD : H ≤ MFD)
    (hU_le_W : U ≤ W)
    (hU_le_B : U ≤ B)
    (hdisj : MFD ⊓ (W ⊓ B) = ⊥) :
    ∀ x : ↥(W ⊓ B), (x : L) ∈ H ⊔ U → (x : L) ∈ U := by
  intro x hx
  rcases (Subgroup.mem_sup_of_normal_left (s := H) (t := U) (x := (x : L))).1 hx with
    ⟨h, hh, u, hu, hhu⟩
  have huW : u ∈ W := hU_le_W hu
  have huB : u ∈ B := hU_le_B hu
  have hhB : h ∈ B := by
    have hxB : (x : L) ∈ B := x.property.2
    have hh_eq : h = (x : L) * u⁻¹ := by
      rw [← hhu]
      simp
    rw [hh_eq]
    exact B.mul_mem hxB (B.inv_mem huB)
  have hhWB : h ∈ W ⊓ B := by
    constructor
    · have hxW : (x : L) ∈ W := x.property.1
      have hh_eq : h = (x : L) * u⁻¹ := by
        rw [← hhu]
        simp
      rw [hh_eq]
      exact W.mul_mem hxW (W.inv_mem huW)
    · exact hhB
  have hhbot : h ∈ (⊥ : Subgroup L) := by
    have hhinf : h ∈ MFD ⊓ (W ⊓ B) := ⟨hH_le_MFD hh, hhWB⟩
    simpa [hdisj] using hhinf
  have hh_one : h = 1 := by
    simpa using hhbot
  have hx_eq_u : (x : L) = u := by
    simpa [hh_one] using hhu.symm
  simpa [hx_eq_u] using hu

private theorem theorem_9_8_mem_left_of_mem_sup_and_left_inf_right_eq_bot_sec9
    {L : Type u} [Group L]
    (H U MFD R : Subgroup L)
    [H.Normal]
    (hH_le_MFD : H ≤ MFD)
    (hU_le_R : U ≤ R)
    (hdisj : MFD ⊓ R = ⊥) :
    ∀ x : MFD, (x : L) ∈ H ⊔ U → (x : L) ∈ H := by
  intro x hx
  rcases (Subgroup.mem_sup_of_normal_left (s := H) (t := U) (x := (x : L))).1 hx with
    ⟨h, hh, u, hu, hhu⟩
  have huMFD : u ∈ MFD := by
    have hxMFD : (x : L) ∈ MFD := x.property
    have hu_eq : u = h⁻¹ * (x : L) := by
      rw [← hhu]
      simp
    rw [hu_eq]
    exact MFD.mul_mem (MFD.inv_mem (hH_le_MFD hh)) hxMFD
  have huR : u ∈ R := hU_le_R hu
  have hubot : u ∈ (⊥ : Subgroup L) := by
    have huinf : u ∈ MFD ⊓ R := ⟨huMFD, huR⟩
    simpa [hdisj] using huinf
  have hu_one : u = 1 := by
    simpa using hubot
  have hx_eq_h : (x : L) = h := by
    simpa [hu_one] using hhu.symm
  simpa [hx_eq_h] using hh

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 100000 in
private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_canonical_quotient_decomposition_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (_hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (_hρcycBase : IsCyclic ρBase.range)
    (_hρcardBase : Nat.card ρBase.range = a)
    (_hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (_hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (_hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype)
    (B : Subgroup ((ambientDerivedSubgroup M).subgroupOf M))
    (hBnormal : B.Normal)
    (hBsemi :
      Section2.IsInternalSemidirectProduct B
        ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M))
        (((U.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) ⊓ B))
    (hWBK :
      let W : Subgroup ((ambientDerivedSubgroup M).subgroupOf M) :=
        (U.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)
      let f : U →* ρBase.range :=
        ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
      let K : Subgroup U := f.ker
      ↥(W ⊓ B) ≃* K)
    (hWBK_compat :
      let W : Subgroup ((ambientDerivedSubgroup M).subgroupOf M) :=
        (U.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)
      let f : U →* ρBase.range :=
        ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
      let K : Subgroup U := f.ker
      ∀ x : ↥(W ⊓ B),
        (((hWBK x : K) : U) : G) =
          ((((x : (ambientDerivedSubgroup M).subgroupOf M) : M) : G)))
    (hWBKquot :
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_right_factor_quotient_bridge_data_sec9
        M MF U H0 C Uprime q H hqpos ρBase hUprimeEq B hWBK)
    (_hA_le_B :
      (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)) ≤ B)
    (_hBindex : Subgroup.index B = a)
    (hAnormal :
      (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)).Normal) :
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
    let f : U →* ρBase.range :=
      ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
    let K : Subgroup U := f.ker
    let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
      theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
        U Uprime hUprimeEq
    let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
    letI : Hsub.Normal := hUprimeNormal.subgroupOf K
    let Clam : Type u := K ⧸ Hsub
    letI : Group Clam := inferInstance
    let hAnormalA : A.Normal := by simpa [Dm, A] using hAnormal
    letI : B.Normal := hBnormal
    letI : A.Normal := hAnormalA
    letI : (A.subgroupOf B).Normal := hAnormalA.subgroupOf B
    let Q : Type u := B ⧸ A.subgroupOf B
    letI : Group Q := inferInstance
    let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
    let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
    let MFDsubB : Subgroup B := MFD.subgroupOf B
    ∃ QH1c : Subgroup Q,
    ∃ QH1 : Subgroup Q,
    ∃ QClam : Subgroup Q,
    ∃ QH1CH1 : Subgroup Q,
    ∃ _hsemi : Section2.IsInternalSemidirectProduct
        (⊤ : Subgroup Q) QH1c QH1CH1,
        ∃ _hprod : Section2.IsInternalDirectProduct QH1CH1 QH1 QClam,
        ∃ eH1 : QH1 ≃* H ⟨0, hqpos⟩,
        ∃ eClam : QClam ≃* Clam,
        (∀ m : MFDsubB,
          ∀ hmH1 :
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
              H ⟨0, hqpos⟩,
            ∃ hmQH1 : QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1,
              eH1
                  ⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ =
                ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                    (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                      ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)),
                  hmH1⟩) ∧
        (∀ m : MFDsubB,
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
            (⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i) →
          QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1c) ∧
        (∀ w : (W ⊓ B).subgroupOf B,
          ∃ hwQClam : QuotientGroup.mk' (A.subgroupOf B) w ∈ QClam,
            eClam
                ⟨QuotientGroup.mk' (A.subgroupOf B) w, hwQClam⟩ =
              QuotientGroup.mk' Hsub
                (hWBK
                  (⟨((w : B) : Dm), by
                    simpa [W, Subgroup.mem_subgroupOf] using w.property⟩ :
                    ↥(W ⊓ B)))) ∧
        ∃ QMF : Subgroup Q,
          QMF =
              ((MFD.subgroupOf B).map (QuotientGroup.mk' (A.subgroupOf B))) ∧
          Section2.IsInternalDirectProduct QMF QH1c QH1 ∧
          QH1 ≤ QMF := by
  -- `H1c ><| H1CH1` and `H1 \x Clam` quotient product decompositions.
  classical
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  have hAnormalA : A.Normal := by
    simpa [Dm, A] using hAnormal
  letI : B.Normal := hBnormal
  letI : A.Normal := hAnormalA
  letI : (A.subgroupOf B).Normal := hAnormalA.subgroupOf B
  let Q : Type u := B ⧸ A.subgroupOf B
  letI : Group Q := inferInstance
  let qB : B →* Q := QuotientGroup.mk' (A.subgroupOf B)
  let WB : Subgroup Dm := W ⊓ B
  let WBsubB : Subgroup B := WB.subgroupOf B
  let H0D : Subgroup Dm := (H0.subgroupOf M).subgroupOf Dm
  let UprimeD : Subgroup Dm := (Uprime.subgroupOf M).subgroupOf Dm
  let WBUprime : Subgroup WB := UprimeD.subgroupOf WB
  let WBHsub : Subgroup WB := Hsub.comap hWBK.toMonoidHom
  have hWBK_compat' :
      ∀ x : WB,
        (((hWBK x : K) : U) : G) = ((((x : WB) : Dm) : M) : G) := by
    simpa [Dm, W, f, K, WB] using hWBK_compat
  have hWB_centralizes_base :
      ∀ x : WB,
        quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩)
          ((((x : WB) : Dm) : M) : G) := by
    intro x
    let uK : K := hWBK x
    have hρ :
        ρBase (QuotientGroup.mk' (C.subgroupOf U) (uK : U)) = 1 := by
      have huK : f (uK : U) = 1 := uK.property
      simpa [f] using congrArg (fun y : ρBase.range => (y : MulAut (H ⟨0, hqpos⟩))) huK
    have hcent :
        quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) ((uK : U) : G) :=
      (hρkerBase (QuotientGroup.mk' (C.subgroupOf U) (uK : U))).mp hρ (uK : U) rfl
    simpa [uK, hWBK_compat' x] using hcent
  have hWBKquot' :
      ∃ eWBHsub : (WB ⧸ WBHsub) ≃* Clam,
        WBUprime = WBHsub ∧
          ∀ x : WB,
            eWBHsub (QuotientGroup.mk' WBHsub x) =
              QuotientGroup.mk' Hsub (hWBK x) := by
    dsimp
      [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_right_factor_quotient_bridge_data_sec9]
      at hWBKquot
    simpa [Dm, W, f, K, Hsub, Clam, WB, UprimeD, WBUprime, WBHsub]
      using hWBKquot
  rcases hWBKquot' with ⟨eWBHsub, hWBUprime_eq, hWBHsub_apply⟩
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hhallD, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hFittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hH0M : H0 ≤ M := (hH0MF.trans hMFleD).trans
    (section12_ambientDerivedSubgroup_le (E := M))
  have hUprimeU : Uprime ≤ U := by
    rw [hUprimeEq, Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_le_self U
  have hUprimeM : Uprime ≤ M := (hUprimeU.trans hUleD).trans
    (section12_ambientDerivedSubgroup_le (E := M))
  have hH0subD : H0.subgroupOf M ≤ Dm := by
    intro x hx
    have hxH0 : ((x : M) : G) ∈ H0 := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact hMFleD (hH0MF hxH0)
  have hUprimeSubD : Uprime.subgroupOf M ≤ Dm := by
    intro x hx
    have hxUprime : ((x : M) : G) ∈ Uprime := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact hUleD (hUprimeU hxUprime)
  have hA_sup :
      A = H0D ⊔ UprimeD := by
    dsimp [A, H0D, UprimeD, Dm]
    rw [Subgroup.subgroupOf_sup (A := H0) (A' := Uprime) (B := M)
      hH0M hUprimeM]
    exact Subgroup.subgroupOf_sup (A := H0.subgroupOf M)
      (A' := Uprime.subgroupOf M) (B := Dm) hH0subD hUprimeSubD
  have hH0D_le_MFD : H0D ≤ ((MF.subgroupOf M).subgroupOf Dm) := by
    intro x hx
    have hxH0 : (((x : Dm) : M) : G) ∈ H0 := by
      simpa [H0D, Subgroup.mem_subgroupOf] using hx
    exact hH0MF hxH0
  have hH0Dnormal : H0D.Normal := by
    simpa [H0D] using
      (case_9_7_a_H0_normal_M_sec9 hcase).subgroupOf Dm
  have hUprimeD_le_W : UprimeD ≤ W := by
    intro x hx
    have hxUprime : (((x : Dm) : M) : G) ∈ Uprime := by
      simpa [UprimeD, Subgroup.mem_subgroupOf] using hx
    exact hUprimeU hxUprime
  have hUprimeD_le_B : UprimeD ≤ B := by
    intro x hx
    have hxA : (x : Dm) ∈ A := by
      rw [hA_sup]
      exact Subgroup.mem_sup_right hx
    exact _hA_le_B hxA
  have hUprimeD_le_WB : UprimeD ≤ WB := by
    intro x hx
    exact ⟨hUprimeD_le_W hx, hUprimeD_le_B hx⟩
  have hA_of_WB_le_UprimeD :
      ∀ x : WB, ((x : Dm) ∈ A) → (x : Dm) ∈ UprimeD := by
    intro x hxA
    letI : H0D.Normal := hH0Dnormal
    exact
      theorem_9_8_mem_right_of_mem_sup_inf_and_left_inf_eq_bot_sec9
        H0D UprimeD W B ((MF.subgroupOf M).subgroupOf Dm)
        hH0D_le_MFD hUprimeD_le_W hUprimeD_le_B hBsemi.inf_eq_bot x
        (by simpa [hA_sup] using hxA)
  let QClam : Subgroup Q := WBsubB.map qB
  let hQClam_equiv : QClam ≃* Clam := by
    let eWBsub : WBsubB ≃* WB := Subgroup.subgroupOfEquivOfLe inf_le_right
    let Nsub : Subgroup WBsubB := (A.subgroupOf B).subgroupOf WBsubB
    have hNsubNormal : Nsub.Normal := by
      exact (hAnormalA.subgroupOf B).subgroupOf WBsubB
    letI : Nsub.Normal := hNsubNormal
    have hNmap : Nsub.map eWBsub.toMonoidHom = WBUprime := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hyN, hyx⟩
        have hyA : ((y : WBsubB) : B) ∈ A.subgroupOf B := by
          simpa [Nsub, Subgroup.mem_subgroupOf] using hyN
        have hyA_Dm : (((y : WBsubB) : B) : Dm) ∈ A := by
          simpa [Subgroup.mem_subgroupOf] using hyA
        have hxA : (x : Dm) ∈ A := by
          have hval := congrArg (fun z : WB => (z : Dm)) hyx
          have hyA_image : ((eWBsub y : WB) : Dm) ∈ A := by
            simpa [eWBsub, Subgroup.subgroupOfEquivOfLe] using hyA_Dm
          have hval' : ((eWBsub y : WB) : Dm) = (x : Dm) := by
            simpa using hval
          rw [hval'] at hyA_image
          exact hyA_image
        exact hA_of_WB_le_UprimeD x hxA
      · intro hx
        let yB : B := ⟨(x : Dm), x.property.2⟩
        have hyWBsub : yB ∈ WBsubB := by
          simpa [WBsubB, WB, Subgroup.mem_subgroupOf, yB] using x.property.1
        let y : WBsubB := ⟨yB, hyWBsub⟩
        refine ⟨y, ?_, ?_⟩
        · have hxA : (x : Dm) ∈ A := by
            rw [hA_sup]
            exact Subgroup.mem_sup_right hx
          change (y : B) ∈ A.subgroupOf B
          simpa [Subgroup.mem_subgroupOf, y, yB] using hxA
        · apply Subtype.ext
          rfl
    haveI : WBUprime.Normal := by
      rw [hWBUprime_eq]
      exact (hUprimeNormal.subgroupOf K).comap hWBK.toMonoidHom
    let eWBUprime : (WB ⧸ WBUprime) ≃* Clam :=
      (QuotientGroup.quotientMulEquivOfEq hWBUprime_eq).trans eWBHsub
    let eQuot : (WBsubB ⧸ Nsub) ≃* (WB ⧸ WBUprime) :=
      QuotientGroup.congr Nsub WBUprime eWBsub hNmap
    exact
      (quotientSubgroupRangeEquiv WBsubB (A.subgroupOf B)).symm.trans
        (eQuot.trans eWBUprime)
  have hQClam_equiv_apply_mk :
      ∀ w : WBsubB,
        hQClam_equiv ⟨qB w, ⟨w, w.property, rfl⟩⟩ =
          QuotientGroup.mk' Hsub
            (hWBK
              (⟨((w : B) : Dm), by
                simpa [WBsubB, WB, Subgroup.mem_subgroupOf] using w.property⟩ : WB)) := by
    intro w
    let wWB : WB :=
      ⟨((w : B) : Dm), by
        simpa [WBsubB, WB, Subgroup.mem_subgroupOf] using w.property⟩
    let Nsub : Subgroup WBsubB := (A.subgroupOf B).subgroupOf WBsubB
    have hRange :
        (quotientSubgroupRangeEquiv WBsubB (A.subgroupOf B))
            (QuotientGroup.mk' Nsub w) =
          ⟨qB w, ⟨w, w.property, rfl⟩⟩ := by
      apply Subtype.ext
      change
        ((quotientSubgroupRangeEquiv WBsubB (A.subgroupOf B))
            (QuotientGroup.mk' ((A.subgroupOf B).subgroupOf WBsubB) w) :
          B ⧸ A.subgroupOf B) =
            QuotientGroup.mk' (A.subgroupOf B) (w : B)
      exact quotientSubgroupRangeEquiv_apply_mk WBsubB (A.subgroupOf B) w
    have hRange_symm :
        (quotientSubgroupRangeEquiv WBsubB (A.subgroupOf B)).symm
            ⟨qB w, ⟨w, w.property, rfl⟩⟩ =
          QuotientGroup.mk' Nsub w := by
      rw [← hRange]
      simp
    have heWBsub :
        (Subgroup.subgroupOfEquivOfLe inf_le_right : WBsubB ≃* WB) w = wWB := by
      apply Subtype.ext
      rfl
    simpa [hQClam_equiv, hRange_symm, wWB, Nsub, heWBsub] using hWBHsub_apply wWB
  let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
  let MFDsubB : Subgroup B := MFD.subgroupOf B
  let QMF : Subgroup Q := MFDsubB.map qB
  have hMFDsubD : MF.subgroupOf M ≤ Dm := by
    intro x hx
    have hxMF : ((x : M) : G) ∈ MF := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact hMFleD hxMF
  let eMFD : MFD ≃* MF :=
    (Subgroup.subgroupOfEquivOfLe (H := MF.subgroupOf M) (K := Dm) hMFDsubD).trans
      (Subgroup.subgroupOfEquivOfLe (H := MF) (K := M)
        (hMFleD.trans (section12_ambientDerivedSubgroup_le (E := M))))
  have hH0D_le_MFD : H0D ≤ MFD := by
    intro x hx
    have hxH0 : (((x : Dm) : M) : G) ∈ H0 := by
      simpa [H0D, Subgroup.mem_subgroupOf] using hx
    exact hH0MF hxH0
  let H0DsubMFD : Subgroup MFD := H0D.subgroupOf MFD
  haveI : H0DsubMFD.Normal := hH0Dnormal.subgroupOf MFD
  have hMFD_kernel_map : H0DsubMFD.map eMFD.toMonoidHom = H0.subgroupOf MF := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hyx⟩
      have hyH0D : (y : Dm) ∈ H0D := by
        simpa [H0DsubMFD, Subgroup.mem_subgroupOf] using hy
      have hyH0 : (((y : Dm) : M) : G) ∈ H0 := by
        simpa [H0D, Subgroup.mem_subgroupOf] using hyH0D
      have hval : ((eMFD y : MF) : G) = ((y : Dm) : G) := by
        rfl
      have hxval : (x : G) = ((y : Dm) : G) := by
        rw [← hval]
        exact congrArg (fun z : MF => (z : G)) hyx.symm
      simpa [Subgroup.mem_subgroupOf, hxval] using hyH0
    · intro hx
      let yM : M := ⟨(x : G),
        (hMFleD.trans (section12_ambientDerivedSubgroup_le (E := M))) x.property⟩
      have hyDmem : yM ∈ Dm := hMFDsubD (by
        simp [Subgroup.mem_subgroupOf, yM])
      let yD : Dm := ⟨yM, hyDmem⟩
      have hyMFDmem : yD ∈ MFD := by
        simp [MFD, Subgroup.mem_subgroupOf, yD, yM]
      let y : MFD := ⟨yD, hyMFDmem⟩
      refine ⟨y, ?_, ?_⟩
      · have hxH0 : (x : G) ∈ H0 := by
          simpa [Subgroup.mem_subgroupOf] using hx
        change (y : Dm) ∈ H0D
        simpa [H0D, Subgroup.mem_subgroupOf, y, yD, yM] using hxH0
      · apply Subtype.ext
        rfl
  let NMFsub : Subgroup MFDsubB := (A.subgroupOf B).subgroupOf MFDsubB
  have hNMFsubNormal : NMFsub.Normal := by
    exact (hAnormalA.subgroupOf B).subgroupOf MFDsubB
  letI : NMFsub.Normal := hNMFsubNormal
  let eMFDsub : MFDsubB ≃* MFD := Subgroup.subgroupOfEquivOfLe hBsemi.left_le
  have hNMF_map : NMFsub.map eMFDsub.toMonoidHom = H0DsubMFD := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyN, hyx⟩
      have hyA : ((y : MFDsubB) : B) ∈ A.subgroupOf B := by
        simpa [NMFsub, Subgroup.mem_subgroupOf] using hyN
      have hyA_Dm : (((y : MFDsubB) : B) : Dm) ∈ A := by
        simpa [Subgroup.mem_subgroupOf] using hyA
      have hxA : (x : Dm) ∈ A := by
        have hval := congrArg (fun z : MFD => (z : Dm)) hyx
        have hyA_image : ((eMFDsub y : MFD) : Dm) ∈ A := by
          simpa [eMFDsub, Subgroup.subgroupOfEquivOfLe] using hyA_Dm
        have hval' : ((eMFDsub y : MFD) : Dm) = (x : Dm) := by
          simpa using hval
        rw [hval'] at hyA_image
        exact hyA_image
      have hxH0D : (x : Dm) ∈ H0D := by
        letI : H0D.Normal := hH0Dnormal
        exact
          theorem_9_8_mem_left_of_mem_sup_and_left_inf_right_eq_bot_sec9
            H0D UprimeD MFD WB hH0D_le_MFD hUprimeD_le_WB
            hBsemi.inf_eq_bot x (by simpa [hA_sup] using hxA)
      simpa [H0DsubMFD, Subgroup.mem_subgroupOf] using hxH0D
    · intro hx
      let yB : B := ⟨(x : Dm), hBsemi.left_le x.property⟩
      have hyMFDsub : yB ∈ MFDsubB := by
        simp [MFDsubB, MFD, Subgroup.mem_subgroupOf, yB]
      let y : MFDsubB := ⟨yB, hyMFDsub⟩
      refine ⟨y, ?_, ?_⟩
      · have hxH0D : (x : Dm) ∈ H0D := by
          simpa [H0DsubMFD, Subgroup.mem_subgroupOf] using hx
        have hxA : (x : Dm) ∈ A := by
          rw [hA_sup]
          exact Subgroup.mem_sup_left hxH0D
        change (y : B) ∈ A.subgroupOf B
        simpa [Subgroup.mem_subgroupOf, y, yB] using hxA
      · apply Subtype.ext
        rfl
  let eMFDquot : (MFD ⧸ H0DsubMFD) ≃* (MF ⧸ H0.subgroupOf MF) :=
    QuotientGroup.congr H0DsubMFD (H0.subgroupOf MF) eMFD hMFD_kernel_map
  let eQuot : (MFDsubB ⧸ NMFsub) ≃* (MFD ⧸ H0DsubMFD) :=
    QuotientGroup.congr NMFsub H0DsubMFD eMFDsub hNMF_map
  let eRangeMFD : (MFDsubB ⧸ NMFsub) ≃* QMF :=
    quotientSubgroupRangeEquiv MFDsubB (A.subgroupOf B)
  let hQMF_equiv : QMF ≃* (MF ⧸ H0.subgroupOf MF) :=
    eRangeMFD.symm.trans (eQuot.trans eMFDquot)
  let QH1sub : Subgroup QMF := (H ⟨0, hqpos⟩).comap hQMF_equiv.toMonoidHom
  let QH1 : Subgroup Q := QH1sub.map QMF.subtype
  let hQH1sub_equiv : QH1sub ≃* H ⟨0, hqpos⟩ := by
    let φ : QH1sub →* H ⟨0, hqpos⟩ :=
      { toFun := fun x => ⟨hQMF_equiv (x : QMF), x.property⟩
        map_one' := by
          ext
          simp
        map_mul' := by
          intro x y
          ext
          simp }
    have hφ_inj : Function.Injective φ := by
      intro x y hxy
      apply Subtype.ext
      apply hQMF_equiv.injective
      exact congrArg (fun z : H ⟨0, hqpos⟩ => (z : MF ⧸ H0.subgroupOf MF)) hxy
    have hφ_surj : Function.Surjective φ := by
      intro x
      let yQMF : QMF := hQMF_equiv.symm (x : MF ⧸ H0.subgroupOf MF)
      have hyQH1 : yQMF ∈ QH1sub := by
        change hQMF_equiv yQMF ∈ H ⟨0, hqpos⟩
        simp [yQMF]
      refine ⟨⟨yQMF, hyQH1⟩, ?_⟩
      ext
      change hQMF_equiv yQMF = (x : MF ⧸ H0.subgroupOf MF)
      simp [yQMF]
    exact MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  let hQH1_range_equiv : QH1sub ≃* QH1 := by
    let φ : QH1sub →* QH1 :=
      { toFun := fun x => ⟨((x : QH1sub) : QMF), ⟨(x : QH1sub), x.property, rfl⟩⟩
        map_one' := by
          ext
          rfl
        map_mul' := by
          intro x y
          ext
          rfl }
    have hφ_inj : Function.Injective φ := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : QH1 => (z : Q)) hxy
    have hφ_surj : Function.Surjective φ := by
      intro x
      rcases x.property with ⟨y, hy, hyx⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      apply Subtype.ext
      exact hyx
    exact MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  let hQH1_equiv : QH1 ≃* H ⟨0, hqpos⟩ :=
    hQH1_range_equiv.symm.trans hQH1sub_equiv
  let H1cMF : Subgroup (MF ⧸ H0.subgroupOf MF) :=
    ⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i
  have hMF_Hsplit :
      Section2.IsInternalDirectProduct
        (⊤ : Subgroup (MF ⧸ H0.subgroupOf MF)) H1cMF (H ⟨0, hqpos⟩) := by
    simpa [H1cMF] using
      theorem_9_8_iSup_split_base_internalDirectProduct_sec9
        H ⟨0, hqpos⟩ hHindep hHsup
  let QH1csub : Subgroup QMF := H1cMF.comap hQMF_equiv.toMonoidHom
  have hQMF_split :
      Section2.IsInternalDirectProduct (⊤ : Subgroup QMF) QH1csub QH1sub := by
    simpa [QH1csub, QH1sub] using
      internalDirectProduct_comap_mulEquiv_top_sec9 hQMF_equiv hMF_Hsplit
  let QH1c : Subgroup Q := QH1csub.map QMF.subtype
  have hQMF_split_in_Q :
      Section2.IsInternalDirectProduct QMF QH1c QH1 := by
    simpa [QH1c, QH1] using
      internalDirectProduct_map_subtype_top_sec9 hQMF_split
  have hQMF_equiv_apply_mk :
      ∀ m : MFDsubB,
        hQMF_equiv ⟨qB m, ⟨m, m.property, rfl⟩⟩ =
          QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m)) := by
    intro m
    have hRange :
        eRangeMFD (QuotientGroup.mk' NMFsub m) =
          ⟨qB m, ⟨m, m.property, rfl⟩⟩ := by
      apply Subtype.ext
      change
        ((quotientSubgroupRangeEquiv MFDsubB (A.subgroupOf B))
            (QuotientGroup.mk' ((A.subgroupOf B).subgroupOf MFDsubB) m) :
          B ⧸ A.subgroupOf B) =
            QuotientGroup.mk' (A.subgroupOf B) (m : B)
      exact quotientSubgroupRangeEquiv_apply_mk MFDsubB (A.subgroupOf B) m
    have hRange_symm :
        eRangeMFD.symm ⟨qB m, ⟨m, m.property, rfl⟩⟩ =
          QuotientGroup.mk' NMFsub m := by
      rw [← hRange]
      simp
    simp [hQMF_equiv, hRange_symm, eQuot, eMFDquot]
  have hQH1_equiv_apply_mk :
      ∀ (m : MFDsubB)
        (hmH1 :
          QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m)) ∈
            H ⟨0, hqpos⟩),
        ∃ hmQH1 : QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1,
          hQH1_equiv ⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ =
            ⟨QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m)),
              hmH1⟩ := by
    intro m hmH1
    let qm : QMF := ⟨qB m, ⟨m, m.property, rfl⟩⟩
    have hqmH1sub : qm ∈ QH1sub := by
      change hQMF_equiv qm ∈ H ⟨0, hqpos⟩
      simpa [qm, hQMF_equiv_apply_mk m] using hmH1
    let ysub : QH1sub := ⟨qm, hqmH1sub⟩
    have hQH1_image_val :
        ((hQH1_range_equiv ysub : QH1) : Q) =
          QuotientGroup.mk' (A.subgroupOf B) m := by
      simp [hQH1_range_equiv, ysub, qm, qB]
      rfl
    let hmQH1 : QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1 := by
      simp [← hQH1_image_val]
    refine ⟨hmQH1, ?_⟩
    have hQH1_image :
        (⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ : QH1) =
          hQH1_range_equiv ysub := by
      apply Subtype.ext
      exact hQH1_image_val.symm
    calc
      hQH1_equiv ⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ =
          hQH1_equiv (hQH1_range_equiv ysub) := by
        rw [hQH1_image]
      _ =
          hQH1sub_equiv ysub := by
        simp [hQH1_equiv]
      _ = ⟨QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m)),
            hmH1⟩ := by
        apply Subtype.ext
        simpa [hQH1sub_equiv, ysub, qm] using hQMF_equiv_apply_mk m
  have hQH1c_apply_mk :
      ∀ (m : MFDsubB)
        (hmH1c :
          QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m)) ∈ H1cMF),
        QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1c := by
    intro m hmH1c
    let qm : QMF := ⟨qB m, ⟨m, m.property, rfl⟩⟩
    have hqmH1csub : qm ∈ QH1csub := by
      change hQMF_equiv qm ∈ H1cMF
      simpa [qm, hQMF_equiv_apply_mk m] using hmH1c
    change qB m ∈ QH1c
    exact ⟨qm, hqmH1csub, rfl⟩
  have hH1cMF_norm_U : quotientSubgroupNormalizedBy MF H0 U H1cMF := by
    intro aU
    rcases hHnorm ⟨0, hqpos⟩ aU with ⟨hconjMF, action, haction, _hmapBase⟩
    refine ⟨hconjMF, action, haction, ?_⟩
    have hmap_each :
        ∀ i : Fin q, (H i).map action.toMonoidHom = H i := by
      intro i
      rcases hHnorm i aU with ⟨hconjMF_i, action_i, haction_i, hmap_i⟩
      have haction_eq : action_i = action := by
        ext x
        rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨h, rfl⟩
        calc
          action_i (QuotientGroup.mk' (H0.subgroupOf MF) h) =
              QuotientGroup.mk' (H0.subgroupOf MF)
                ⟨(aU : G)⁻¹ * (h : G) * (aU : G), hconjMF_i h⟩ := haction_i h
          _ = QuotientGroup.mk' (H0.subgroupOf MF)
                ⟨(aU : G)⁻¹ * (h : G) * (aU : G), hconjMF h⟩ := by
                congr 1
          _ = action (QuotientGroup.mk' (H0.subgroupOf MF) h) := (haction h).symm
      simpa [haction_eq] using hmap_i.symm
    have hmap_sup : H1cMF.map action.toMonoidHom = H1cMF := by
      simp_rw [H1cMF, Subgroup.map_iSup, hmap_each]
    exact hmap_sup.symm
  let QH1CH1 : Subgroup Q := QH1 ⊔ QClam
  have hQH1_QClam_commute :
      ∀ h ∈ QH1, ∀ k ∈ QClam, h * k = k * h := by
    intro h hh k hk
    rcases hh with ⟨y, hyQH1sub, hyh⟩
    rcases y.property with ⟨m, hmMFDsub, hmy⟩
    rcases hk with ⟨w, hwWBsub, hwk⟩
    let mSub : MFDsubB := ⟨m, hmMFDsub⟩
    let mMF : MF := eMFD (eMFDsub mSub)
    have hmHbase :
        QuotientGroup.mk' (H0.subgroupOf MF) mMF ∈ H ⟨0, hqpos⟩ := by
      have hybase : hQMF_equiv y ∈ H ⟨0, hqpos⟩ := by
        simpa [QH1sub] using hyQH1sub
      have hy_eq :
          y = ⟨qB mSub, ⟨mSub, mSub.property, rfl⟩⟩ := by
        apply Subtype.ext
        simpa [mSub] using hmy.symm
      rw [hy_eq] at hybase
      simpa [mMF, hQMF_equiv_apply_mk mSub] using hybase
    have hmMFD : (m : Dm) ∈ MFD := by
      simpa [MFDsubB, Subgroup.mem_subgroupOf] using hmMFDsub
    have hwWB : (w : Dm) ∈ WB := by
      simpa [WBsubB, Subgroup.mem_subgroupOf] using hwWBsub
    let wWB : WB := ⟨(w : Dm), hwWB⟩
    rcases hWB_centralizes_base wWB with ⟨hconjMF, action, haction, hfix⟩
    have hfix_mk :
        QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨((((wWB : WB) : Dm) : M) : G)⁻¹ * (mMF : G) *
                ((((wWB : WB) : Dm) : M) : G), hconjMF mMF⟩ =
          QuotientGroup.mk' (H0.subgroupOf MF) mMF := by
      calc
        QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨((((wWB : WB) : Dm) : M) : G)⁻¹ * (mMF : G) *
                ((((wWB : WB) : Dm) : M) : G), hconjMF mMF⟩ =
            action (QuotientGroup.mk' (H0.subgroupOf MF) mMF) := by
              exact (haction mMF).symm
        _ = QuotientGroup.mk' (H0.subgroupOf MF) mMF :=
              hfix (QuotientGroup.mk' (H0.subgroupOf MF) mMF) hmHbase
    have hdeltaH0 :
        (⟨((((wWB : WB) : Dm) : M) : G)⁻¹ * (mMF : G) *
            ((((wWB : WB) : Dm) : M) : G), hconjMF mMF⟩ / mMF : MF) ∈
          H0.subgroupOf MF :=
      QuotientGroup.eq_iff_div_mem.mp hfix_mk
    have hconjMFD :
        (w : Dm)⁻¹ * (m : Dm) * (w : Dm) ∈ MFD := by
      simpa [Section2.conjBy, mul_assoc] using
        hBsemi.right_normalizes_left ((w : Dm)⁻¹) (WB.inv_mem hwWB)
          (m : Dm) hmMFD
    let conjB : B :=
      ⟨(w : Dm)⁻¹ * (m : Dm) * (w : Dm), hBsemi.left_le hconjMFD⟩
    have hdeltaH0D : ((conjB / m : B) : Dm) ∈ H0D := by
      have hdeltaH0G :
          (((⟨((((wWB : WB) : Dm) : M) : G)⁻¹ * (mMF : G) *
              ((((wWB : WB) : Dm) : M) : G), hconjMF mMF⟩ / mMF : MF) : G)) ∈
            H0 := by
        simpa [Subgroup.mem_subgroupOf] using hdeltaH0
      simpa [H0D, Subgroup.mem_subgroupOf, conjB, mMF, mSub, wWB, eMFD,
        eMFDsub, Subgroup.subgroupOfEquivOfLe, div_eq_mul_inv, mul_assoc] using hdeltaH0G
    have hconj_eq_m : qB conjB = qB m := by
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hdeltaA : ((conjB / m : B) : Dm) ∈ A := by
        rw [hA_sup]
        exact Subgroup.mem_sup_left hdeltaH0D
      simpa [Subgroup.mem_subgroupOf] using hdeltaA
    have hconjB_eq : conjB = w⁻¹ * m * w := by
      apply Subtype.ext
      rfl
    have hconjQ :
        (qB w)⁻¹ * qB m * qB w = qB m := by
      calc
        (qB w)⁻¹ * qB m * qB w = qB (w⁻¹ * m * w) := by
          simp [map_mul, map_inv, mul_assoc]
        _ = qB conjB := by rw [← hconjB_eq]
        _ = qB m := hconj_eq_m
    have hcomm_mw : qB m * qB w = qB w * qB m := by
      have hleft := congrArg (fun z : Q => qB w * z) hconjQ
      simpa [mul_assoc] using hleft
    rw [← hyh, ← hwk]
    change (y : Q) * qB w = qB w * (y : Q)
    rw [← hmy]
    exact hcomm_mw
  have hQMF_inf_QClam : QMF ⊓ QClam = ⊥ := by
    apply le_antisymm
    · intro x hx
      rcases hx.1 with ⟨m, hmMFDsub, hmx⟩
      rcases hx.2 with ⟨w, hwWBsub, hwx⟩
      have hmwA_B : m / w ∈ A.subgroupOf B := by
        exact QuotientGroup.eq_iff_div_mem.mp (hmx.trans hwx.symm)
      letI : H0D.Normal := hH0Dnormal
      have hmwA_D : ((m / w : B) : Dm) ∈ A := by
        simpa [Subgroup.mem_subgroupOf] using hmwA_B
      have hmwSup : ((m / w : B) : Dm) ∈ H0D ⊔ UprimeD := by
        simpa [hA_sup] using hmwA_D
      rcases (Subgroup.mem_sup_of_normal_left
          (s := H0D) (t := UprimeD) (x := ((m / w : B) : Dm))).1
          hmwSup with
        ⟨h0, hh0, u0, hu0, hprod0⟩
      have hmMFD : (m : Dm) ∈ MFD := by
        simpa [MFDsubB, Subgroup.mem_subgroupOf] using hmMFDsub
      have hwWB : (w : Dm) ∈ WB := by
        simpa [WBsubB, Subgroup.mem_subgroupOf] using hwWBsub
      have hmul :
          (m : Dm) * (w : Dm)⁻¹ = h0 * u0 := by
        simpa [div_eq_mul_inv] using hprod0.symm
      have huniq :=
        internalSemidirectProduct_mul_unique_sec9 hBsemi
          hmMFD (hH0D_le_MFD hh0) (WB.inv_mem hwWB) (hUprimeD_le_WB hu0) hmul
      have hmA_D : (m : Dm) ∈ A := by
        rw [huniq.1]
        rw [hA_sup]
        exact Subgroup.mem_sup_left hh0
      have hmA_B' : m ∈ A.subgroupOf B := by
        simpa [Subgroup.mem_subgroupOf] using hmA_D
      have hq_m_one : qB m = 1 :=
        (QuotientGroup.eq_one_iff (N := A.subgroupOf B) (x := m)).2 hmA_B'
      have hx_one : x = 1 := by
        rw [← hmx, hq_m_one]
      simp [hx_one]
    · exact bot_le
  have hQH1_le_QMF : QH1 ≤ QMF := by
    intro x hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hQH1_inf_QClam : QH1 ⊓ QClam = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxQMFClam : x ∈ QMF ⊓ QClam :=
        ⟨hQH1_le_QMF hx.1, hx.2⟩
      simpa [hQMF_inf_QClam] using hxQMFClam
    · exact bot_le
  have hprod : Section2.IsInternalDirectProduct QH1CH1 QH1 QClam := by
    simpa [QH1CH1] using
      internalDirectProduct_sup_of_commute_inf_eq_bot_sec9
        QH1 QClam hQH1_QClam_commute hQH1_inf_QClam
  have hsemiQMF :
      Section2.IsInternalSemidirectProduct (⊤ : Subgroup Q) QMF QClam := by
    refine
      { left_le := ?_
        right_le := ?_
        right_normalizes_left := ?_
        inf_eq_bot := hQMF_inf_QClam
        mul_surjective := ?_ }
    · intro x _hx
      trivial
    · intro x _hx
      trivial
    · intro k hk h hh
      rcases hk with ⟨w, hwWBsub, hwk⟩
      rcases hh with ⟨m, hmMFDsub, hmh⟩
      have hmMFD : (m : Dm) ∈ MFD := by
        simpa [MFDsubB, Subgroup.mem_subgroupOf] using hmMFDsub
      have hwWB : (w : Dm) ∈ WB := by
        simpa [WBsubB, Subgroup.mem_subgroupOf] using hwWBsub
      have hconjMFD : Section2.conjBy (w : Dm) (m : Dm) ∈ MFD := by
        exact hBsemi.right_normalizes_left (w : Dm) hwWB (m : Dm) hmMFD
      let conjB : B := ⟨Section2.conjBy (w : Dm) (m : Dm), hBsemi.left_le hconjMFD⟩
      have hconjB_MFDsub : conjB ∈ MFDsubB := by
        simpa [MFDsubB, Subgroup.mem_subgroupOf, conjB] using hconjMFD
      refine ⟨conjB, hconjB_MFDsub, ?_⟩
      rw [← hwk, ← hmh]
      have hconjB_eq : conjB = w * m * w⁻¹ := by
        apply Subtype.ext
        rfl
      rw [hconjB_eq]
      simp [Section2.conjBy, map_mul, map_inv, mul_assoc]
    · intro c _hc
      rcases QuotientGroup.mk'_surjective (A.subgroupOf B) c with ⟨b, rfl⟩
      rcases hBsemi.mul_surjective (b : Dm) b.property with
        ⟨m, hmMFD, w, hwWB, hbw⟩
      let mB : B := ⟨m, hBsemi.left_le hmMFD⟩
      let wB : B := ⟨w, hwWB.2⟩
      have hmB_MFDsub : mB ∈ MFDsubB := by
        change (m : Dm) ∈ MFD
        exact hmMFD
      have hwB_WBsub : wB ∈ WBsubB := by
        change (w : Dm) ∈ WB
        exact hwWB
      refine ⟨qB mB, ⟨mB, hmB_MFDsub, rfl⟩,
        qB wB, ⟨wB, hwB_WBsub, rfl⟩, ?_⟩
      have hb_eq : b = mB * wB := by
        apply Subtype.ext
        exact hbw
      rw [hb_eq]
      exact qB.map_mul mB wB
  have hQClam_normalizes_QH1c :
      ∀ k ∈ QClam, ∀ h ∈ QH1c, Section2.conjBy k h ∈ QH1c := by
    intro k hk h hh
    rcases hk with ⟨w, hwWBsub, hwk⟩
    rcases hh with ⟨y, hyQH1csub, hyh⟩
    rcases y.property with ⟨m, hmMFDsub, hmy⟩
    let mSub : MFDsubB := ⟨m, hmMFDsub⟩
    let mMF : MF := eMFD (eMFDsub mSub)
    have hmH1c :
        QuotientGroup.mk' (H0.subgroupOf MF) mMF ∈ H1cMF := by
      have hybase : hQMF_equiv y ∈ H1cMF := by
        simpa [QH1csub] using hyQH1csub
      have hy_eq :
          y = ⟨qB mSub, ⟨mSub, mSub.property, rfl⟩⟩ := by
        apply Subtype.ext
        simpa [mSub] using hmy.symm
      rw [hy_eq] at hybase
      simpa [mMF, hQMF_equiv_apply_mk mSub] using hybase
    have hmMFD : (m : Dm) ∈ MFD := by
      simpa [MFDsubB, Subgroup.mem_subgroupOf] using hmMFDsub
    have hwWB : (w : Dm) ∈ WB := by
      simpa [WBsubB, Subgroup.mem_subgroupOf] using hwWBsub
    let wWB : WB := ⟨(w : Dm), hwWB⟩
    let uK : K := hWBK wWB
    rcases hH1cMF_norm_U ((uK : U)⁻¹) with
      ⟨hconjMF, action, haction, hmap⟩
    have hmem_action :
        action (QuotientGroup.mk' (H0.subgroupOf MF) mMF) ∈ H1cMF := by
      rw [hmap]
      exact Subgroup.mem_map_of_mem action.toMonoidHom hmH1c
    let conjMF : MF :=
      ⟨(((uK : K) : U) : G) * (mMF : G) * (((uK : K) : U) : G)⁻¹,
        by simpa using hconjMF mMF⟩
    have hmem_conj :
        QuotientGroup.mk' (H0.subgroupOf MF) conjMF ∈ H1cMF := by
      rw [haction mMF] at hmem_action
      simpa [conjMF, mul_assoc] using hmem_action
    have hconjMFD : Section2.conjBy (w : Dm) (m : Dm) ∈ MFD := by
      exact hBsemi.right_normalizes_left (w : Dm) hwWB (m : Dm) hmMFD
    let conjB : B :=
      ⟨Section2.conjBy (w : Dm) (m : Dm), hBsemi.left_le hconjMFD⟩
    have hconjB_MFDsub : conjB ∈ MFDsubB := by
      simpa [MFDsubB, Subgroup.mem_subgroupOf, conjB] using hconjMFD
    let conjSub : MFDsubB := ⟨conjB, hconjB_MFDsub⟩
    let yConj : QMF := ⟨qB conjSub, ⟨conjSub, conjSub.property, rfl⟩⟩
    have hconjMF_eq : eMFD (eMFDsub conjSub) = conjMF := by
      apply Subtype.ext
      have hu_eq :
          (((uK : K) : U) : G) = ((((wWB : WB) : Dm) : M) : G) := by
        simpa [uK] using hWBK_compat' wWB
      simp [conjSub, conjB, conjMF, mSub, mMF, wWB, hu_eq, eMFD, eMFDsub,
        Subgroup.subgroupOfEquivOfLe, Section2.conjBy, mul_assoc]
    have hyConj_QH1csub : yConj ∈ QH1csub := by
      change hQMF_equiv yConj ∈ H1cMF
      rw [hQMF_equiv_apply_mk conjSub, hconjMF_eq]
      exact hmem_conj
    refine ⟨yConj, hyConj_QH1csub, ?_⟩
    have hconjQ :
        qB conjB = Section2.conjBy (qB w) (qB m) := by
      have hconjB_eq : conjB = w * m * w⁻¹ := by
        apply Subtype.ext
        rfl
      rw [hconjB_eq]
      simp [Section2.conjBy, map_mul, map_inv, mul_assoc]
    rw [← hwk, ← hyh]
    change qB conjB = Section2.conjBy (qB w) (y : Q)
    rw [← hmy]
    exact hconjQ
  have hsemiQ :
      Section2.IsInternalSemidirectProduct (⊤ : Subgroup Q) QH1c QH1CH1 := by
    -- Associativity of the canonical quotient semidirect product:
    -- `Q = (QH1c × QH1) ⋊ QClam = QH1c ⋊ (QH1 × QClam)`.
    have hQH1c_le_QMF : QH1c ≤ QMF := by
      intro x hx
      rcases hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hQH1_normalizes_QH1c :
        ∀ k ∈ QH1, ∀ h ∈ QH1c, Section2.conjBy k h ∈ QH1c := by
      intro k hk h hh
      have hconj_eq : Section2.conjBy k h = h := by
        calc
          Section2.conjBy k h = k * h * k⁻¹ := rfl
          _ = h * k * k⁻¹ := by
            rw [(hQMF_split_in_Q.commute h hh k hk).symm]
          _ = h := by simp [mul_assoc]
      simpa [hconj_eq] using hh
    have hQH1CH1_normalizes_QH1c :
        ∀ k ∈ QH1CH1, ∀ h ∈ QH1c, Section2.conjBy k h ∈ QH1c := by
      intro k hk h hh
      rcases hprod.mul_surjective k hk with ⟨q1, hq1, qc, hqc, hkprod⟩
      have hqc_h : Section2.conjBy qc h ∈ QH1c :=
        hQClam_normalizes_QH1c qc hqc h hh
      have hq1_norm :
          Section2.conjBy q1 (Section2.conjBy qc h) ∈ QH1c :=
        hQH1_normalizes_QH1c q1 hq1 (Section2.conjBy qc h) hqc_h
      have hconj_eq :
          Section2.conjBy k h =
            Section2.conjBy q1 (Section2.conjBy qc h) := by
        rw [hkprod]
        simp [Section2.conjBy, mul_assoc]
      simpa [hconj_eq] using hq1_norm
    have hQH1c_inf_QH1CH1 : QH1c ⊓ QH1CH1 = ⊥ := by
      apply le_antisymm
      · intro x hx
        rcases hprod.mul_surjective x hx.2 with ⟨q1, hq1, qc, hqc, hxprod⟩
        have hxQMF : x ∈ QMF := hQH1c_le_QMF hx.1
        have hq1QMF : q1 ∈ QMF := hQH1_le_QMF hq1
        have hqcQMF : qc ∈ QMF := by
          have hqc_eq : qc = q1⁻¹ * x := by
            rw [hxprod]
            simp
          rw [hqc_eq]
          exact QMF.mul_mem (QMF.inv_mem hq1QMF) hxQMF
        have hqcInf : qc ∈ QMF ⊓ QClam := ⟨hqcQMF, hqc⟩
        have hqc_one : qc = 1 := by
          have hbot : qc ∈ (⊥ : Subgroup Q) := by
            simpa [hQMF_inf_QClam] using hqcInf
          simpa using hbot
        have hx_eq_q1 : x = q1 := by
          rw [hxprod, hqc_one]
          simp
        have hxQH1 : x ∈ QH1 := by
          simpa [hx_eq_q1] using hq1
        have hxInf : x ∈ QH1c ⊓ QH1 := ⟨hx.1, hxQH1⟩
        have hxBot : x ∈ (⊥ : Subgroup Q) := by
          simpa [hQMF_split_in_Q.inf_eq_bot] using hxInf
        simpa using hxBot
      · exact bot_le
    refine
      { left_le := ?_
        right_le := ?_
        right_normalizes_left := hQH1CH1_normalizes_QH1c
        inf_eq_bot := hQH1c_inf_QH1CH1
        mul_surjective := ?_ }
    · intro x _hx
      trivial
    · intro x _hx
      trivial
    · intro c _hc
      rcases hsemiQMF.mul_surjective c (by trivial) with
        ⟨qmf, hqmf, qc, hqc, hcprod⟩
      rcases hQMF_split_in_Q.mul_surjective qmf hqmf with
        ⟨qh1c, hqh1c, qh1, hqh1, hqmfprod⟩
      have hright : qh1 * qc ∈ QH1CH1 := by
        change qh1 * qc ∈ QH1 ⊔ QClam
        have hqh1_sup : qh1 ∈ QH1 ⊔ QClam :=
          (le_sup_left : QH1 ≤ QH1 ⊔ QClam) hqh1
        have hqc_sup : qc ∈ QH1 ⊔ QClam :=
          (le_sup_right : QClam ≤ QH1 ⊔ QClam) hqc
        exact (QH1 ⊔ QClam).mul_mem hqh1_sup hqc_sup
      refine ⟨qh1c, hqh1c, qh1 * qc, hright, ?_⟩
      rw [hcprod, hqmfprod]
      simp [mul_assoc]
  exact
    ⟨QH1c, QH1, QClam, QH1CH1, hsemiQ, hprod, hQH1_equiv, hQClam_equiv,
      (fun m hmH1 => by
        have hmRaw_eq :
            eMFD (eMFDsub m) =
              theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m) := by
          ext
          rfl
        have hmH1' :
            QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m)) ∈
              H ⟨0, hqpos⟩ := by
          simpa [hmRaw_eq] using hmH1
        rcases hQH1_equiv_apply_mk m hmH1' with ⟨hmQH1, hmQH1_apply⟩
        refine ⟨hmQH1, ?_⟩
        simpa [hmRaw_eq] using hmQH1_apply),
      (fun m hmH1c => by
        have hmRaw_eq :
            eMFD (eMFDsub m) =
              theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m) := by
          ext
          rfl
        have hmH1c' :
            QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m)) ∈
              H1cMF := by
          simpa [H1cMF, hmRaw_eq] using hmH1c
        simpa using hQH1c_apply_mk m hmH1c'),
      (fun w => by
        let hwQClam : QuotientGroup.mk' (A.subgroupOf B) w ∈ QClam := by
          exact ⟨w, w.property, rfl⟩
        refine ⟨hwQClam, ?_⟩
        exact hQClam_equiv_apply_mk w),
    QMF, rfl, hQMF_split_in_Q, hQH1_le_QMF⟩

set_option maxHeartbeats 2000000 in
private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_canonical_quotient_product_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype)
    (B : Subgroup ((ambientDerivedSubgroup M).subgroupOf M))
    (hBnormal : B.Normal)
    (hBsemi :
      Section2.IsInternalSemidirectProduct B
        ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M))
        (((U.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) ⊓ B))
    (hWBK :
      let W : Subgroup ((ambientDerivedSubgroup M).subgroupOf M) :=
        (U.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)
      let f : U →* ρBase.range :=
        ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
      let K : Subgroup U := f.ker
      ↥(W ⊓ B) ≃* K)
    (hWBK_compat :
      let W : Subgroup ((ambientDerivedSubgroup M).subgroupOf M) :=
        (U.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)
      let f : U →* ρBase.range :=
        ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
      let K : Subgroup U := f.ker
      ∀ x : ↥(W ⊓ B),
        (((hWBK x : K) : U) : G) =
          ((((x : (ambientDerivedSubgroup M).subgroupOf M) : M) : G)))
    (hWBKquot :
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_right_factor_quotient_bridge_data_sec9
        M MF U H0 C Uprime q H hqpos ρBase hUprimeEq B hWBK)
    (_hA_le_B :
      (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)) ≤ B)
    (_hBindex : Subgroup.index B = a) :
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
    let f : U →* ρBase.range :=
      ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
    let K : Subgroup U := f.ker
    let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
      theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
        U Uprime hUprimeEq
    let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
    letI : Hsub.Normal := hUprimeNormal.subgroupOf K
    let Clam : Type u := K ⧸ Hsub
    letI : Group Clam := inferInstance
    ∃ hAnormal : A.Normal,
      letI : B.Normal := hBnormal
      letI : A.Normal := hAnormal
      letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
      let Q : Type u := B ⧸ A.subgroupOf B
      letI : Group Q := inferInstance
      let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
      let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
      let MFDsubB : Subgroup B := MFD.subgroupOf B
      ∃ QH1c : Subgroup Q,
      ∃ QH1 : Subgroup Q,
      ∃ QClam : Subgroup Q,
      ∃ QH1CH1 : Subgroup Q,
      ∃ _hsemi : Section2.IsInternalSemidirectProduct
          (⊤ : Subgroup Q) QH1c QH1CH1,
      ∃ _hprod : Section2.IsInternalDirectProduct QH1CH1 QH1 QClam,
      ∃ eH1 : QH1 ≃* H ⟨0, hqpos⟩,
      ∃ eClam : QClam ≃* Clam,
        (∀ m : MFDsubB,
          ∀ hmH1 :
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
              H ⟨0, hqpos⟩,
            ∃ hmQH1 : QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1,
              eH1
                  ⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ =
                  ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                      (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                        ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)),
                    hmH1⟩) ∧
          (∀ m : MFDsubB,
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
              (⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i) →
            QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1c) ∧
          (∀ w : (W ⊓ B).subgroupOf B,
            ∃ hwQClam : QuotientGroup.mk' (A.subgroupOf B) w ∈ QClam,
              eClam
                  ⟨QuotientGroup.mk' (A.subgroupOf B) w, hwQClam⟩ =
                QuotientGroup.mk' Hsub
                  (hWBK
                    (⟨((w : B) : Dm), by
                      simpa [W, Subgroup.mem_subgroupOf] using w.property⟩ :
                      ↥(W ⊓ B)))) ∧
            ∃ QMF : Subgroup Q,
              QMF =
                  ((MFD.subgroupOf B).map (QuotientGroup.mk' (A.subgroupOf B))) ∧
              Section2.IsInternalDirectProduct QMF QH1c QH1 ∧
              QH1 ≤ QMF := by
  classical
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  have hAnormal : A.Normal := by
    simpa [Dm, A] using
      theorem_9_8_H0Uprime_normal_ambientDerived_subgroupOf_sec9
        M MF U W1 W2 H0 C Uprime p q a hcase hUprimeEq
  refine ⟨hAnormal, ?_⟩
  simpa [Dm, A] using
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_canonical_quotient_decomposition_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
      ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
      hUprimeEq B hBnormal hBsemi hWBK hWBK_compat hWBKquot _hA_le_B _hBindex
      (by simpa [Dm, A] using hAnormal)

set_option maxHeartbeats 800000 in
private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_structure_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_structure_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  classical
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
  let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
  let fU : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨hhallD, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hFittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hhallD with ⟨hDleM, _hDHall⟩
  rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
  have hMFDnormal : MFD.Normal := by
    simpa [Dm, MFD] using
      theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
        M MF U W1 W2 H0 C p q a hcase
  letI : MFD.Normal := hMFDnormal
  have hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup Dm) MFD W := by
    simpa [Dm, MFD, W] using
      theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
        M MF U W1 W2 q h92
        (by simpa [Dm, MFD] using hMFDnormal)
  let toU : W →* U := theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U
  let Φ : Dm →* ρBase.range :=
    (fU.comp toU).comp (internalSemidirectRightProjectionTop_sec9 hsemi)
  let B : Subgroup Dm := Φ.ker
  have hBnormal : B.Normal := by
    simpa [B] using MonoidHom.normal_ker Φ
  have hMFleM : MF ≤ M := hMFleD.trans hDleM
  have hUleM : U ≤ M := hUleD.trans hDleM
  have htoU_surj : Function.Surjective toU := by
    intro u0
    let uM : M := ⟨(u0 : G), hUleM u0.property⟩
    let uD : Dm :=
      ⟨uM, by
        simpa [Dm, Subgroup.mem_subgroupOf, uM] using hUleD u0.property⟩
    let uW : W :=
      ⟨uD, by
        change (uD : M) ∈ U.subgroupOf M
        simp [uD, uM, Subgroup.mem_subgroupOf]⟩
    exact ⟨uW, by
      ext
      rfl⟩
  have hΦrange_top : Φ.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u0, rfl⟩
    rcases htoU_surj u0 with ⟨w, hw⟩
    refine ⟨(w : Dm), ?_⟩
    ext
    simp [Φ, fU, toU, internalSemidirectRightProjectionTop_apply_right_sec9 hsemi w, hw]
  have hBindex : Subgroup.index B = a := by
    calc
      Subgroup.index B = Nat.card Φ.range := by
        simpa [B] using Subgroup.index_ker Φ
      _ = Nat.card (⊤ : Subgroup ρBase.range) := by rw [hΦrange_top]
      _ = Nat.card ρBase.range := by simp
      _ = a := hρcardBase
  have hMFD_to_B : MFD ≤ B := by
    intro x hx
    change Φ x = 1
    have hproj :
        internalSemidirectRightProjectionTop_sec9 hsemi (x : Dm) = 1 := by
      simpa using
        internalSemidirectRightProjectionTop_apply_left_sec9 hsemi
          ⟨(x : Dm), hx⟩
    simp [Φ, hproj]
  have hBsemi : Section2.IsInternalSemidirectProduct B MFD (W ⊓ B) := by
    refine
      { left_le := hMFD_to_B
        right_le := inf_le_right
        right_normalizes_left := ?_
        inf_eq_bot := ?_
        mul_surjective := ?_ }
    · intro k hk h hh
      exact hsemi.right_normalizes_left k hk.1 h hh
    · apply le_antisymm
      · intro x hx
        have hxInf : x ∈ MFD ⊓ W := ⟨hx.1, hx.2.1⟩
        have hxBot : x ∈ (⊥ : Subgroup Dm) := by
          simpa [hsemi.inf_eq_bot] using hxInf
        simpa using hxBot
      · exact bot_le
    · intro c hc
      rcases hsemi.mul_surjective c (by trivial) with ⟨m, hm, w, hw, hmw⟩
      have hmB : m ∈ B := hMFD_to_B hm
      have hwB : w ∈ B := by
        have hw_eq : w = m⁻¹ * c := by
          calc
            w = m⁻¹ * (m * w) := by simp
            _ = m⁻¹ * c := by rw [← hmw]
        rw [hw_eq]
        exact B.mul_mem (B.inv_mem hmB) hc
      exact ⟨m, hm, w, ⟨hw, hwB⟩, hmw⟩
  let K : Subgroup U := fU.ker
  let rightToK : ↥(W ⊓ B) →* K :=
    { toFun := fun x => by
        refine ⟨toU ⟨(x : Dm), x.property.1⟩, ?_⟩
        change fU (toU ⟨(x : Dm), x.property.1⟩) = 1
        have hproj :
            internalSemidirectRightProjectionTop_sec9 hsemi (x : Dm) =
              (⟨(x : Dm), x.property.1⟩ : W) := by
          simpa using
            internalSemidirectRightProjectionTop_apply_right_sec9 hsemi
              (⟨(x : Dm), x.property.1⟩ : W)
        have hxB : Φ (x : Dm) = 1 := x.property.2
        simpa [Φ, hproj] using hxB
      map_one' := by
        ext
        rfl
      map_mul' := by
        intro x y
        ext
        rfl }
  have hrightToK_inj : Function.Injective rightToK := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : K => ((z : U) : G)) hxy
  have hrightToK_surj : Function.Surjective rightToK := by
    intro k
    let uM : M := ⟨(k : G), hUleM (k : U).property⟩
    let uD : Dm :=
      ⟨uM, by
        simpa [Dm, Subgroup.mem_subgroupOf, uM] using hUleD (k : U).property⟩
    have huW : uD ∈ W := by
      change (uD : M) ∈ U.subgroupOf M
      simp [uD, uM, Subgroup.mem_subgroupOf]
    let uW : W := ⟨uD, huW⟩
    have huB : uD ∈ B := by
      change Φ uD = 1
      have hproj :
          internalSemidirectRightProjectionTop_sec9 hsemi uD = uW := by
        simpa [uW] using internalSemidirectRightProjectionTop_apply_right_sec9 hsemi uW
      have hto : toU uW = (k : U) := by
        ext
        rfl
      calc
        Φ uD = fU (toU uW) := by simp [Φ, hproj]
        _ = fU (k : U) := by rw [hto]
        _ = 1 := k.property
    let x : ↥(W ⊓ B) := ⟨uD, ⟨huW, huB⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  let eWBK : ↥(W ⊓ B) ≃* K :=
    MulEquiv.ofBijective rightToK ⟨hrightToK_inj, hrightToK_surj⟩
  have hWBK_compat :
      (let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
       let f : U →* ρBase.range :=
          ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
       let K : Subgroup U := f.ker
       ∀ x : ↥(W ⊓ B),
        (((eWBK x : K) : U) : G) = ((((x : Dm) : M) : G))) := by
    dsimp
    intro x
    change (((rightToK x : K) : U) : G) = ((((x : Dm) : M) : G))
    simp [rightToK, toU, theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9]
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hUprimeU : Uprime ≤ U := by
    rw [hUprimeEq, Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_le_self U
  have hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  have hH0leM : H0 ≤ M := hH0MF.trans hMFleM
  have hUprimeleM : Uprime ≤ M := hUprimeU.trans hUleM
  have hH0subD : H0.subgroupOf M ≤ Dm := by
    intro x hx
    have hxH0 : ((x : M) : G) ∈ H0 := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact (hH0MF.trans hMFleD) hxH0
  have hUprimeSubD : Uprime.subgroupOf M ≤ Dm := by
    intro x hx
    have hxUprime : ((x : M) : G) ∈ Uprime := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact (hUprimeU.trans hUleD) hxUprime
  have hUprime_le_fUker : Uprime.subgroupOf U ≤ fU.ker := by
    simpa [fU] using
      theorem_9_8_initial_constituent_Mtheta_baseActionKernel_uprime_le_sec9
        U C Uprime ρBase hρcycBase hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  let UprimeD : Subgroup Dm := (Uprime.subgroupOf M).subgroupOf Dm
  let WBUprime : Subgroup ↥(W ⊓ B) := UprimeD.subgroupOf (W ⊓ B)
  have hWBUprime_eq_comap : WBUprime = Hsub.comap eWBK.toMonoidHom := by
    ext x
    constructor
    · intro hxWBU
      have hxUprimeD : (x : Dm) ∈ UprimeD := by
        simpa [WBUprime, Subgroup.mem_subgroupOf] using hxWBU
      have hxUprime : (((x : Dm) : M) : G) ∈ Uprime := by
        simpa [UprimeD, Subgroup.mem_subgroupOf] using hxUprimeD
      change ((eWBK x : K) : U) ∈ Uprime.subgroupOf U
      change ((rightToK x : K) : U) ∈ Uprime.subgroupOf U
      change ((toU ⟨(x : Dm), x.property.1⟩ : U) : G) ∈ Uprime
      simpa [toU, theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9] using hxUprime
    · intro hk
      change ((eWBK x : K) : U) ∈ Uprime.subgroupOf U at hk
      change ((rightToK x : K) : U) ∈ Uprime.subgroupOf U at hk
      change ((toU ⟨(x : Dm), x.property.1⟩ : U) : G) ∈ Uprime at hk
      have hxUprime : (((x : Dm) : M) : G) ∈ Uprime := by
        simpa [toU, theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9] using hk
      simpa [WBUprime, UprimeD, Subgroup.mem_subgroupOf] using hxUprime
  let WBHsub : Subgroup ↥(W ⊓ B) := Hsub.comap eWBK.toMonoidHom
  have hWBHsub_map : WBHsub.map eWBK.toMonoidHom = Hsub := by
    exact Subgroup.map_comap_eq_self_of_surjective eWBK.surjective Hsub
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  letI : WBHsub.Normal := (hUprimeNormal.subgroupOf K).comap eWBK.toMonoidHom
  let hWBHsubQuot : (↥(W ⊓ B) ⧸ WBHsub) ≃* (K ⧸ Hsub) := by
    exact QuotientGroup.congr WBHsub Hsub eWBK hWBHsub_map
  have hWBHsubQuot_apply :
      ∀ x : ↥(W ⊓ B),
        hWBHsubQuot (QuotientGroup.mk' WBHsub x) =
          QuotientGroup.mk' Hsub (eWBK x) := by
    intro x
    simp [hWBHsubQuot]
  have hWBKquot :
      ∃ eWBHsub : (↥(W ⊓ B) ⧸ WBHsub) ≃* (K ⧸ Hsub),
        WBUprime = WBHsub ∧
          ∀ x : ↥(W ⊓ B),
            eWBHsub (QuotientGroup.mk' WBHsub x) =
              QuotientGroup.mk' Hsub (eWBK x) :=
    ⟨hWBHsubQuot, hWBUprime_eq_comap, hWBHsubQuot_apply⟩
  have hH0_to_B : (H0.subgroupOf M).subgroupOf Dm ≤ B := by
    intro x hx
    change Φ x = 1
    have hxMFD : (x : Dm) ∈ MFD := by
      have hxH0 : (((x : Dm) : M) : G) ∈ H0 := by
        simpa [Subgroup.mem_subgroupOf] using hx
      exact hH0MF hxH0
    have hproj :
        internalSemidirectRightProjectionTop_sec9 hsemi (x : Dm) = 1 := by
      simpa using
        internalSemidirectRightProjectionTop_apply_left_sec9 hsemi
          ⟨(x : Dm), hxMFD⟩
    simp [Φ, hproj]
  have hUprime_to_B : (Uprime.subgroupOf M).subgroupOf Dm ≤ B := by
    intro x hx
    change Φ x = 1
    have hxUprime : (((x : Dm) : M) : G) ∈ Uprime := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxW : (x : Dm) ∈ W := by
      exact hUprimeU hxUprime
    let w : W := ⟨(x : Dm), hxW⟩
    have hproj :
        internalSemidirectRightProjectionTop_sec9 hsemi (x : Dm) = w := by
      simpa [w] using internalSemidirectRightProjectionTop_apply_right_sec9 hsemi w
    have htoU_Uprime : toU w ∈ Uprime.subgroupOf U := by
      change ((toU w : U) : G) ∈ Uprime
      simpa [toU, w,
        theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9] using hxUprime
    have hfU : fU (toU w) = 1 := hUprime_le_fUker htoU_Uprime
    calc
      Φ x = fU (toU w) := by simp [Φ, hproj]
      _ = 1 := hfU
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  have hA_le_B : A ≤ B := by
    change (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm) ≤ B
    rw [Subgroup.subgroupOf_sup (A := H0) (A' := Uprime) (B := M)
      hH0leM hUprimeleM]
    rw [Subgroup.subgroupOf_sup (A := H0.subgroupOf M)
      (A' := Uprime.subgroupOf M) (B := Dm) hH0subD hUprimeSubD]
    exact sup_le hH0_to_B hUprime_to_B
  rcases
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_canonical_quotient_product_source_core_sec9
        M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
        ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
        hUprimeEq B hBnormal (by simpa [MFD, W, B] using hBsemi)
        (by simpa [W, fU, K] using eWBK)
        (by simpa [W, fU, K] using hWBK_compat)
        (by
          dsimp
            [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_right_factor_quotient_bridge_data_sec9]
          simpa [W, fU, K, Hsub, UprimeD, WBUprime, WBHsub] using hWBKquot)
        (by simpa [A] using hA_le_B) hBindex with
      ⟨hAnormal, QH1c, QH1, QClam, QH1CH1, hsemiQ, hprod, eH1, eClam,
        hQH1_apply, hQH1c_apply, hQClam_apply, QMF, hQMF_eq, hQMF_split_in_Q,
        hQH1_le_QMF⟩
  exact
    ⟨B, hBnormal, hAnormal, by simpa [A] using hA_le_B, hBindex,
      by simpa [MFD] using hMFD_to_B,
      by simpa [MFD, W, B] using hBsemi,
      by simpa [W, fU, K] using eWBK,
      by simpa [W, fU, K] using hWBK_compat,
      QMF, QH1c, QH1, QClam, QH1CH1, hsemiQ, hprod, eH1, eClam,
      hQH1_apply, hQH1c_apply, hQClam_apply, hQMF_eq, hQMF_split_in_Q,
      hQH1_le_QMF⟩


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 100000 in
private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_character_irr_Xtheta_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (_hρcardBase : Nat.card ρBase.range = a)
    (_hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (_hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (_hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    let f : U →* ρBase.range :=
      ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
    let K : Subgroup U := f.ker
    let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
      theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
        U Uprime hUprimeEq
    let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
    letI : Hsub.Normal := hUprimeNormal.subgroupOf K
    let Clam : Type u := K ⧸ Hsub
    letI : Group Clam := inferInstance
    let hClamComm : IsMulCommutative Clam :=
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
        U C Uprime ρBase hUprimeEq
    let Lam : Type u := Clam →* ℂˣ
    let hf_surj : Function.Surjective f := by
      intro y
      rcases y with ⟨y, hy⟩
      rcases hy with ⟨x, rfl⟩
      rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
      exact ⟨u, rfl⟩
    letI : IsCyclic ρBase.range := hρcycBase
    letI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
    let σ : ρBase.range →* MulAut Clam :=
      mulAutHomInvOfCommDomain_sec9
        (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
          simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
    let instLamAction : MulAction ρBase.range Lam :=
      linearCharacterMulAction_sec9 σ
    let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
      Subgroup.subtype ρBase.range
    let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
      nonprincipalLinearCharacterIndexMulAction_sec9 p
        (hHcard ⟨0, hqpos⟩) ρRange
    letI : MulAction ρBase.range Lam := instLamAction
    letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
    let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
    let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
    ∀ (B : Subgroup Dm) (hBnormal : B.Normal) (hAnormal : A.Normal),
    ∀ (_hA_le_B : A ≤ B)
      (_hMFD_le_B : MFD ≤ B)
      (hBsemi : Section2.IsInternalSemidirectProduct B MFD (W ⊓ B))
      (eWBK : ↥(W ⊓ B) ≃* K)
      (_hWBK_compat :
        ∀ x : ↥(W ⊓ B),
          (((eWBK x : K) : U) : G) = ((((x : Dm) : M) : G))),
    letI : B.Normal := hBnormal
    letI : A.Normal := hAnormal
    letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
    let Q : Type u := B ⧸ A.subgroupOf B
    letI : Group Q := inferInstance
    ∀ (QH1c QH1 QClam QH1CH1 : Subgroup Q),
    ∀ (hsemi : Section2.IsInternalSemidirectProduct
        (⊤ : Subgroup Q) QH1c QH1CH1)
      (hprod : Section2.IsInternalDirectProduct QH1CH1 QH1 QClam)
      (eH1 : QH1 ≃* H ⟨0, hqpos⟩)
      (eClam : QClam ≃* Clam),
    ∀ (_hQH1_apply :
        ∀ (m : MFD.subgroupOf B)
          (hmH1 :
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
              H ⟨0, hqpos⟩),
            ∃ hmQH1 : QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1,
              eH1 ⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ =
                ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                    (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                      ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)),
                  hmH1⟩)
      (_hQH1c_apply :
        ∀ m : MFD.subgroupOf B,
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
            (⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i) →
          QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1c)
      (_hQClam_apply :
        ∀ w : (W ⊓ B).subgroupOf B,
          ∃ hwQClam : QuotientGroup.mk' (A.subgroupOf B) w ∈ QClam,
            eClam ⟨QuotientGroup.mk' (A.subgroupOf B) w, hwQClam⟩ =
              QuotientGroup.mk' Hsub
                (eWBK
                  (⟨((w : B) : Dm), by
                    simpa [W, Subgroup.mem_subgroupOf] using w.property⟩ :
                    ↥(W ⊓ B))))
      (QMF : Subgroup Q)
      (_hQMF_eq :
        QMF = ((MFD.subgroupOf B).map (QuotientGroup.mk' (A.subgroupOf B))))
      (_hQMF_split_in_Q : Section2.IsInternalDirectProduct QMF QH1c QH1)
      (_hQH1_le_QMF : QH1 ≤ QMF),
    let ψlin : Fin (p - 1) × Lam → Q →* ℂˣ := fun k =>
      semidirectProductOfInternalDirectProductLinearCharacter_sec9
        hsemi hprod
        (((nonprincipalLinearCharacterEquivFin_sec9
              (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1.comp
          eH1.toMonoidHom)
        (k.2.comp eClam.toMonoidHom)
    ∀ (_hIeq :
        ∀ k : Fin (p - 1) × Lam,
          Section1.inertiaSubgroup B
            (Section1.quotientCharacterInflation A B (ψlin k)) = B),
    ∀ (_hθnotMF :
        ∀ k : Fin (p - 1) × Lam,
          ¬ Section1.subgroupInKernel'
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin k))) MFD),
    ∀ k : Fin (p - 1) × Lam,
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF Dm
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k)))) := by
  classical
  dsimp
  intro B hBnormal hAnormal hA_le_B hMFD_le_B hBsemi eWBK hWBK_compat
    QH1c QH1 QClam QH1CH1 hsemi hprod eH1 eClam hQH1_apply hQH1c_apply
    hQClam_apply QMF hQMF_eq hQMF_split_in_Q hQH1_le_QMF hIeq hθnotMF k
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  letI : IsCyclic ρBase.range := hρcycBase
  letI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  let ψlin : Fin (p - 1) × Lam → (B ⧸ A.subgroupOf B) →* ℂˣ := fun k =>
    semidirectProductOfInternalDirectProductLinearCharacter_sec9
      hsemi hprod
      (((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1.comp
        eH1.toMonoidHom)
      (k.2.comp eClam.toMonoidHom)
  letI : B.Normal := hBnormal
  letI : A.Normal := hAnormal
  letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
  have hψirr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.quotientCharacterInflation A B (ψlin k)) :=
    Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      A B (ψlin k)
  have hinner :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF B
          (Section1.quotientCharacterInflation A B (ψlin k))) :=
    inducedCF_isIrreducible_of_inertia_eq_self_sec9 B hψirr (by
      simpa [ψlin] using hIeq k)
  have hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  have hcomp : Dm.IsComplement' (W1.subgroupOf M) := by
    dsimp [Dm]
    exact ambientDerived_W1_isComplement'_subgroupOf_M_of_hypothesis_9_2_sec9
      M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
  have hsemiM :
      Section2.IsInternalSemidirectProduct (⊤ : Subgroup M) Dm (W1.subgroupOf M) :=
    internalSemidirectProduct_top_of_normal_isComplement'_sec9 hcomp
  refine
    inducedCF_isIrreducible_of_semidirect_no_nontrivial_complement_fixed_sec9
      Dm (W1.subgroupOf M) hsemiM hinner ?_
  intro g hgW1 hg_ne hfix
  have hkerMFD :
      Section1.subgroupInKernel'
        (Section1.inducedCF B
          (Section1.quotientCharacterInflation A B (ψlin k))) MFD := by
    let χbase : H ⟨0, hqpos⟩ →* ℂˣ :=
      ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1
    let χQH1 : QH1 →* ℂˣ := χbase.comp eH1.toMonoidHom
    let ηQClam : QClam →* ℂˣ := k.2.comp eClam.toMonoidHom
    have hsourceKerQH1c :
        ∀ b : B,
          QuotientGroup.mk' (A.subgroupOf B) b ∈ QH1c →
            Section1.quotientCharacterInflation A B (ψlin k) b =
              Section1.degree
                (Section1.quotientCharacterInflation A B (ψlin k)) := by
      intro b hb
      let qh : QH1c := ⟨QuotientGroup.mk' (A.subgroupOf B) b, hb⟩
      have hproj :
          internalSemidirectRightProjectionTop_sec9 hsemi
              (QuotientGroup.mk' (A.subgroupOf B) b) = 1 := by
        simpa [qh] using
          internalSemidirectRightProjectionTop_apply_left_sec9 hsemi qh
      have hψ :
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) b) = 1 := by
        calc
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) b) =
              Section3.internalDirectProductLinearCharacter hprod χQH1 ηQClam
                (internalSemidirectRightProjectionTop_sec9 hsemi
                  (QuotientGroup.mk' (A.subgroupOf B) b)) := by
                rfl
          _ = Section3.internalDirectProductLinearCharacter hprod χQH1 ηQClam 1 := by
                rw [hproj]
          _ = 1 := by simp
      rw [Section1.quotientCharacterInflation_degree]
      simpa [Section1.quotientCharacterInflation, hψ]
    have hkerA :
        Section1.subgroupInKernel'
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k))) A :=
      subgroupInKernel'_inducedCF_of_subgroupInKernel'_sec9
        B A hA_le_B hψirr
        (Section1.subgroupInKernel'_quotientCharacterInflation A B (ψlin k))
    have hMFDnormal : MFD.Normal := by
      simpa [MFD, Dm] using
        theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
          M MF U W1 W2 H0 C p q a hcase
    letI : MFD.Normal := hMFDnormal
    let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
    have hsemiTop :
        Section2.IsInternalSemidirectProduct (⊤ : Subgroup Dm) MFD W := by
      simpa [MFD, W, Dm] using
        theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
          M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase) hMFDnormal
    let gW1 : W1 := ⟨(g : G), by
      simpa [Subgroup.mem_subgroupOf] using hgW1⟩
    have hgW1_ne : gW1 ≠ 1 := by
      intro hg1
      apply hg_ne
      ext
      exact congrArg (fun x : W1 => (x : G)) hg1
    let gW1inv : W1 := gW1⁻¹
    have hgW1inv_ne : gW1inv ≠ 1 := by
      intro hg1
      exact hgW1_ne (inv_eq_one.mp hg1)
    rcases theorem_9_8_weak_orbit_nonidentity_moves_base_sec9
        H hqpos hHcard hHnorm hHindep hconjBase hcase gW1inv hgW1inv_ne with
      ⟨iMove, hiMove_ne, hbase_to_iMove⟩
    let H1cMF : Subgroup (MF ⧸ H0.subgroupOf MF) :=
      ⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i
    rcases hbase_to_iMove with
      ⟨hconjMF_move, actionMove, hactionMove, htargetMove⟩
    have hbase_conj_mem_H1c :
        ∀ m : MF,
          QuotientGroup.mk' (H0.subgroupOf MF) m ∈ H ⟨0, hqpos⟩ →
            QuotientGroup.mk' (H0.subgroupOf MF)
                ⟨(g : G) * (m : G) * (g : G)⁻¹, by
                  simpa [gW1inv, gW1] using hconjMF_move m⟩ ∈ H1cMF := by
      intro m hmBase
      have htarget_mem :
          actionMove (QuotientGroup.mk' (H0.subgroupOf MF) m) ∈ H iMove := by
        rw [htargetMove]
        exact ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase, rfl⟩
      have hcoord :
          actionMove (QuotientGroup.mk' (H0.subgroupOf MF) m) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(g : G) * (m : G) * (g : G)⁻¹, by
                simpa [gW1inv, gW1] using hconjMF_move m⟩ := by
        simpa [gW1inv, gW1] using hactionMove m
      rw [hcoord] at htarget_mem
      exact
        Subgroup.mem_iSup_of_mem iMove
          (Subgroup.mem_iSup_of_mem hiMove_ne htarget_mem)
    let qMFD : MFD →* (MF ⧸ H0.subgroupOf MF) :=
      (QuotientGroup.mk' (H0.subgroupOf MF)).comp
        (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF)
    let MFDH1cSub : Subgroup MFD := H1cMF.comap qMFD
    let MFDH1Sub : Subgroup MFD := (H ⟨0, hqpos⟩).comap qMFD
    let MFDH1c : Subgroup Dm := MFDH1cSub.map MFD.subtype
    let MFDH1 : Subgroup Dm := MFDH1Sub.map MFD.subtype
    have hMFleD : MF ≤ ambientDerivedSubgroup M :=
      MF_le_ambientDerived_of_hypothesis_9_2_sec9
        M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
    have hDleM : ambientDerivedSubgroup M ≤ M :=
      section12_ambientDerivedSubgroup_le (E := M)
    have hqMFD_surj : Function.Surjective qMFD := by
      intro x
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨mMF, rfl⟩
      let mM : M := ⟨(mMF : G), hDleM (hMFleD mMF.property)⟩
      let mD : Dm := ⟨mM, by
        simpa [Dm, Subgroup.mem_subgroupOf, mM] using hMFleD mMF.property⟩
      let mMFD : MFD := ⟨mD, by
        change (mD : M) ∈ MF.subgroupOf M
        simp [mD, mM, Subgroup.mem_subgroupOf]⟩
      refine ⟨mMFD, ?_⟩
      rfl
    have hMF_Hsplit :
        Section2.IsInternalDirectProduct
          (⊤ : Subgroup (MF ⧸ H0.subgroupOf MF)) H1cMF (H ⟨0, hqpos⟩) := by
      simpa [H1cMF] using
        theorem_9_8_iSup_split_base_internalDirectProduct_sec9
          H ⟨0, hqpos⟩ hHindep hHsup
    have hMF_Hsplit_sup : H1cMF ⊔ H ⟨0, hqpos⟩ = ⊤ := by
      apply top_unique
      intro x _hx
      rcases hMF_Hsplit.mul_surjective x (by trivial) with
        ⟨h1c, hh1c, h1, hh1, hx⟩
      rw [hx]
      exact (H1cMF ⊔ H ⟨0, hqpos⟩).mul_mem
        (Subgroup.mem_sup_left hh1c) (Subgroup.mem_sup_right hh1)
    have hMFD_coord_sup : MFDH1cSub ⊔ MFDH1Sub = ⊤ := by
      have hle_range_H1c : H1cMF ≤ qMFD.range := by
        rw [MonoidHom.range_eq_top.mpr hqMFD_surj]
        exact le_top
      have hle_range_H1 : H ⟨0, hqpos⟩ ≤ qMFD.range := by
        rw [MonoidHom.range_eq_top.mpr hqMFD_surj]
        exact le_top
      calc
        MFDH1cSub ⊔ MFDH1Sub =
            (H1cMF ⊔ H ⟨0, hqpos⟩).comap qMFD := by
              simpa [MFDH1cSub, MFDH1Sub] using
                Subgroup.comap_sup_eq_of_le_range qMFD hle_range_H1c hle_range_H1
        _ = ⊤ := by
              rw [hMF_Hsplit_sup]
              rfl
    have hMFD_map_top : (⊤ : Subgroup MFD).map MFD.subtype = MFD := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, _hy, hyx⟩
        rw [← hyx]
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    have hMFDH_join : MFDH1c ⊔ MFDH1 = MFD := by
      calc
        MFDH1c ⊔ MFDH1 =
            (MFDH1cSub ⊔ MFDH1Sub).map MFD.subtype := by
              rw [Subgroup.map_sup]
        _ = (⊤ : Subgroup MFD).map MFD.subtype := by rw [hMFD_coord_sup]
        _ = MFD := hMFD_map_top
    have hH1cMF_norm_U : quotientSubgroupNormalizedBy MF H0 U H1cMF := by
      intro aU
      rcases hHnorm ⟨0, hqpos⟩ aU with ⟨hconjMF, action, haction, _hmapBase⟩
      refine ⟨hconjMF, action, haction, ?_⟩
      have hmap_each :
          ∀ i : Fin q, (H i).map action.toMonoidHom = H i := by
        intro i
        rcases hHnorm i aU with ⟨hconjMF_i, action_i, haction_i, hmap_i⟩
        have haction_eq : action_i = action := by
          ext x
          rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨h, rfl⟩
          calc
            action_i (QuotientGroup.mk' (H0.subgroupOf MF) h) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(aU : G)⁻¹ * (h : G) * (aU : G), hconjMF_i h⟩ := haction_i h
            _ = QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(aU : G)⁻¹ * (h : G) * (aU : G), hconjMF h⟩ := by
                  congr 1
            _ = action (QuotientGroup.mk' (H0.subgroupOf MF) h) := (haction h).symm
        simpa [haction_eq] using hmap_i.symm
      have hmap_sup : H1cMF.map action.toMonoidHom = H1cMF := by
        simp_rw [H1cMF, Subgroup.map_iSup, hmap_each]
      exact hmap_sup.symm
    have hsourceKerMFDH1c :
        Section1.subgroupInKernel'
          (Section1.quotientCharacterInflation A B (ψlin k))
          (MFDH1c.subgroupOf B) := by
      intro a
      have haMFDH1c : ((a : B) : Dm) ∈ MFDH1c := by
        exact Subgroup.mem_subgroupOf.mp a.property
      rcases haMFDH1c with ⟨y, hyH1c, hy_eq⟩
      have haMFD : ((a : B) : Dm) ∈ MFD := by
        rw [← hy_eq]
        exact y.property
      let mSub : MFD.subgroupOf B := ⟨a, by
        simpa [Subgroup.mem_subgroupOf] using haMFD⟩
      have hy_mSub :
          y = (Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub := by
        apply Subtype.ext
        simpa [mSub, Subgroup.subgroupOfEquivOfLe] using hy_eq
      have hmH1c :
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub)) ∈
            H1cMF := by
        have hycoord : qMFD y ∈ H1cMF := by
          simpa [MFDH1cSub] using hyH1c
        simpa [qMFD, hy_mSub]
          using hycoord
      have hmQH1c :
          QuotientGroup.mk' (A.subgroupOf B) mSub ∈ QH1c :=
        hQH1c_apply mSub hmH1c
      simpa [mSub] using hsourceKerQH1c a hmQH1c
    have hMFDH1c_le_MFD : MFDH1c ≤ MFD := by
      intro x hx
      rcases hx with ⟨y, _hy, hyx⟩
      rw [← hyx]
      exact y.property
    have hMFDH1c_le_B : MFDH1c ≤ B :=
      hMFDH1c_le_MFD.trans hMFD_le_B
    have hMFDH1c_normal : MFDH1c.Normal := by
      refine Subgroup.Normal.mk ?_
      intro n hn x
      rcases hn with ⟨n0, hn0H1c, hn0_eq⟩
      have hnMFD : n ∈ MFD := by
        rw [← hn0_eq]
        exact n0.property
      let conjMFD : MFD := ⟨x * n * x⁻¹, hMFDnormal.conj_mem n hnMFD x⟩
      refine ⟨conjMFD, ?_, rfl⟩
      rcases hsemiTop.mul_surjective x (by trivial) with ⟨m, hm, w, hw, hxmw⟩
      let mMFD : MFD := ⟨m, hm⟩
      let wU : U := ⟨(((w : Dm) : M) : G), by
        have hwUM : ((w : Dm) : M) ∈ U.subgroupOf M := by
          simpa [W, Dm, Subgroup.mem_subgroupOf] using hw
        simpa [Subgroup.mem_subgroupOf] using hwUM⟩
      let wConjMFD : MFD :=
        ⟨w * n * w⁻¹, hsemiTop.right_normalizes_left w hw n hnMFD⟩
      have hq_wConj_mem : qMFD wConjMFD ∈ H1cMF := by
        rcases hH1cMF_norm_U (wU⁻¹) with
          ⟨hconjMF, action, haction, hmap⟩
        have hmem_action : action (qMFD n0) ∈ H1cMF := by
          rw [hmap]
          exact Subgroup.mem_map_of_mem action.toMonoidHom (by
            simpa [MFDH1cSub] using hn0H1c)
        have hcoord : action (qMFD n0) = qMFD wConjMFD := by
          let nMF : MF := theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF n0
          have hact := haction nMF
          have hrhs :
              QuotientGroup.mk' (H0.subgroupOf MF)
                  (⟨(((wU⁻¹ : U) : G))⁻¹ * (nMF : G) * ((wU⁻¹ : U) : G),
                    hconjMF nMF⟩ : MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF wConjMFD) := by
            congr 1
            apply Subtype.ext
            simpa [theorem_9_8_MFDSubgroupOf_to_MF_sec9, nMF, wConjMFD, wU,
              hn0_eq, mul_assoc]
          calc
            action (qMFD n0) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  (⟨(((wU⁻¹ : U) : G))⁻¹ * (nMF : G) * ((wU⁻¹ : U) : G),
                    hconjMF nMF⟩ : MF) := by
                  simpa [qMFD, nMF] using hact
            _ = qMFD wConjMFD := by
                  simpa [qMFD] using hrhs
        rwa [hcoord] at hmem_action
      have hH1c_normal : H1cMF.Normal :=
        by
          refine Subgroup.Normal.mk ?_
          intro n hn g
          have h : g * n * g⁻¹ = n := by
            simp [mul_assoc, mul_comm]
          simpa [h] using hn
      have hconj_eq :
          conjMFD = mMFD * wConjMFD * mMFD⁻¹ := by
        apply Subtype.ext
        simp [conjMFD, mMFD, wConjMFD, hxmw, mul_assoc]
      rw [hconj_eq]
      change qMFD (mMFD * wConjMFD * mMFD⁻¹) ∈ H1cMF
      simpa [map_mul, map_inv, mul_assoc] using
        hH1c_normal.conj_mem (qMFD wConjMFD) hq_wConj_mem (qMFD mMFD)
    letI : MFDH1c.Normal := hMFDH1c_normal
    have hkerMFDH1c :
        Section1.subgroupInKernel'
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k))) MFDH1c :=
      subgroupInKernel'_inducedCF_of_subgroupInKernel'_sec9
        B MFDH1c hMFDH1c_le_B hψirr hsourceKerMFDH1c
    have hkerMFDH1 :
        Section1.subgroupInKernel'
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k))) MFDH1 := by
      intro z
      rcases z.property with ⟨z0, hz0H1, hz0_eq⟩
      let zD : Dm := MFD.subtype z0
      let zMF : MF := theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF z0
      have hz0Base :
          QuotientGroup.mk' (H0.subgroupOf MF) zMF ∈ H ⟨0, hqpos⟩ := by
        simpa [MFDH1Sub, qMFD, zMF] using hz0H1
      let zConjD : Dm :=
        ⟨(g : M) * (zD : M) * (g : M)⁻¹,
          hDnormal.conj_mem (zD : M) zD.property g⟩
      have hzConjMFD : zConjD ∈ MFD := by
        change (zConjD : M) ∈ MF.subgroupOf M
        have hzMFconj := hconjMF_move zMF
        simpa [zConjD, zD, zMF, gW1inv, gW1,
          theorem_9_8_MFDSubgroupOf_to_MF_sec9,
          Subgroup.mem_subgroupOf, mul_assoc] using hzMFconj
      let zConjMFD : MFD := ⟨zConjD, hzConjMFD⟩
      have hzConjH1cSub : zConjMFD ∈ MFDH1cSub := by
        have hzcoord := hbase_conj_mem_H1c zMF hz0Base
        simpa [MFDH1cSub, qMFD, zConjMFD, zConjD, zD, zMF,
          theorem_9_8_MFDSubgroupOf_to_MF_sec9, mul_assoc] using hzcoord
      have hzConjH1c : zConjD ∈ MFDH1c :=
        ⟨zConjMFD, hzConjH1cSub, rfl⟩
      have hker_conj :=
        hkerMFDH1c ⟨zConjD, hzConjH1c⟩
      have hfix_eval := congrFun hfix (z : Dm)
      have hX_conj_eq :
          Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin k)) zConjD =
            Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin k)) (z : Dm) := by
        simpa [Section1.conjugateOnNormal, zConjD, zD, hz0_eq, ψlin] using hfix_eval
      exact hX_conj_eq.symm.trans hker_conj
    have hkerJoin :
        Section1.subgroupInKernel'
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k)))
          (MFDH1c ⊔ MFDH1) :=
      subgroupInKernel'_sup_of_irreducible_sec9 hinner hkerMFDH1c hkerMFDH1
    rw [← hMFDH_join]
    exact hkerJoin
  exact False.elim (hθnotMF k (by
    simpa [A, MFD, ψlin] using hkerMFD))

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 100000 in
private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_character_inj_Xtheta_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (_hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (_hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (_hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    let f : U →* ρBase.range :=
      ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
    let K : Subgroup U := f.ker
    let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
      theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
        U Uprime hUprimeEq
    let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
    letI : Hsub.Normal := hUprimeNormal.subgroupOf K
    let Clam : Type u := K ⧸ Hsub
    letI : Group Clam := inferInstance
    let hClamComm : IsMulCommutative Clam :=
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
        U C Uprime ρBase hUprimeEq
    let Lam : Type u := Clam →* ℂˣ
    let hf_surj : Function.Surjective f := by
      intro y
      rcases y with ⟨y, hy⟩
      rcases hy with ⟨x, rfl⟩
      rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
      exact ⟨u, rfl⟩
    letI : IsCyclic ρBase.range := hρcycBase
    letI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
    let σ : ρBase.range →* MulAut Clam :=
      mulAutHomInvOfCommDomain_sec9
        (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
          simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
    let instLamAction : MulAction ρBase.range Lam :=
      linearCharacterMulAction_sec9 σ
    let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
      Subgroup.subtype ρBase.range
    let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
      nonprincipalLinearCharacterIndexMulAction_sec9 p
        (hHcard ⟨0, hqpos⟩) ρRange
    letI : MulAction ρBase.range Lam := instLamAction
    letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
    let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
    let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
    ∀ (B : Subgroup Dm) (hBnormal : B.Normal) (hAnormal : A.Normal),
    ∀ (_hMFD_le_B : MFD ≤ B)
      (hBsemi : Section2.IsInternalSemidirectProduct B MFD (W ⊓ B))
      (eWBK : ↥(W ⊓ B) ≃* K)
      (_hWBK_compat :
        ∀ x : ↥(W ⊓ B),
          (((eWBK x : K) : U) : G) = ((((x : Dm) : M) : G))),
    letI : B.Normal := hBnormal
    letI : A.Normal := hAnormal
    letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
    let Q : Type u := B ⧸ A.subgroupOf B
    letI : Group Q := inferInstance
    ∀ (QH1c QH1 QClam QH1CH1 : Subgroup Q),
    ∀ (hsemi : Section2.IsInternalSemidirectProduct
        (⊤ : Subgroup Q) QH1c QH1CH1)
      (hprod : Section2.IsInternalDirectProduct QH1CH1 QH1 QClam)
      (eH1 : QH1 ≃* H ⟨0, hqpos⟩)
      (eClam : QClam ≃* Clam),
    let ψlin : Fin (p - 1) × Lam → Q →* ℂˣ := fun k =>
      semidirectProductOfInternalDirectProductLinearCharacter_sec9
        hsemi hprod
        (((nonprincipalLinearCharacterEquivFin_sec9
              (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1.comp
          eH1.toMonoidHom)
        (k.2.comp eClam.toMonoidHom)
    ∀ (_hQH1_apply :
        ∀ (m : MFD.subgroupOf B)
          (hmH1 :
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
              H ⟨0, hqpos⟩),
            ∃ hmQH1 : QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1,
              eH1 ⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ =
                ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                    (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                      ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)),
                  hmH1⟩)
      (_hQH1c_apply :
        ∀ m : MFD.subgroupOf B,
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
            (⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i) →
          QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1c)
      (_hQClam_apply :
        ∀ w : (W ⊓ B).subgroupOf B,
          ∃ hwQClam : QuotientGroup.mk' (A.subgroupOf B) w ∈ QClam,
            eClam ⟨QuotientGroup.mk' (A.subgroupOf B) w, hwQClam⟩ =
              QuotientGroup.mk' Hsub
                (eWBK
                  (⟨((w : B) : Dm), by
                    simpa [W, Subgroup.mem_subgroupOf] using w.property⟩ :
                    ↥(W ⊓ B)))),
    ∀ (_hIeq :
        ∀ k : Fin (p - 1) × Lam,
          Section1.inertiaSubgroup B
            (Section1.quotientCharacterInflation A B (ψlin k)) = B)
      (_hθnotMF :
        ∀ k : Fin (p - 1) × Lam,
          ¬ Section1.subgroupInKernel'
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin k))) MFD)
      (_hψlin_injective : Function.Injective ψlin)
      (_hpairStabilizer :
        ∀ k : Fin (p - 1) × Lam,
          MulAction.stabilizer ρBase.range k = ⊥),
    ∀ k l : Fin (p - 1) × Lam,
      Section1.inducedCF Dm
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k))) =
        Section1.inducedCF Dm
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin l))) →
      MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l := by
  classical
  dsimp
  intro B hBnormal hAnormal hMFD_le_B hBsemi eWBK hWBK_compat QH1c QH1 QClam
    QH1CH1 hsemi hprod eH1 eClam hQH1_apply hQH1c_apply hQClam_apply hIeq
    hθnotMF hψlin_injective hpairStabilizer
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let Lam : Type u := Clam →* ℂˣ
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
  let ψlin : Fin (p - 1) × Lam → (B ⧸ A.subgroupOf B) →* ℂˣ := fun k =>
    semidirectProductOfInternalDirectProductLinearCharacter_sec9
      hsemi hprod
      (((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1.comp
        eH1.toMonoidHom)
      (k.2.comp eClam.toMonoidHom)
  letI : B.Normal := hBnormal
  letI : A.Normal := hAnormal
  letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
  have hψirr :
      ∀ k : Fin (p - 1) × Lam,
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.quotientCharacterInflation A B (ψlin k)) := by
    intro k
    exact Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      A B (ψlin k)
  have hinner_irr :
      ∀ k : Fin (p - 1) × Lam,
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k))) := by
    intro k
    exact inducedCF_isIrreducible_of_inertia_eq_self_sec9 B (hψirr k) (by
      simpa [ψlin] using hIeq k)
  have houter_to_inner :
      ∀ k l : Fin (p - 1) × Lam,
        Section1.inducedCF Dm
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin k))) =
          Section1.inducedCF Dm
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin l))) →
        Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k)) =
          Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin l)) := by
    have hDnormal : Dm.Normal := by
      simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
    letI : Dm.Normal := hDnormal
    have hMFDnormal : MFD.Normal := by
      simpa [MFD, Dm] using
        theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
          M MF U W1 W2 H0 C p q a hcase
    letI : MFD.Normal := hMFDnormal
    have hsemiTop :
        Section2.IsInternalSemidirectProduct (⊤ : Subgroup Dm) MFD W := by
      simpa [MFD, W, Dm] using
        theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
          M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase) hMFDnormal
    have hcomp : Dm.IsComplement' (W1.subgroupOf M) := by
      dsimp [Dm]
      exact ambientDerived_W1_isComplement'_subgroupOf_M_of_hypothesis_9_2_sec9
        M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
    have hsemiM :
        Section2.IsInternalSemidirectProduct (⊤ : Subgroup M) Dm (W1.subgroupOf M) :=
      internalSemidirectProduct_top_of_normal_isComplement'_sec9 hcomp
    have hinner_class :
        ∀ r : Fin (p - 1) × Lam,
          Section1.IsClassFunction
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin r))) := by
      intro r
      exact Section1.inducedCF_isClassFunction B
        (Section1.quotientCharacterInflation A B (ψlin r))
    intro k l hInd
    rcases induced_eq_imp_conjugateOrbitConj_of_irreducible_sec9
        Dm (hinner_irr k) (hinner_irr l) hInd with ⟨i, hi⟩
    revert hi
    refine Quotient.inductionOn i ?_
    intro g hi
    have hconjG :
        Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k)) =
          Section1.conjugateOnNormal Dm
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin l))) g := by
      simpa [Section1.conjugateOrbitConj] using hi
    rcases hsemiM.mul_surjective g (by trivial) with ⟨d0, hd0, w0, hw0, hg⟩
    have hconjW :
        Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k)) =
          Section1.conjugateOnNormal Dm
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin l))) w0 := by
      have hconjMW :
          Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin k)) =
            Section1.conjugateOnNormal Dm
              (Section1.inducedCF B
                (Section1.quotientCharacterInflation A B (ψlin l))) (d0 * w0) := by
        simpa [hg] using hconjG
      have herase :
          Section1.conjugateOnNormal Dm
              (Section1.inducedCF B
                (Section1.quotientCharacterInflation A B (ψlin l))) (d0 * w0) =
            Section1.conjugateOnNormal Dm
              (Section1.inducedCF B
                (Section1.quotientCharacterInflation A B (ψlin l))) w0 :=
        conjugateOnNormal_mul_left_of_mem_sec9
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin l))) (hinner_class l) hd0
      exact hconjMW.trans herase
    have hw0_eq : w0 = 1 := by
      by_contra hw0_ne
      have hkerMFD :
          Section1.subgroupInKernel'
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin k))) MFD := by
        have hsourceKerQH1c :
            ∀ r : Fin (p - 1) × Lam,
              ∀ b : B,
                QuotientGroup.mk' (A.subgroupOf B) b ∈ QH1c →
                  Section1.quotientCharacterInflation A B (ψlin r) b =
                    Section1.degree
                      (Section1.quotientCharacterInflation A B (ψlin r)) := by
          intro r b hb
          let χbase : H ⟨0, hqpos⟩ →* ℂˣ :=
            ((nonprincipalLinearCharacterEquivFin_sec9
                (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) r.1).1
          let χQH1 : QH1 →* ℂˣ := χbase.comp eH1.toMonoidHom
          let ηQClam : QClam →* ℂˣ := r.2.comp eClam.toMonoidHom
          let qh : QH1c := ⟨QuotientGroup.mk' (A.subgroupOf B) b, hb⟩
          have hproj :
              internalSemidirectRightProjectionTop_sec9 hsemi
                  (QuotientGroup.mk' (A.subgroupOf B) b) = 1 := by
            simpa [qh] using
              internalSemidirectRightProjectionTop_apply_left_sec9 hsemi qh
          have hψ :
              ψlin r (QuotientGroup.mk' (A.subgroupOf B) b) = 1 := by
            calc
              ψlin r (QuotientGroup.mk' (A.subgroupOf B) b) =
                  Section3.internalDirectProductLinearCharacter hprod χQH1 ηQClam
                    (internalSemidirectRightProjectionTop_sec9 hsemi
                      (QuotientGroup.mk' (A.subgroupOf B) b)) := by
                    rfl
              _ = Section3.internalDirectProductLinearCharacter hprod χQH1 ηQClam 1 := by
                    rw [hproj]
              _ = 1 := by simp
          rw [Section1.quotientCharacterInflation_degree]
          simpa [Section1.quotientCharacterInflation, hψ]
        let w0W1 : W1 := ⟨(w0 : G), by
          simpa [Subgroup.mem_subgroupOf] using hw0⟩
        have hw0W1_ne : w0W1 ≠ 1 := by
          intro hw1
          apply hw0_ne
          ext
          exact congrArg (fun x : W1 => (x : G)) hw1
        let w0W1inv : W1 := w0W1⁻¹
        have hw0W1inv_ne : w0W1inv ≠ 1 := by
          intro hw1
          exact hw0W1_ne (inv_eq_one.mp hw1)
        rcases theorem_9_8_weak_orbit_nonidentity_moves_base_sec9
            H hqpos hHcard hHnorm hHindep hconjBase hcase w0W1inv hw0W1inv_ne with
          ⟨iMove, hiMove_ne, hbase_to_iMove⟩
        let H1cMF : Subgroup (MF ⧸ H0.subgroupOf MF) :=
          ⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i
        rcases hbase_to_iMove with
          ⟨hconjMF_move, actionMove, hactionMove, htargetMove⟩
        have hbase_conj_mem_H1c :
            ∀ m : MF,
              QuotientGroup.mk' (H0.subgroupOf MF) m ∈ H ⟨0, hqpos⟩ →
                QuotientGroup.mk' (H0.subgroupOf MF)
                    ⟨(w0 : G) * (m : G) * (w0 : G)⁻¹, by
                      simpa [w0W1inv, w0W1] using hconjMF_move m⟩ ∈ H1cMF := by
          intro m hmBase
          have htarget_mem :
              actionMove (QuotientGroup.mk' (H0.subgroupOf MF) m) ∈ H iMove := by
            rw [htargetMove]
            exact ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase, rfl⟩
          have hcoord :
              actionMove (QuotientGroup.mk' (H0.subgroupOf MF) m) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(w0 : G) * (m : G) * (w0 : G)⁻¹, by
                    simpa [w0W1inv, w0W1] using hconjMF_move m⟩ := by
            simpa [w0W1inv, w0W1] using hactionMove m
          rw [hcoord] at htarget_mem
          exact
            Subgroup.mem_iSup_of_mem iMove
              (Subgroup.mem_iSup_of_mem hiMove_ne htarget_mem)
        let qMFD : MFD →* (MF ⧸ H0.subgroupOf MF) :=
          (QuotientGroup.mk' (H0.subgroupOf MF)).comp
            (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF)
        let MFDH1cSub : Subgroup MFD := H1cMF.comap qMFD
        let MFDH1Sub : Subgroup MFD := (H ⟨0, hqpos⟩).comap qMFD
        let MFDH1c : Subgroup Dm := MFDH1cSub.map MFD.subtype
        let MFDH1 : Subgroup Dm := MFDH1Sub.map MFD.subtype
        have hMFleD : MF ≤ ambientDerivedSubgroup M :=
          MF_le_ambientDerived_of_hypothesis_9_2_sec9
            M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
        have hDleM : ambientDerivedSubgroup M ≤ M :=
          section12_ambientDerivedSubgroup_le (E := M)
        have hqMFD_surj : Function.Surjective qMFD := by
          intro x
          rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨mMF, rfl⟩
          let mM : M := ⟨(mMF : G), hDleM (hMFleD mMF.property)⟩
          let mD : Dm := ⟨mM, by
            simpa [Dm, Subgroup.mem_subgroupOf, mM] using hMFleD mMF.property⟩
          let mMFD : MFD := ⟨mD, by
            change (mD : M) ∈ MF.subgroupOf M
            simp [mD, mM, Subgroup.mem_subgroupOf]⟩
          exact ⟨mMFD, rfl⟩
        have hMF_Hsplit :
            Section2.IsInternalDirectProduct
              (⊤ : Subgroup (MF ⧸ H0.subgroupOf MF)) H1cMF (H ⟨0, hqpos⟩) := by
          simpa [H1cMF] using
            theorem_9_8_iSup_split_base_internalDirectProduct_sec9
              H ⟨0, hqpos⟩ hHindep hHsup
        have hMF_Hsplit_sup : H1cMF ⊔ H ⟨0, hqpos⟩ = ⊤ := by
          apply top_unique
          intro x _hx
          rcases hMF_Hsplit.mul_surjective x (by trivial) with ⟨h1c, hh1c, h1, hh1, hx⟩
          rw [hx]
          exact (H1cMF ⊔ H ⟨0, hqpos⟩).mul_mem
            (Subgroup.mem_sup_left hh1c) (Subgroup.mem_sup_right hh1)
        have hMFD_coord_sup : MFDH1cSub ⊔ MFDH1Sub = ⊤ := by
          have hle_range_H1c : H1cMF ≤ qMFD.range := by
            rw [MonoidHom.range_eq_top.mpr hqMFD_surj]
            exact le_top
          have hle_range_H1 : H ⟨0, hqpos⟩ ≤ qMFD.range := by
            rw [MonoidHom.range_eq_top.mpr hqMFD_surj]
            exact le_top
          calc
            MFDH1cSub ⊔ MFDH1Sub =
                (H1cMF ⊔ H ⟨0, hqpos⟩).comap qMFD := by
                  simpa [MFDH1cSub, MFDH1Sub] using
                    Subgroup.comap_sup_eq_of_le_range qMFD hle_range_H1c hle_range_H1
            _ = ⊤ := by
                  rw [hMF_Hsplit_sup]
                  rfl
        have hMFD_map_top : (⊤ : Subgroup MFD).map MFD.subtype = MFD := by
          ext x
          constructor
          · intro hx
            rcases hx with ⟨y, _hy, hyx⟩
            rw [← hyx]
            exact y.property
          · intro hx
            exact ⟨⟨x, hx⟩, trivial, rfl⟩
        have hMFDH_join : MFDH1c ⊔ MFDH1 = MFD := by
          calc
            MFDH1c ⊔ MFDH1 =
                (MFDH1cSub ⊔ MFDH1Sub).map MFD.subtype := by
                  rw [Subgroup.map_sup]
            _ = (⊤ : Subgroup MFD).map MFD.subtype := by rw [hMFD_coord_sup]
            _ = MFD := hMFD_map_top
        have hH1cMF_norm_U : quotientSubgroupNormalizedBy MF H0 U H1cMF := by
          intro aU
          rcases hHnorm ⟨0, hqpos⟩ aU with ⟨hconjMF, action, haction, _hmapBase⟩
          refine ⟨hconjMF, action, haction, ?_⟩
          have hmap_each :
              ∀ i : Fin q, (H i).map action.toMonoidHom = H i := by
            intro i
            rcases hHnorm i aU with ⟨hconjMF_i, action_i, haction_i, hmap_i⟩
            have haction_eq : action_i = action := by
              ext x
              rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨h, rfl⟩
              calc
                action_i (QuotientGroup.mk' (H0.subgroupOf MF) h) =
                    QuotientGroup.mk' (H0.subgroupOf MF)
                      ⟨(aU : G)⁻¹ * (h : G) * (aU : G), hconjMF_i h⟩ := haction_i h
                _ = QuotientGroup.mk' (H0.subgroupOf MF)
                      ⟨(aU : G)⁻¹ * (h : G) * (aU : G), hconjMF h⟩ := by
                      congr 1
                _ = action (QuotientGroup.mk' (H0.subgroupOf MF) h) := (haction h).symm
            simpa [haction_eq] using hmap_i.symm
          have hmap_sup : H1cMF.map action.toMonoidHom = H1cMF := by
            simp_rw [H1cMF, Subgroup.map_iSup, hmap_each]
          exact hmap_sup.symm
        have hMFDH1c_le_MFD : MFDH1c ≤ MFD := by
          intro x hx
          rcases hx with ⟨y, _hy, hyx⟩
          rw [← hyx]
          exact y.property
        have hMFDH1c_le_B : MFDH1c ≤ B :=
          hMFDH1c_le_MFD.trans hMFD_le_B
        have hMFDH1c_normal : MFDH1c.Normal := by
          refine Subgroup.Normal.mk ?_
          intro n hn x
          rcases hn with ⟨n0, hn0H1c, hn0_eq⟩
          have hnMFD : n ∈ MFD := by
            rw [← hn0_eq]
            exact n0.property
          let conjMFD : MFD := ⟨x * n * x⁻¹, hMFDnormal.conj_mem n hnMFD x⟩
          refine ⟨conjMFD, ?_, rfl⟩
          rcases hsemiTop.mul_surjective x (by trivial) with ⟨m, hm, w, hw, hxmw⟩
          let mMFD : MFD := ⟨m, hm⟩
          let wU : U := ⟨(((w : Dm) : M) : G), by
            have hwUM : ((w : Dm) : M) ∈ U.subgroupOf M := by
              simpa [W, Dm, Subgroup.mem_subgroupOf] using hw
            simpa [Subgroup.mem_subgroupOf] using hwUM⟩
          let wConjMFD : MFD :=
            ⟨w * n * w⁻¹, hsemiTop.right_normalizes_left w hw n hnMFD⟩
          have hq_wConj_mem : qMFD wConjMFD ∈ H1cMF := by
            rcases hH1cMF_norm_U (wU⁻¹) with
              ⟨hconjMF, action, haction, hmap⟩
            have hmem_action : action (qMFD n0) ∈ H1cMF := by
              rw [hmap]
              exact Subgroup.mem_map_of_mem action.toMonoidHom (by
                simpa [MFDH1cSub] using hn0H1c)
            have hcoord : action (qMFD n0) = qMFD wConjMFD := by
              let nMF : MF := theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF n0
              have hact := haction nMF
              have hrhs :
                  QuotientGroup.mk' (H0.subgroupOf MF)
                      (⟨(((wU⁻¹ : U) : G))⁻¹ * (nMF : G) * ((wU⁻¹ : U) : G),
                        hconjMF nMF⟩ : MF) =
                    QuotientGroup.mk' (H0.subgroupOf MF)
                      (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF wConjMFD) := by
                congr 1
                apply Subtype.ext
                simpa [theorem_9_8_MFDSubgroupOf_to_MF_sec9, nMF, wConjMFD, wU,
                  hn0_eq, mul_assoc]
              calc
                action (qMFD n0) =
                    QuotientGroup.mk' (H0.subgroupOf MF)
                      (⟨(((wU⁻¹ : U) : G))⁻¹ * (nMF : G) * ((wU⁻¹ : U) : G),
                        hconjMF nMF⟩ : MF) := by
                      simpa [qMFD, nMF] using hact
                _ = qMFD wConjMFD := by
                      simpa [qMFD] using hrhs
            rwa [hcoord] at hmem_action
          have hH1c_normal : H1cMF.Normal := by
            refine Subgroup.Normal.mk ?_
            intro n hn g
            have h : g * n * g⁻¹ = n := by
              simp [mul_assoc, mul_comm]
            simpa [h] using hn
          have hconj_eq :
              conjMFD = mMFD * wConjMFD * mMFD⁻¹ := by
            apply Subtype.ext
            simp [conjMFD, mMFD, wConjMFD, hxmw, mul_assoc]
          rw [hconj_eq]
          change qMFD (mMFD * wConjMFD * mMFD⁻¹) ∈ H1cMF
          simpa [map_mul, map_inv, mul_assoc] using
            hH1c_normal.conj_mem (qMFD wConjMFD) hq_wConj_mem (qMFD mMFD)
        letI : MFDH1c.Normal := hMFDH1c_normal
        have hsourceKerMFDH1c :
            ∀ r : Fin (p - 1) × Lam,
              Section1.subgroupInKernel'
                (Section1.quotientCharacterInflation A B (ψlin r))
                (MFDH1c.subgroupOf B) := by
          intro r a
          have haMFDH1c : ((a : B) : Dm) ∈ MFDH1c := by
            exact Subgroup.mem_subgroupOf.mp a.property
          rcases haMFDH1c with ⟨y, hyH1c, hy_eq⟩
          have haMFD : ((a : B) : Dm) ∈ MFD := by
            rw [← hy_eq]
            exact y.property
          let mSub : MFD.subgroupOf B := ⟨a, by
            simpa [Subgroup.mem_subgroupOf] using haMFD⟩
          have hy_mSub :
              y = (Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub := by
            apply Subtype.ext
            simpa [mSub, Subgroup.subgroupOfEquivOfLe] using hy_eq
          have hmH1c :
              QuotientGroup.mk' (H0.subgroupOf MF)
                  (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                    ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub)) ∈
                H1cMF := by
            have hycoord : qMFD y ∈ H1cMF := by
              simpa [MFDH1cSub] using hyH1c
            simpa [qMFD, hy_mSub] using hycoord
          have hmQH1c :
              QuotientGroup.mk' (A.subgroupOf B) mSub ∈ QH1c :=
            hQH1c_apply mSub hmH1c
          simpa [mSub] using hsourceKerQH1c r a hmQH1c
        have hkerMFDH1c :
            ∀ r : Fin (p - 1) × Lam,
              Section1.subgroupInKernel'
                (Section1.inducedCF B
                  (Section1.quotientCharacterInflation A B (ψlin r))) MFDH1c := by
          intro r
          exact subgroupInKernel'_inducedCF_of_subgroupInKernel'_sec9
            B MFDH1c hMFDH1c_le_B (hψirr r) (hsourceKerMFDH1c r)
        have hkerMFDH1 :
            Section1.subgroupInKernel'
              (Section1.inducedCF B
                (Section1.quotientCharacterInflation A B (ψlin k))) MFDH1 := by
          intro z
          rcases z.property with ⟨z0, hz0H1, hz0_eq⟩
          let zD : Dm := MFD.subtype z0
          let zMF : MF := theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF z0
          have hz0Base :
              QuotientGroup.mk' (H0.subgroupOf MF) zMF ∈ H ⟨0, hqpos⟩ := by
            simpa [MFDH1Sub, qMFD, zMF] using hz0H1
          let zConjD : Dm :=
            ⟨(w0 : M) * (zD : M) * (w0 : M)⁻¹,
              hDnormal.conj_mem (zD : M) zD.property w0⟩
          have hzConjMFD : zConjD ∈ MFD := by
            change (zConjD : M) ∈ MF.subgroupOf M
            have hzMFconj := hconjMF_move zMF
            simpa [zConjD, zD, zMF, w0W1inv, w0W1,
              theorem_9_8_MFDSubgroupOf_to_MF_sec9,
              Subgroup.mem_subgroupOf, mul_assoc] using hzMFconj
          let zConjMFD : MFD := ⟨zConjD, hzConjMFD⟩
          have hzConjH1cSub : zConjMFD ∈ MFDH1cSub := by
            have hzcoord := hbase_conj_mem_H1c zMF hz0Base
            simpa [MFDH1cSub, qMFD, zConjMFD, zConjD, zD, zMF,
              theorem_9_8_MFDSubgroupOf_to_MF_sec9, mul_assoc] using hzcoord
          have hzConjH1c : zConjD ∈ MFDH1c :=
            ⟨zConjMFD, hzConjH1cSub, rfl⟩
          have hker_conj :=
            hkerMFDH1c l ⟨zConjD, hzConjH1c⟩
          have hdegree_lk :
              Section1.degree
                    (Section1.inducedCF B
                      (Section1.quotientCharacterInflation A B (ψlin l))) =
                Section1.degree
                    (Section1.inducedCF B
                      (Section1.quotientCharacterInflation A B (ψlin k))) := by
            have hdegree_kl :
                Section1.degree
                    (Section1.inducedCF B
                      (Section1.quotientCharacterInflation A B (ψlin k))) =
                  Section1.degree
                    (Section1.inducedCF B
                      (Section1.quotientCharacterInflation A B (ψlin l))) := by
              have hdegree_conj :
                  Section1.degree
                      (Section1.conjugateOnNormal Dm
                        (Section1.inducedCF B
                          (Section1.quotientCharacterInflation A B (ψlin l))) w0) =
                    Section1.degree
                      (Section1.inducedCF B
                        (Section1.quotientCharacterInflation A B (ψlin l))) := by
                unfold Section1.degree Section1.conjugateOnNormal
                exact congrArg
                  (Section1.inducedCF B
                    (Section1.quotientCharacterInflation A B (ψlin l)))
                  (Subtype.ext (by simp))
              exact (congrArg Section1.degree hconjW).trans hdegree_conj
            exact hdegree_kl.symm
          have hconj_eval := congrFun hconjW (z : Dm)
          have hX_conj_eq :
              Section1.inducedCF B
                  (Section1.quotientCharacterInflation A B (ψlin k)) (z : Dm) =
                Section1.inducedCF B
                  (Section1.quotientCharacterInflation A B (ψlin l)) zConjD := by
            simpa [Section1.conjugateOnNormal, zConjD, zD, hz0_eq] using hconj_eval
          exact (hX_conj_eq.trans hker_conj).trans hdegree_lk
        have hkerJoin :
            Section1.subgroupInKernel'
              (Section1.inducedCF B
                (Section1.quotientCharacterInflation A B (ψlin k)))
              (MFDH1c ⊔ MFDH1) :=
          subgroupInKernel'_sup_of_irreducible_sec9 (hinner_irr k)
            (hkerMFDH1c k) hkerMFDH1
        rw [← hMFDH_join]
        exact hkerJoin
      exact False.elim (hθnotMF k (by
        simpa [MFD, A, ψlin] using hkerMFD))
    have hconjW_one :
        Section1.conjugateOnNormal Dm
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin l))) w0 =
          Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin l)) := by
      funext x
      simp [hw0_eq, Section1.conjugateOnNormal]
    exact hconjW.trans hconjW_one
  have hinner_orbit :
      ∀ k l : Fin (p - 1) × Lam,
        Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k)) =
          Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin l)) →
        MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l := by
    have hMFDnormal : MFD.Normal := by
      simpa [MFD, Dm] using
        theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
          M MF U W1 W2 H0 C p q a hcase
    letI : MFD.Normal := hMFDnormal
    have hsemiTop :
        Section2.IsInternalSemidirectProduct (⊤ : Subgroup Dm) MFD W := by
      simpa [MFD, W, Dm] using
        theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
          M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase) hMFDnormal
    have hsource_class :
        ∀ r : Fin (p - 1) × Lam,
          Section1.IsClassFunction
            (Section1.quotientCharacterInflation A B (ψlin r)) := by
      intro r
      exact Section1.quotientCharacterInflation_isClassFunction A B (ψlin r)
    have hfirst_of_conj :
        ∀ (k l : Fin (p - 1) × Lam) (u0 : Dm) (uU : U),
          (((u0 : Dm) : M) : G) = (uU : G) →
          Section1.quotientCharacterInflation A B (ψlin k) =
            Section1.conjugateOnNormal B
              (Section1.quotientCharacterInflation A B (ψlin l)) u0 →
          k.1 = (f uU • l).1 := by
      intro k l u0 uU hu0 hconj
      change k.1 = f uU • l.1
      let χbaseK : H ⟨0, hqpos⟩ →* ℂˣ :=
        ((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1
      let χbaseL : H ⟨0, hqpos⟩ →* ℂˣ :=
        ((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) l.1).1
      let χbaseAction : H ⟨0, hqpos⟩ →* ℂˣ :=
        ((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) (f uU • l.1)).1
      have hχbase_action :
          χbaseAction = χbaseL.comp (ρRange (f uU)).symm.toMonoidHom := by
        simpa [χbaseL, χbaseAction, ρRange, instFirstAction] using
          nonprincipalLinearCharacterIndexMulAction_spec_sec9
            p (hHcard ⟨0, hqpos⟩) ρRange (f uU) l.1
      have hχ : χbaseK = χbaseAction := by
        ext x
        have hMFleD : MF ≤ ambientDerivedSubgroup M :=
          MF_le_ambientDerived_of_hypothesis_9_2_sec9
            M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
        have hDleM : ambientDerivedSubgroup M ≤ M :=
          section12_ambientDerivedSubgroup_le (E := M)
        rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF)
            (x : MF ⧸ H0.subgroupOf MF) with
          ⟨mMF, hmMFx⟩
        let mM : M := ⟨(mMF : G), hDleM (hMFleD mMF.property)⟩
        let mD : Dm := ⟨mM, by
          simpa [Dm, Subgroup.mem_subgroupOf, mM] using hMFleD mMF.property⟩
        have hmD_MFD : mD ∈ MFD := by
          change (mD : M) ∈ MF.subgroupOf M
          simp [mD, mM, Subgroup.mem_subgroupOf]
        let mB : B := ⟨mD, hMFD_le_B hmD_MFD⟩
        have hmB_MFDsub : mB ∈ MFD.subgroupOf B := by
          simpa [MFD, Subgroup.mem_subgroupOf, mB] using hmD_MFD
        let mSub : MFD.subgroupOf B := ⟨mB, hmB_MFDsub⟩
        have hmRaw_eq :
            theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub) =
              mMF := by
          apply Subtype.ext
          rfl
        have hmH1 :
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub)) ∈
              H ⟨0, hqpos⟩ := by
          rw [hmRaw_eq, hmMFx]
          exact x.property
        rcases hQH1_apply mSub hmH1 with ⟨hmQH1, hcoord⟩
        let y : QH1 := ⟨QuotientGroup.mk' (A.subgroupOf B) mB, hmQH1⟩
        have hcoord_x : eH1 y = x := by
          calc
            eH1 y =
                ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                    (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                      ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub)),
                  hmH1⟩ := by
                    simpa [y, mSub] using hcoord
            _ = x := by
                    apply Subtype.ext
                    simpa [hmRaw_eq] using hmMFx
        have hk_eval :
            ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) = χbaseK x := by
          have hcomp := congrArg (fun φ : QH1 →* ℂˣ => φ y)
            (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
              hsemi hprod
              (χbaseK.comp eH1.toMonoidHom)
              (k.2.comp eClam.toMonoidHom))
          calc
            ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) =
                (χbaseK.comp eH1.toMonoidHom) y := by
                  simpa [ψlin, χbaseK, y] using hcomp
            _ = χbaseK x := by
                  simp [MonoidHom.comp_apply, hcoord_x]
        have hu0W : u0 ∈ W := by
          change ((u0 : Dm) : M) ∈ U.subgroupOf M
          simp [Subgroup.mem_subgroupOf, hu0]
        have hconjMFD : Section2.conjBy u0 mD ∈ MFD :=
          hsemiTop.right_normalizes_left u0 hu0W mD hmD_MFD
        let mConjB : B := ⟨Section2.conjBy u0 mD, hMFD_le_B hconjMFD⟩
        have hmConjB_MFDsub : mConjB ∈ MFD.subgroupOf B := by
          simpa [MFD, Subgroup.mem_subgroupOf, mConjB] using hconjMFD
        let mConjSub : MFD.subgroupOf B := ⟨mConjB, hmConjB_MFDsub⟩
        rcases hρactionBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹))
            (uU⁻¹) rfl with
          ⟨hconjMF, haction⟩
        let xFromM : H ⟨0, hqpos⟩ :=
          ⟨QuotientGroup.mk' (H0.subgroupOf MF) mMF, by
            rw [hmMFx]
            exact x.property⟩
        have hxFromM : xFromM = x := by
          apply Subtype.ext
          exact hmMFx
        let conjMF : MF :=
          ⟨((uU : G) * (mMF : G) * (uU : G)⁻¹), by
            simpa using hconjMF mMF⟩
        have hsymm_apply :
            ((ρRange (f uU)).symm x : MF ⧸ H0.subgroupOf MF) =
              (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) x :
                MF ⧸ H0.subgroupOf MF) := by
          simp [ρRange, f]
        have hact_x :
            (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) x :
                MF ⧸ H0.subgroupOf MF) =
              QuotientGroup.mk' (H0.subgroupOf MF) conjMF := by
          have hact := haction mMF xFromM.property
          have hact' :
              (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) xFromM :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF) conjMF := by
            simpa [xFromM, conjMF, mul_assoc] using hact
          simpa [hxFromM] using hact'
        have hmConjRaw_eq :
            theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub) =
              conjMF := by
          apply Subtype.ext
          simp [mConjSub, mConjB, mD, mM, conjMF, Section2.conjBy,
            theorem_9_8_MFDSubgroupOf_to_MF_sec9, hu0, mul_assoc]
        have hconjCoord :
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)) =
              ((ρRange (f uU)).symm x : MF ⧸ H0.subgroupOf MF) := by
          calc
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)) =
                QuotientGroup.mk' (H0.subgroupOf MF) conjMF := by
                  rw [hmConjRaw_eq]
            _ = (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) x :
                  MF ⧸ H0.subgroupOf MF) := hact_x.symm
            _ = ((ρRange (f uU)).symm x : MF ⧸ H0.subgroupOf MF) :=
                  hsymm_apply.symm
        have hmConjH1 :
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)) ∈
              H ⟨0, hqpos⟩ := by
          rw [hconjCoord]
          exact ((ρRange (f uU)).symm x).property
        rcases hQH1_apply mConjSub hmConjH1 with
          ⟨hmConjQH1, hcoordConj⟩
        let yConj : QH1 :=
          ⟨QuotientGroup.mk' (A.subgroupOf B) mConjB, hmConjQH1⟩
        have hcoordConj_x : eH1 yConj = (ρRange (f uU)).symm x := by
          calc
            eH1 yConj =
                ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                    (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                      ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)),
                  hmConjH1⟩ := by
                    simpa [yConj, mConjSub] using hcoordConj
            _ = (ρRange (f uU)).symm x := by
                    apply Subtype.ext
                    exact hconjCoord
        have hl_eval :
            ψlin l (QuotientGroup.mk' (A.subgroupOf B) mConjB) =
              χbaseAction x := by
          have hcomp := congrArg (fun φ : QH1 →* ℂˣ => φ yConj)
            (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
              hsemi hprod
              (χbaseL.comp eH1.toMonoidHom)
              (l.2.comp eClam.toMonoidHom))
          have hχapply := congrArg (fun φ : H ⟨0, hqpos⟩ →* ℂˣ => φ x)
            hχbase_action
          calc
            ψlin l (QuotientGroup.mk' (A.subgroupOf B) mConjB) =
                (χbaseL.comp eH1.toMonoidHom) yConj := by
                  simpa [ψlin, χbaseL, yConj] using hcomp
            _ = χbaseL ((ρRange (f uU)).symm x) := by
                  simp [MonoidHom.comp_apply, hcoordConj_x]
            _ = χbaseAction x := by
                  simpa [MonoidHom.comp_apply] using hχapply.symm
        have hconj_units :
            ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) =
              ψlin l (QuotientGroup.mk' (A.subgroupOf B) mConjB) := by
          apply Units.ext
          have hconj_val := congrFun hconj mB
          change
            ((ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) : ℂˣ) : ℂ) =
              ((ψlin l (QuotientGroup.mk' (A.subgroupOf B) mConjB) : ℂˣ) : ℂ)
          simpa [Section1.conjugateOnNormal, Section1.quotientCharacterInflation,
            mConjB, mB, mD, Section2.conjBy, mul_assoc] using hconj_val
        exact congrArg Units.val (by
          calc
            (χbaseK x : ℂˣ) = ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) :=
              hk_eval.symm
            _ = ψlin l (QuotientGroup.mk' (A.subgroupOf B) mConjB) := hconj_units
            _ = χbaseAction x := hl_eval)
      let e := nonprincipalLinearCharacterEquivFin_sec9
        (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)
      apply e.injective
      apply Subtype.ext
      exact hχ
    have hlam_of_conj :
        ∀ (k l : Fin (p - 1) × Lam) (u0 : Dm) (uU : U),
          (((u0 : Dm) : M) : G) = (uU : G) →
          Section1.quotientCharacterInflation A B (ψlin k) =
            Section1.conjugateOnNormal B
              (Section1.quotientCharacterInflation A B (ψlin l)) u0 →
          k.2 = (f uU • l).2 := by
      intro k l u0 uU hu0 hconj
      have hClamComm : IsMulCommutative Clam :=
        theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
          U C Uprime ρBase hUprimeEq
      have hf_surj : Function.Surjective f := by
        intro y
        rcases y with ⟨y, hy⟩
        rcases hy with ⟨x, rfl⟩
        rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
        exact ⟨u, rfl⟩
      haveI : IsCyclic ρBase.range := hρcycBase
      haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
      let σ0 : ρBase.range →* MulAut Clam :=
        kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
          simpa [Clam, Hsub, K, f] using hClamComm) hf_surj
      have hLamAction :
          f uU • l.2 = l.2.comp (σ0 (f uU)).toMonoidHom := by
        have hspec :=
          linearCharacterMulAction_spec_sec9
            (mulAutHomInvOfCommDomain_sec9 σ0) (f uU) l.2
        simpa [σ0, linearCharacterMulAction_sec9, mulAutHomInvOfCommDomain_sec9,
          Clam, Hsub, K, f] using hspec
      change k.2 = f uU • l.2
      rw [hLamAction]
      ext xK
      let wWB : ↥(W ⊓ B) := eWBK.symm xK
      let wB : B := ⟨(wWB : Dm), wWB.property.2⟩
      have hwB_mem : wB ∈ (W ⊓ B).subgroupOf B := by
        exact (Subgroup.mem_subgroupOf (H := W ⊓ B) (K := B)).mpr (by
          simp [wB])
      let wSub : (W ⊓ B).subgroupOf B := ⟨wB, hwB_mem⟩
      rcases hQClam_apply wSub with ⟨hwQClam, hwCoord⟩
      let y : QClam :=
        ⟨QuotientGroup.mk' (A.subgroupOf B) wB, by
          simpa [wSub] using hwQClam⟩
      have hwSub_eq :
          (⟨((wSub : B) : Dm), by
              simpa [W, Subgroup.mem_subgroupOf] using wSub.property⟩ :
            ↥(W ⊓ B)) = wWB := by
        ext
        rfl
      have hy_coord :
          eClam y = QuotientGroup.mk' Hsub xK := by
        calc
          eClam y =
              QuotientGroup.mk' Hsub
                (eWBK
                  (⟨((wSub : B) : Dm), by
                    simpa [W, Subgroup.mem_subgroupOf] using wSub.property⟩ :
                    ↥(W ⊓ B))) := by
              simpa [y, wSub] using hwCoord
          _ = QuotientGroup.mk' Hsub xK := by
              simp [hwSub_eq, wWB]
      let χk : H ⟨0, hqpos⟩ →* ℂˣ :=
        ((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1
      let χl : H ⟨0, hqpos⟩ →* ℂˣ :=
        ((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) l.1).1
      have hk_eval :
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) wB) =
            k.2 (QuotientGroup.mk' Hsub xK) := by
        have hcomp := congrArg (fun φ : QClam →* ℂˣ => φ y)
          (semidirectProductOfInternalDirectProductLinearCharacter_comp_right_sec9
            hsemi hprod
            (χk.comp eH1.toMonoidHom)
            (k.2.comp eClam.toMonoidHom))
        calc
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) wB) =
              (k.2.comp eClam.toMonoidHom) y := by
                simpa [ψlin, χk, y] using hcomp
          _ = k.2 (QuotientGroup.mk' Hsub xK) := by
                simp [MonoidHom.comp_apply, hy_coord]
      have hu0W : u0 ∈ W := by
        change ((u0 : Dm) : M) ∈ U.subgroupOf M
        simp [Subgroup.mem_subgroupOf, hu0]
      let wConjB : B :=
        ⟨u0 * (wB : Dm) * u0⁻¹,
          hBnormal.conj_mem (wB : Dm) wB.property u0⟩
      have hwConjW : (wConjB : Dm) ∈ W := by
        have hwW : (wB : Dm) ∈ W := by
          simpa [wB] using wWB.property.1
        simpa [wConjB, mul_assoc] using
          W.mul_mem (W.mul_mem hu0W hwW) (W.inv_mem hu0W)
      let wConjWB : ↥(W ⊓ B) := ⟨(wConjB : Dm), ⟨hwConjW, wConjB.property⟩⟩
      have hwConjB_mem : wConjB ∈ (W ⊓ B).subgroupOf B := by
        simpa [wConjWB, Subgroup.mem_subgroupOf]
      let wConjSub : (W ⊓ B).subgroupOf B := ⟨wConjB, hwConjB_mem⟩
      rcases hQClam_apply wConjSub with ⟨hwConjQClam, hwConjCoord⟩
      let yConj : QClam :=
        ⟨QuotientGroup.mk' (A.subgroupOf B) wConjB, by
          simpa [wConjSub] using hwConjQClam⟩
      have hwConjSub_eq :
          (⟨((wConjSub : B) : Dm), by
              simpa [W, Subgroup.mem_subgroupOf] using wConjSub.property⟩ :
            ↥(W ⊓ B)) = wConjWB := by
        ext
        rfl
      let xConjK : K :=
        ⟨uU * (xK : U) * uU⁻¹,
          (inferInstance : K.Normal).conj_mem (xK : U) xK.property uU⟩
      have hxK_compat :
          (((xK : K) : U) : G) = (((wWB : ↥(W ⊓ B)) : Dm) : M) := by
        simpa [wWB] using hWBK_compat wWB
      have hwConj_compat :
          ((((wConjWB : ↥(W ⊓ B)) : Dm) : M) : G) =
            (uU : G) * (((xK : K) : U) : G) * (uU : G)⁻¹ := by
        calc
          ((((wConjWB : ↥(W ⊓ B)) : Dm) : M) : G) =
              (((u0 : Dm) : M) : G) * ((((wWB : ↥(W ⊓ B)) : Dm) : M) : G) *
                (((u0 : Dm) : M) : G)⁻¹ := by
                simp [wConjWB, wConjB, wB, mul_assoc]
          _ = (uU : G) * (((xK : K) : U) : G) * (uU : G)⁻¹ := by
                simp [hu0, hxK_compat, mul_assoc]
      have heWBK_conj :
          eWBK wConjWB = xConjK := by
        apply Subtype.ext
        apply Subtype.ext
        calc
          (((eWBK wConjWB : K) : U) : G) =
              ((((wConjWB : ↥(W ⊓ B)) : Dm) : M) : G) := hWBK_compat wConjWB
          _ = (((xConjK : K) : U) : G) := by
                simpa [xConjK] using hwConj_compat
      have hσ0_apply :
          σ0 (f uU) (QuotientGroup.mk' Hsub xK) =
            QuotientGroup.mk' Hsub xConjK := by
        simpa [σ0, Clam, Hsub, K, f, xConjK] using
          kernelQuotientConjHomOfSurjective_apply_mk_sec9
            f (Uprime.subgroupOf U)
            (by simpa [Clam, Hsub, K, f] using hClamComm) hf_surj uU xK
      have hyConj_coord :
          eClam yConj = σ0 (f uU) (QuotientGroup.mk' Hsub xK) := by
        calc
          eClam yConj =
              QuotientGroup.mk' Hsub
                (eWBK
                  (⟨((wConjSub : B) : Dm), by
                    simpa [W, Subgroup.mem_subgroupOf] using wConjSub.property⟩ :
                    ↥(W ⊓ B))) := by
              simpa [yConj, wConjSub] using hwConjCoord
          _ = QuotientGroup.mk' Hsub (eWBK wConjWB) := by
              rw [hwConjSub_eq]
          _ = QuotientGroup.mk' Hsub xConjK := by
              rw [heWBK_conj]
          _ = σ0 (f uU) (QuotientGroup.mk' Hsub xK) := hσ0_apply.symm
      have hl_eval :
          ψlin l (QuotientGroup.mk' (A.subgroupOf B) wConjB) =
            l.2 (σ0 (f uU) (QuotientGroup.mk' Hsub xK)) := by
        have hcomp := congrArg (fun φ : QClam →* ℂˣ => φ yConj)
          (semidirectProductOfInternalDirectProductLinearCharacter_comp_right_sec9
            hsemi hprod
            (χl.comp eH1.toMonoidHom)
            (l.2.comp eClam.toMonoidHom))
        calc
          ψlin l (QuotientGroup.mk' (A.subgroupOf B) wConjB) =
              (l.2.comp eClam.toMonoidHom) yConj := by
                simpa [ψlin, χl, yConj] using hcomp
          _ = l.2 (σ0 (f uU) (QuotientGroup.mk' Hsub xK)) := by
                simp [MonoidHom.comp_apply, hyConj_coord]
      have hconj_units :
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) wB) =
            ψlin l (QuotientGroup.mk' (A.subgroupOf B) wConjB) := by
        apply Units.ext
        have hconj_val := congrFun hconj wB
        change
          ((ψlin k (QuotientGroup.mk' (A.subgroupOf B) wB) : ℂˣ) : ℂ) =
            ((ψlin l (QuotientGroup.mk' (A.subgroupOf B) wConjB) : ℂˣ) : ℂ)
        simpa [Section1.conjugateOnNormal, Section1.quotientCharacterInflation,
          wConjB, wB, mul_assoc] using hconj_val
      exact congrArg Units.val (by
        calc
          k.2 (QuotientGroup.mk' Hsub xK) =
              ψlin k (QuotientGroup.mk' (A.subgroupOf B) wB) := hk_eval.symm
          _ = ψlin l (QuotientGroup.mk' (A.subgroupOf B) wConjB) := hconj_units
          _ = l.2 (σ0 (f uU) (QuotientGroup.mk' Hsub xK)) := hl_eval)
    intro k l hθeq
    rcases induced_eq_imp_conjugateOrbitConj_of_irreducible_sec9
        B (hψirr k) (hψirr l) hθeq with ⟨i, hi⟩
    revert hi
    refine Quotient.inductionOn i ?_
    intro g hi
    have hconjG :
        Section1.quotientCharacterInflation A B (ψlin k) =
          Section1.conjugateOnNormal B
            (Section1.quotientCharacterInflation A B (ψlin l)) g := by
      simpa [Section1.conjugateOrbitConj] using hi
    rcases hsemiTop.mul_surjective g (by trivial) with ⟨m0, hm0, u0, hu0, hg⟩
    have hmB : m0 ∈ B := hMFD_le_B hm0
    have hconjU :
        Section1.quotientCharacterInflation A B (ψlin k) =
          Section1.conjugateOnNormal B
            (Section1.quotientCharacterInflation A B (ψlin l)) u0 := by
      have hconjMU :
          Section1.quotientCharacterInflation A B (ψlin k) =
            Section1.conjugateOnNormal B
              (Section1.quotientCharacterInflation A B (ψlin l)) (m0 * u0) := by
        simpa [hg] using hconjG
      have herase :
          Section1.conjugateOnNormal B
              (Section1.quotientCharacterInflation A B (ψlin l)) (m0 * u0) =
            Section1.conjugateOnNormal B
              (Section1.quotientCharacterInflation A B (ψlin l)) u0 :=
        conjugateOnNormal_mul_left_of_mem_sec9
          (Section1.quotientCharacterInflation A B (ψlin l)) (hsource_class l) hmB
      exact hconjMU.trans herase
    let uU : U := ⟨(((u0 : Dm) : M) : G), by
      have huUM : ((u0 : Dm) : M) ∈ U.subgroupOf M := by
        simpa [W, Dm, Subgroup.mem_subgroupOf] using hu0
      simpa [Subgroup.mem_subgroupOf] using huUM⟩
    have hpair : k = f uU • l := by
      exact Prod.ext
        (hfirst_of_conj k l u0 uU rfl hconjU)
        (hlam_of_conj k l u0 uU rfl hconjU)
    rw [MulAction.orbitRel_apply]
    exact MulAction.mem_orbit_iff.mpr ⟨f uU, hpair.symm⟩
  intro k l hInd
  exact hinner_orbit k l (houter_to_inner k l (by simpa [Dm, A, ψlin] using hInd))


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 100000 in
private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_character_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_structure_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq →
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  intro hstructure
  classical
  dsimp
    [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_structure_data_sec9]
    at hstructure
  dsimp
    [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_data_sec9]
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  letI : IsCyclic ρBase.range := hρcycBase
  letI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
  rcases hstructure with
    ⟨B, hBnormal, hAnormal, hA_le_B, hBindex, hMFD_le_B,
      hBsemi, eWBK, hWBK_compat,
      QMF, QH1c, QH1, QClam, QH1CH1, hsemi, hprod, eH1, eClam,
      hQH1_apply, hQH1c_apply, hQClam_apply, hQMF_eq, hQMF_split_in_Q,
      hQH1_le_QMF⟩
  letI : B.Normal := hBnormal
  letI : A.Normal := hAnormal
  letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
  let Q : Type u := B ⧸ A.subgroupOf B
  letI : Group Q := inferInstance
  let ψlin : Fin (p - 1) × Lam → Q →* ℂˣ := fun k =>
    semidirectProductOfInternalDirectProductLinearCharacter_sec9
      hsemi hprod
      (((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1.comp
        eH1.toMonoidHom)
      (k.2.comp eClam.toMonoidHom)
  have hpairStabilizer :
      ∀ k : Fin (p - 1) × Lam,
        MulAction.stabilizer ρBase.range k = ⊥ := by
    intro k
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_bot]
      rw [MulAction.mem_stabilizer_iff] at hx
      have hfirst : x • k.1 = k.1 := congrArg Prod.fst hx
      let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
        Subgroup.subtype ρBase.range
      let e := nonprincipalLinearCharacterEquivFin_sec9
        (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)
      have hcharfixed :
          nonprincipalLinearCharacterDualEquiv_sec9 (ρRange x) (e k.1) =
            e k.1 := by
        apply Subtype.ext
        have hspec :=
          nonprincipalLinearCharacterIndexMulAction_spec_sec9
            p (hHcard ⟨0, hqpos⟩) ρRange x k.1
        have hleft : (e (x • k.1)).1 = (e k.1).1 :=
          congrArg Subtype.val (congrArg e hfirst)
        exact hspec.symm.trans hleft
      have hxval : (x : MulAut (H ⟨0, hqpos⟩)) = 1 :=
        mulAut_eq_one_of_nonprincipalLinearCharacterDualEquiv_eq_self_sec9
          (hHcard ⟨0, hqpos⟩) (case_9_7_a_p_prime_sec9 hcase)
          (ρRange x) (e k.1) hcharfixed
      exact Subtype.ext hxval
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [MulAction.mem_stabilizer_iff]
      simp [hx]
  have hψlin_injective : Function.Injective ψlin := by
    intro k l hkl
    let χk : H ⟨0, hqpos⟩ →* ℂˣ :=
      ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1
    let χl : H ⟨0, hqpos⟩ →* ℂˣ :=
      ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) l.1).1
    let ηk : QClam →* ℂˣ := k.2.comp eClam.toMonoidHom
    let ηl : QClam →* ℂˣ := l.2.comp eClam.toMonoidHom
    have hχ : χk = χl := by
      ext x
      let y : QH1 := eH1.symm x
      have hleft_k := congrArg (fun φ : QH1 →* ℂˣ => φ y)
        (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
          hsemi hprod (χk.comp eH1.toMonoidHom) ηk)
      have hleft_l := congrArg (fun φ : QH1 →* ℂˣ => φ y)
        (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
          hsemi hprod (χl.comp eH1.toMonoidHom) ηl)
      have hval := congrArg (fun φ : Q →* ℂˣ => φ (y : Q)) hkl
      change ((χk x : ℂˣ) : ℂ) = ((χl x : ℂˣ) : ℂ)
      calc
        ((χk x : ℂˣ) : ℂ) = (((ψlin k) (y : Q) : ℂˣ) : ℂ) := by
          simpa [ψlin, χk, ηk, y] using congrArg Units.val hleft_k.symm
        _ = (((ψlin l) (y : Q) : ℂˣ) : ℂ) := congrArg Units.val hval
        _ = ((χl x : ℂˣ) : ℂ) := by
          simpa [ψlin, χl, ηl, y] using congrArg Units.val hleft_l
    have hfst : k.1 = l.1 := by
      let e := nonprincipalLinearCharacterEquivFin_sec9
        (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)
      apply e.injective
      apply Subtype.ext
      exact hχ
    have hη : k.2 = l.2 := by
      ext x
      let y : QClam := eClam.symm x
      have hright_k := congrArg (fun φ : QClam →* ℂˣ => φ y)
        (semidirectProductOfInternalDirectProductLinearCharacter_comp_right_sec9
          hsemi hprod (χk.comp eH1.toMonoidHom) ηk)
      have hright_l := congrArg (fun φ : QClam →* ℂˣ => φ y)
        (semidirectProductOfInternalDirectProductLinearCharacter_comp_right_sec9
          hsemi hprod (χl.comp eH1.toMonoidHom) ηl)
      have hval := congrArg (fun φ : Q →* ℂˣ => φ (y : Q)) hkl
      change ((k.2 x : ℂˣ) : ℂ) = ((l.2 x : ℂˣ) : ℂ)
      calc
        ((k.2 x : ℂˣ) : ℂ) = (((ψlin k) (y : Q) : ℂˣ) : ℂ) := by
          simpa [ψlin, χk, ηk, y] using congrArg Units.val hright_k.symm
        _ = (((ψlin l) (y : Q) : ℂˣ) : ℂ) := congrArg Units.val hval
        _ = ((l.2 x : ℂˣ) : ℂ) := by
          simpa [ψlin, χl, ηl, y] using congrArg Units.val hright_l
    exact Prod.ext hfst hη
  have hMFDnormal : MFD.Normal := by
    simpa [MFD, Dm] using
      theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
        M MF U W1 W2 H0 C p q a hcase
  letI : MFD.Normal := hMFDnormal
  have hsemiTop :
      Section2.IsInternalSemidirectProduct (⊤ : Subgroup Dm) MFD W := by
    simpa [MFD, W, Dm] using
      theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
        M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase) hMFDnormal
  have hfirst_free :
      ∀ (x : ρBase.range) (i : Fin (p - 1)), x • i = i → x = 1 := by
    intro x i hfirst
    let e := nonprincipalLinearCharacterEquivFin_sec9
      (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)
    have hcharfixed :
        nonprincipalLinearCharacterDualEquiv_sec9 (ρRange x) (e i) = e i := by
      apply Subtype.ext
      have hspec :=
        nonprincipalLinearCharacterIndexMulAction_spec_sec9
          p (hHcard ⟨0, hqpos⟩) ρRange x i
      have hleft : (e (x • i)).1 = (e i).1 :=
        congrArg Subtype.val (congrArg e hfirst)
      exact hspec.symm.trans hleft
    have hxval : (x : MulAut (H ⟨0, hqpos⟩)) = 1 :=
      mulAut_eq_one_of_nonprincipalLinearCharacterDualEquiv_eq_self_sec9
        (hHcard ⟨0, hqpos⟩) (case_9_7_a_p_prime_sec9 hcase)
        (ρRange x) (e i) hcharfixed
    exact Subtype.ext hxval
  have hψlin_first_fixed_of_conjugate :
      ∀ (k : Fin (p - 1) × Lam) (u0 : Dm) (uU : U),
        (((u0 : Dm) : M) : G) = (uU : G) →
        Section1.conjugateOnNormal B
            (Section1.quotientCharacterInflation A B (ψlin k)) u0 =
          Section1.quotientCharacterInflation A B (ψlin k) →
        f uU • k.1 = k.1 := by
    intro k u0 uU hu0 hfix
    let χbase : H ⟨0, hqpos⟩ →* ℂˣ :=
      ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1
    let χbase' : H ⟨0, hqpos⟩ →* ℂˣ :=
      ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) (f uU • k.1)).1
    have hχbase_action :
        χbase' = χbase.comp (ρRange (f uU)).symm.toMonoidHom := by
      simpa [χbase, χbase', ρRange, instFirstAction] using
        nonprincipalLinearCharacterIndexMulAction_spec_sec9
          p (hHcard ⟨0, hqpos⟩) ρRange (f uU) k.1
    have hχ : χbase' = χbase := by
      ext x
      have hMFleD : MF ≤ ambientDerivedSubgroup M :=
        MF_le_ambientDerived_of_hypothesis_9_2_sec9
          M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
      have hDleM : ambientDerivedSubgroup M ≤ M :=
        section12_ambientDerivedSubgroup_le (E := M)
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF)
          (x : MF ⧸ H0.subgroupOf MF) with
        ⟨mMF, hmMFx⟩
      let mM : M := ⟨(mMF : G), hDleM (hMFleD mMF.property)⟩
      let mD : Dm := ⟨mM, by
        simpa [Dm, Subgroup.mem_subgroupOf, mM] using hMFleD mMF.property⟩
      have hmD_MFD : mD ∈ MFD := by
        change (mD : M) ∈ MF.subgroupOf M
        simp [mD, mM, Subgroup.mem_subgroupOf]
      let mB : B := ⟨mD, hMFD_le_B hmD_MFD⟩
      have hmB_MFDsub : mB ∈ MFD.subgroupOf B := by
        simpa [MFD, Subgroup.mem_subgroupOf, mB] using hmD_MFD
      let mSub : MFD.subgroupOf B := ⟨mB, hmB_MFDsub⟩
      have hmRaw_eq :
          theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
              ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub) =
            mMF := by
        apply Subtype.ext
        rfl
      have hmH1 :
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub)) ∈
            H ⟨0, hqpos⟩ := by
        rw [hmRaw_eq, hmMFx]
        exact x.property
      rcases hQH1_apply mSub hmH1 with ⟨hmQH1, hcoord⟩
      let y : QH1 := ⟨QuotientGroup.mk' (A.subgroupOf B) mB, hmQH1⟩
      have hcoord_x : eH1 y = x := by
        calc
          eH1 y =
              ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                  (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                    ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub)),
                hmH1⟩ := by
                  simpa [y, mSub] using hcoord
          _ = x := by
                  apply Subtype.ext
                  simpa [hmRaw_eq] using hmMFx
      have hright_eval :
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) = χbase x := by
        have hcomp := congrArg (fun φ : QH1 →* ℂˣ => φ y)
          (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
            hsemi hprod
            (χbase.comp eH1.toMonoidHom)
            (k.2.comp eClam.toMonoidHom))
        calc
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) =
              (χbase.comp eH1.toMonoidHom) y := by
                simpa [ψlin, χbase, y] using hcomp
          _ = χbase x := by
                simp [MonoidHom.comp_apply, hcoord_x]
      have hu0W : u0 ∈ W := by
        change ((u0 : Dm) : M) ∈ U.subgroupOf M
        simp [Subgroup.mem_subgroupOf, hu0]
      have hconjMFD : Section2.conjBy u0 mD ∈ MFD :=
        hsemiTop.right_normalizes_left u0 hu0W mD hmD_MFD
      let mConjB : B := ⟨Section2.conjBy u0 mD, hMFD_le_B hconjMFD⟩
      have hmConjB_MFDsub : mConjB ∈ MFD.subgroupOf B := by
        simpa [MFD, Subgroup.mem_subgroupOf, mConjB] using hconjMFD
      let mConjSub : MFD.subgroupOf B := ⟨mConjB, hmConjB_MFDsub⟩
      rcases hρactionBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹))
          (uU⁻¹) rfl with
        ⟨hconjMF, haction⟩
      let xFromM : H ⟨0, hqpos⟩ :=
        ⟨QuotientGroup.mk' (H0.subgroupOf MF) mMF, by
          rw [hmMFx]
          exact x.property⟩
      have hxFromM : xFromM = x := by
        apply Subtype.ext
        exact hmMFx
      let conjMF : MF :=
        ⟨((uU : G) * (mMF : G) * (uU : G)⁻¹), by
          simpa using hconjMF mMF⟩
      have hsymm_apply :
          ((ρRange (f uU)).symm x : MF ⧸ H0.subgroupOf MF) =
            (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) x :
              MF ⧸ H0.subgroupOf MF) := by
        simp [ρRange, f]
      have hact_x :
          (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) x :
              MF ⧸ H0.subgroupOf MF) =
            QuotientGroup.mk' (H0.subgroupOf MF) conjMF := by
        have hact := haction mMF xFromM.property
        have hact' :
            (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) xFromM :
                MF ⧸ H0.subgroupOf MF) =
              QuotientGroup.mk' (H0.subgroupOf MF) conjMF := by
          simpa [xFromM, conjMF, mul_assoc] using hact
        simpa [hxFromM] using hact'
      have hmConjRaw_eq :
          theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
              ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub) =
            conjMF := by
        apply Subtype.ext
        simp [mConjSub, mConjB, mD, mM, conjMF, Section2.conjBy,
          theorem_9_8_MFDSubgroupOf_to_MF_sec9, hu0, mul_assoc]
      have hconjCoord :
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)) =
            ((ρRange (f uU)).symm x : MF ⧸ H0.subgroupOf MF) := by
        calc
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)) =
              QuotientGroup.mk' (H0.subgroupOf MF) conjMF := by
                rw [hmConjRaw_eq]
          _ = (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) x :
                MF ⧸ H0.subgroupOf MF) := hact_x.symm
          _ = ((ρRange (f uU)).symm x : MF ⧸ H0.subgroupOf MF) :=
                hsymm_apply.symm
      have hmConjH1 :
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)) ∈
            H ⟨0, hqpos⟩ := by
        rw [hconjCoord]
        exact ((ρRange (f uU)).symm x).property
      rcases hQH1_apply mConjSub hmConjH1 with
        ⟨hmConjQH1, hcoordConj⟩
      let yConj : QH1 :=
        ⟨QuotientGroup.mk' (A.subgroupOf B) mConjB, hmConjQH1⟩
      have hcoordConj_x : eH1 yConj = (ρRange (f uU)).symm x := by
        calc
          eH1 yConj =
              ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                  (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                    ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)),
                hmConjH1⟩ := by
                  simpa [yConj, mConjSub] using hcoordConj
          _ = (ρRange (f uU)).symm x := by
                  apply Subtype.ext
                  exact hconjCoord
      have hleft_eval :
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) mConjB) = χbase' x := by
        have hcomp := congrArg (fun φ : QH1 →* ℂˣ => φ yConj)
          (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
            hsemi hprod
            (χbase.comp eH1.toMonoidHom)
            (k.2.comp eClam.toMonoidHom))
        have hχapply := congrArg (fun φ : H ⟨0, hqpos⟩ →* ℂˣ => φ x)
          hχbase_action
        calc
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) mConjB) =
              (χbase.comp eH1.toMonoidHom) yConj := by
                simpa [ψlin, χbase, yConj] using hcomp
          _ = χbase ((ρRange (f uU)).symm x) := by
                simp [MonoidHom.comp_apply, hcoordConj_x]
          _ = χbase' x := by
                simpa [MonoidHom.comp_apply] using hχapply.symm
      have hfix_units :
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) mConjB) =
            ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) := by
        apply Units.ext
        have hfix_val := congrFun hfix mB
        change
          ((ψlin k (QuotientGroup.mk' (A.subgroupOf B) mConjB) : ℂˣ) : ℂ) =
            ((ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) : ℂˣ) : ℂ)
        simpa [Section1.conjugateOnNormal, Section1.quotientCharacterInflation,
          mConjB, mB, mD, Section2.conjBy, mul_assoc] using hfix_val
      exact congrArg Units.val (by
        calc
          (χbase' x : ℂˣ) = ψlin k (QuotientGroup.mk' (A.subgroupOf B) mConjB) :=
            hleft_eval.symm
          _ = ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) := hfix_units
          _ = χbase x := hright_eval)
    let e := nonprincipalLinearCharacterEquivFin_sec9
      (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)
    apply e.injective
    apply Subtype.ext
    exact hχ
  have hIeq :
      ∀ k : Fin (p - 1) × Lam,
        Section1.inertiaSubgroup B
          (Section1.quotientCharacterInflation A B (ψlin k)) = B := by
    intro k
    have hI_le_B :
        Section1.inertiaSubgroup B
            (Section1.quotientCharacterInflation A B (ψlin k)) ≤ B := by
      intro g hgI
      rcases hsemiTop.mul_surjective g (by trivial) with ⟨m0, hm0, u0, hu0, hg⟩
      have hmB : m0 ∈ B := hMFD_le_B hm0
      let uU : U := ⟨(((u0 : Dm) : M) : G), by
        have huUM : ((u0 : Dm) : M) ∈ U.subgroupOf M := by
          simpa [W, Dm, Subgroup.mem_subgroupOf] using hu0
        simpa [Subgroup.mem_subgroupOf] using huUM⟩
      have hu_fix :
          Section1.conjugateOnNormal B
              (Section1.quotientCharacterInflation A B (ψlin k)) u0 =
            Section1.quotientCharacterInflation A B (ψlin k) := by
        have hgfix :
            Section1.conjugateOnNormal B
                (Section1.quotientCharacterInflation A B (ψlin k)) g =
              Section1.quotientCharacterInflation A B (ψlin k) := by
          simpa [Section1.inertiaSubgroup] using hgI
        have hmulfix :
            Section1.conjugateOnNormal B
                (Section1.quotientCharacterInflation A B (ψlin k)) (m0 * u0) =
              Section1.quotientCharacterInflation A B (ψlin k) := by
          simpa [hg] using hgfix
        have herase :
            Section1.conjugateOnNormal B
                (Section1.quotientCharacterInflation A B (ψlin k)) (m0 * u0) =
              Section1.conjugateOnNormal B
                (Section1.quotientCharacterInflation A B (ψlin k)) u0 :=
          conjugateOnNormal_mul_left_of_mem_sec9
            (Section1.quotientCharacterInflation A B (ψlin k))
            (Section1.quotientCharacterInflation_isClassFunction A B (ψlin k)) hmB
        exact herase.symm.trans hmulfix
      have hxone : f uU = 1 := by
        exact hfirst_free (f uU) k.1
          (hψlin_first_fixed_of_conjugate k u0 uU (by rfl) hu_fix)
      have huK : uU ∈ K := by
        simpa [K, MonoidHom.mem_ker] using hxone
      let uK : K := ⟨uU, huK⟩
      let WB : Subgroup Dm := W ⊓ B
      let wB : WB := eWBK.symm uK
      have hwG :
          ((((wB : WB) : Dm) : M) : G) = (uU : G) := by
        have hcompat := hWBK_compat wB
        have hval : (((eWBK wB : K) : U) : G) = (uU : G) := by
          simp [wB, uK]
        exact hcompat.symm.trans hval
      have hu0_eq_wB : u0 = (wB : Dm) := by
        apply Subtype.ext
        apply Subtype.ext
        simpa [uU] using hwG.symm
      have huB : u0 ∈ B := by
        rw [hu0_eq_wB]
        exact wB.property.2
      rw [hg]
      exact B.mul_mem hmB huB
    refine le_antisymm hI_le_B ?_
    exact Section1.proposition_1_7_inertia_contains_H (H := B)
      (theta := Section1.quotientCharacterInflation A B (ψlin k))
      (hclass := Section1.quotientCharacterInflation_isClassFunction A B (ψlin k))
  have hθnotMF :
      ∀ k : Fin (p - 1) × Lam,
        ¬ Section1.subgroupInKernel'
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k))) MFD := by
    intro k hkerMFD
    let χbase : H ⟨0, hqpos⟩ →* ℂˣ :=
      ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1
    let χQH1 : QH1 →* ℂˣ := χbase.comp eH1.toMonoidHom
    let ηQClam : QClam →* ℂˣ := k.2.comp eClam.toMonoidHom
    have hψirr :
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.quotientCharacterInflation A B (ψlin k)) :=
      Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
        A B (ψlin k)
    have hsrcKer :
        Section1.subgroupInKernel'
          (Section1.quotientCharacterInflation A B (ψlin k))
          (MFD.subgroupOf B) :=
      subgroupInKernel'_of_inducedCF_sec9 B MFD hMFD_le_B hψirr hkerMFD
    have hχbase_ne : χbase ≠ 1 := by
      simpa [χbase] using
        ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).2
    apply hχbase_ne
    ext x
    let y : QH1 := eH1.symm x
    have hyQMF : (y : Q) ∈ QMF :=
      hQH1_le_QMF y.property
    have hyQMF' :
        (y : Q) ∈
          ((MFD.subgroupOf B).map (QuotientGroup.mk' (A.subgroupOf B))) := by
      simpa [hQMF_eq] using hyQMF
    rcases hyQMF' with ⟨m, hmMFD, hmy⟩
    have hmker := hsrcKer ⟨m, hmMFD⟩
    have hψm : ((ψlin k) (QuotientGroup.mk' (A.subgroupOf B) m) : ℂ) = 1 := by
      rw [Section1.quotientCharacterInflation_degree] at hmker
      simpa [Section1.quotientCharacterInflation] using hmker
    have hψy : ((ψlin k) (y : Q) : ℂ) = 1 := by
      simpa [hmy] using hψm
    have hrestrict :
        ψlin k (y : Q) = χQH1 y := by
      have hcomp := congrArg (fun φ : QH1 →* ℂˣ => φ y)
        (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
          hsemi hprod χQH1 ηQClam)
      simpa [ψlin, χQH1, ηQClam, χbase] using hcomp
    have hyval : ((χQH1 y) : ℂ) = 1 := by
      simpa [hrestrict] using hψy
    simpa [χQH1, y] using hyval
  refine
    ⟨B, hBnormal, hAnormal, hA_le_B, hBindex,
      QH1c, QH1, QClam, QH1CH1, hsemi, hprod, eH1, eClam, ?_, ?_, ?_, ?_⟩
  · exact hIeq
  · intro k hkerMFD
    let χbase : H ⟨0, hqpos⟩ →* ℂˣ :=
      ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1
    let χQH1 : QH1 →* ℂˣ := χbase.comp eH1.toMonoidHom
    let ηQClam : QClam →* ℂˣ := k.2.comp eClam.toMonoidHom
    have hψirr :
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.quotientCharacterInflation A B (ψlin k)) :=
      Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
        A B (ψlin k)
    have hsrcKer :
        Section1.subgroupInKernel'
          (Section1.quotientCharacterInflation A B (ψlin k))
          (MFD.subgroupOf B) :=
      subgroupInKernel'_of_inducedCF_sec9 B MFD hMFD_le_B hψirr hkerMFD
    have hχbase_ne : χbase ≠ 1 := by
      simpa [χbase] using
        ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).2
    apply hχbase_ne
    ext x
    let y : QH1 := eH1.symm x
    have hyQMF : (y : Q) ∈ QMF :=
      hQH1_le_QMF y.property
    have hyQMF' :
        (y : Q) ∈
          ((MFD.subgroupOf B).map (QuotientGroup.mk' (A.subgroupOf B))) := by
      simpa [hQMF_eq] using hyQMF
    rcases hyQMF' with ⟨m, hmMFD, hmy⟩
    have hmker := hsrcKer ⟨m, hmMFD⟩
    have hψm : ((ψlin k) (QuotientGroup.mk' (A.subgroupOf B) m) : ℂ) = 1 := by
      rw [Section1.quotientCharacterInflation_degree] at hmker
      simpa [Section1.quotientCharacterInflation] using hmker
    have hψy : ((ψlin k) (y : Q) : ℂ) = 1 := by
      simpa [hmy] using hψm
    have hrestrict :
        ψlin k (y : Q) = χQH1 y := by
      have hcomp := congrArg (fun φ : QH1 →* ℂˣ => φ y)
        (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
          hsemi hprod χQH1 ηQClam)
      simpa [ψlin, χQH1, ηQClam, χbase] using hcomp
    have hyval : ((χQH1 y) : ℂ) = 1 := by
      simpa [hrestrict] using hψy
    simpa [χQH1, y] using hyval
  ·
    intro k
    exact
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_character_irr_Xtheta_core_sec9
        (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
        (H0 := H0) (C := C) (Uprime := Uprime)
        (p := p) (q := q) (a := a) (u := u)
        (H := H) (hqpos := hqpos) (hHcard := hHcard)
        (hHnorm := hHnorm) (hHindep := hHindep) (hHsup := hHsup)
        (ρBase := ρBase) (hρcycBase := hρcycBase)
        (_hρcardBase := hρcardBase) (_hρactionBase := hρactionBase)
        (_hρkerBase := hρkerBase) (hconjBase := hconjBase)
        (hcase := hcase) (_hBarU := hBarU) (hUprimeEq := hUprimeEq)
        (B := B) (hBnormal := hBnormal) (hAnormal := hAnormal)
        (_hA_le_B := hA_le_B) (_hMFD_le_B := hMFD_le_B) (hBsemi := hBsemi)
        (eWBK := eWBK) (_hWBK_compat := hWBK_compat)
        (QH1c := QH1c) (QH1 := QH1) (QClam := QClam)
        (QH1CH1 := QH1CH1) (hsemi := hsemi) (hprod := hprod)
        (eH1 := eH1) (eClam := eClam)
        (_hQH1_apply := hQH1_apply) (_hQH1c_apply := hQH1c_apply)
        (_hQClam_apply := hQClam_apply)
        (QMF := QMF) (_hQMF_eq := hQMF_eq)
        (_hQMF_split_in_Q := hQMF_split_in_Q) (_hQH1_le_QMF := hQH1_le_QMF)
        (_hIeq := hIeq) (_hθnotMF := hθnotMF) k
  ·
    intro k l hInd
    exact
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_character_inj_Xtheta_core_sec9
        (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
        (H0 := H0) (C := C) (Uprime := Uprime)
        (p := p) (q := q) (a := a) (u := u)
        (H := H) (hqpos := hqpos) (hHcard := hHcard)
        (hHnorm := hHnorm) (hHindep := hHindep) (hHsup := hHsup)
        (ρBase := ρBase) (hρcycBase := hρcycBase)
        (_hρcardBase := hρcardBase) (hρactionBase := hρactionBase)
        (_hρkerBase := hρkerBase) (hconjBase := hconjBase)
        (hcase := hcase) (_hBarU := hBarU) (hUprimeEq := hUprimeEq)
        (B := B) (hBnormal := hBnormal) (hAnormal := hAnormal)
        (_hMFD_le_B := hMFD_le_B) (hBsemi := hBsemi)
        (eWBK := eWBK) (_hWBK_compat := hWBK_compat)
        (QH1c := QH1c) (QH1 := QH1) (QClam := QClam)
          (QH1CH1 := QH1CH1) (hsemi := hsemi) (hprod := hprod)
          (eH1 := eH1) (eClam := eClam)
          (_hQH1_apply := hQH1_apply) (_hQH1c_apply := hQH1c_apply)
          (_hQClam_apply := hQClam_apply) (_hIeq := hIeq)
          (_hθnotMF := hθnotMF)
          (_hψlin_injective := hψlin_injective)
        (_hpairStabilizer := hpairStabilizer) k l hInd

private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  exact
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_character_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
      ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
      hUprimeEq
      (theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_structure_source_core_sec9
        M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
        ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
        hUprimeEq)

private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  exact
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_of_semidirect_product_formula_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq
      (theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_source_core_sec9
        M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
        ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
        hUprimeEq)

private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  exact
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_of_quotient_linear_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq
      (theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_source_core_sec9
        M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
        ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
        hUprimeEq)

private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  exact
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_of_semidirect_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq
      (theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_source_core_sec9
        M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
        ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
        hUprimeEq)

set_option maxHeartbeats 800000 in
private theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        ∀ hUprimeEq : Uprime = (_root_.commutator U).map U.subtype,
          theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_data_sec9
            M MF U H0 C Uprime p q a H hqpos hHcard ρBase hUprimeEq := by
  -- the base `U -> rhoBase.range` action, quotiented by `U'`.
  -- `def_Itheta` for this concrete quotient.
  intro hcase hBarU hUprimeEq
  classical
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_data_sec9]
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  letI : Fintype Clam := Fintype.ofFinite Clam
  letI : DecidableEq Clam := Classical.decEq Clam
  letI : Finite Clam := Finite.of_fintype Clam
  have hClamComm : IsMulCommutative Clam := by
    simpa [Clam, Hsub, K, f] using
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
        U C Uprime ρBase hUprimeEq
  letI : IsMulCommutative Clam := hClamComm
  letI : CommGroup Clam := IsMulCommutative.instCommGroup
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Clam) :=
    Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent Clam)
  let Lam : Type u := Clam →* ℂˣ
  let instFintypeLam : Fintype Lam := Fintype.ofFinite Lam
  let instDecidableEqLam : DecidableEq Lam := Classical.decEq Lam
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  let lam : Lam → Clam →* ℂˣ := fun χ => χ
  have hlaminj : Function.Injective lam := by
    intro χ η hχη
    exact hχη
  have hLamClamcard : Fintype.card Lam = Fintype.card Clam := by
    change Fintype.card (Clam →* ℂˣ) = Fintype.card Clam
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Clam ℂ
  have hlamdata :
      ∀ j : Lam,
        Section1.IsIrreducibleCharacterOnGroup
          (fun x : Clam => (lam j x : ℂ)) ∧
        Section1.degree (fun x : Clam => (lam j x : ℂ)) = 1 := by
    intro χ
    constructor
    · change Section1.IsIrreducibleCharacterOnGroup
        (Section1.characterInflationByHom (MonoidHom.id Clam) χ)
      exact Section1.characterInflationByHom_isIrreducibleCharacterOnGroup
        (MonoidHom.id Clam) χ
    · simpa [lam] using Section1.linearCharacter_degree χ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  letI : IsCyclic ρBase.range := hρcycBase
  letI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  have htail :
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_sec9
        M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
      ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
      hUprimeEq
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_sec9]
    at htail
  exact ⟨Lam, instFintypeLam, instDecidableEqLam, lam, hlaminj, hLamClamcard,
    hlamdata, instLamAction, by
      simpa [f, K, Hsub, Clam, Lam, σ, instLamAction] using htail⟩

private theorem theorem_9_8_initial_constituent_Mtheta_free_action_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          theorem_9_8_initial_constituent_Mtheta_free_action_data_sec9
            M MF U H0 Uprime p a := by
  -- `[set~ 0] × Iirr Clam`, its order is `a`, and quotienting gives the
  -- induced `M'` constituents of degree `a`.
  intro hcase hBarU hUprime
  haveI : NeZero a :=
    ⟨Nat.ne_of_gt
      (case_9_7_a_index_a_pos_sec9 M MF U W1 W2 H0 C p q a hcase)⟩
  rcases case_9_7_a_component_decomposition_sec9 hcase with
    ⟨hnormalH0, H, hHcard, hHnorm, hHindep, hHsup, hfac, hconj⟩
  rcases hconj with ⟨hqpos, hconjBase⟩
  rcases hfac ⟨0, hqpos⟩ with
    ⟨hnormalC, ρBase, hρcycBase, hρcardBase, hρactionBase, hρkerBase⟩
  rcases case_9_7_a_quotient_isElementaryAbelian_sec9 hcase with
    ⟨_hnormalH0_case, hquotElem⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hquotElem
  haveI : IsMulCommutative (MF ⧸ H0.subgroupOf MF) := inferInstance
  have hclam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
      ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
      hUprime
  have hindex :=
    theorem_9_8_initial_constituent_Mtheta_clam_index_action_data_of_clam_kernel_quotient_theta_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hρcardBase
      hUprime hclam
  have hrawTheta :=
    theorem_9_8_initial_constituent_Mtheta_clam_raw_theta_data_of_clam_index_action_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase
      (case_9_7_a_p_prime_sec9 hcase) hindex
  have hparam :=
    theorem_9_8_initial_constituent_Mtheta_clam_parameter_data_of_clam_raw_theta_data_sec9
      M MF U H0 C Uprime p q a H hqpos ρBase hrawTheta
  have hrange :=
    theorem_9_8_initial_constituent_Mtheta_base_range_action_data_of_clam_parameter_data_sec9
      M MF U H0 C Uprime p q a H hqpos ρBase hparam
  have habstract :=
    theorem_9_8_initial_constituent_Mtheta_abstract_cyclic_action_data_of_base_range_action_data_sec9
      M MF U H0 C Uprime p q a H hqpos ρBase hρcycBase hρcardBase hrange
  have hcyclic :=
    theorem_9_8_initial_constituent_Mtheta_cyclic_action_data_of_abstract_cyclic_action_data_sec9
      M MF U H0 Uprime p a habstract
  exact theorem_9_8_initial_constituent_Mtheta_free_action_data_of_cyclic_action_data_sec9
    M MF U H0 Uprime p a hcyclic

private theorem theorem_9_8_initial_degree_count_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
            (theorem_9_8_initial_degree_subfamily_sec9 M q a SH0U).card ≥
              ((p - 1) / a) * (Nat.card U / (a * Nat.card Uprime)) := by
  -- `S(H0U')`.  The witness-level theorem below only unpacks this count
  -- through `kernelInducedFamily`.
  intro hcase hBarU hUprime hSH0U
  have hfree :
      theorem_9_8_initial_constituent_Mtheta_free_action_data_sec9
        M MF U H0 Uprime p a :=
    theorem_9_8_initial_constituent_Mtheta_free_action_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u hcase hBarU hUprime
  have hraw :
      theorem_9_8_initial_constituent_Mtheta_raw_product_data_sec9
        M MF U H0 Uprime p a :=
    theorem_9_8_initial_constituent_Mtheta_raw_product_data_of_free_action_data_sec9
      M MF U H0 Uprime p a hfree
  have hmtheta :
      theorem_9_8_initial_constituent_Mtheta_data_sec9 M MF U H0 Uprime p a :=
    theorem_9_8_initial_constituent_Mtheta_data_of_raw_product_data_sec9
      M MF U H0 Uprime p a hraw
  have horbit :
      theorem_9_8_initial_constituent_orbit_data_sec9 M MF U H0 Uprime p a :=
    theorem_9_8_initial_constituent_orbit_data_of_Mtheta_data_sec9
      M MF U H0 Uprime p a (case_9_7_a_index_dvd_p_minus_one_sec9 hcase) hmtheta
  have hfamily :
      theorem_9_8_initial_constituent_family_data_sec9 M MF U H0 Uprime p a :=
    theorem_9_8_initial_constituent_family_data_of_orbit_data_sec9
      M MF U H0 Uprime p a
      (case_9_7_a_index_a_pos_sec9 M MF U W1 W2 H0 C p q a hcase)
      horbit
  exact theorem_9_8_initial_degree_count_of_constituent_family_data_sec9
    M MF U W1 W2 H0 Uprime p q a SH0U
    (case_9_7_a_hypothesis_9_2_sec9 hcase) hSH0U hfamily

private theorem theorem_9_8_initial_constituent_witness_count_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
            ∃ I : Finset (Section1.ClassFunction M),
              I ⊆ SH0U ∧
                I.card ≥ ((p - 1) / a) *
                  (Nat.card U / (a * Nat.card Uprime)) ∧
                ∀ χ : Section1.ClassFunction M, χ ∈ I →
                  Section1.IsIrreducibleCharacterOnGroup χ ∧
                    ∃ θ : Section1.ClassFunction
                        ((ambientDerivedSubgroup M).subgroupOf M),
                      Section1.IsIrreducibleCharacterOnGroup θ ∧
                        ¬ Section1.subgroupInKernel' θ
                          ((MF.subgroupOf M).subgroupOf
                            ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                        Section1.subgroupInKernel' θ
                          (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                            ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                        χ = Section1.inducedCF
                          ((ambientDerivedSubgroup M).subgroupOf M) θ ∧
                        Section1.degree θ = (a : ℂ) := by
  intro hcase hBarU hUprime hSH0U
  classical
  let I : Finset (Section1.ClassFunction M) :=
    theorem_9_8_initial_degree_subfamily_sec9 M q a SH0U
  have hIcard :
      I.card ≥ ((p - 1) / a) *
        (Nat.card U / (a * Nat.card Uprime)) := by
    simpa [I] using
      theorem_9_8_initial_degree_count_source_core_sec9
        M MF U W1 W2 H0 C Uprime p q a u SH0U hcase hBarU hUprime hSH0U
  have hDindex :
      Subgroup.index ((ambientDerivedSubgroup M).subgroupOf M) = q :=
    ambientDerived_subgroupOf_index_eq_q_of_hypothesis_9_2_sec9
      M MF U W1 W2 q hcase.1
  refine ⟨I, ?_, hIcard, ?_⟩
  · intro χ hχI
    have hχdata :
        χ ∈ SH0U ∧
          Section1.IsIrreducibleCharacterOnGroup χ ∧
            Section1.degree χ = (q * a : ℂ) := by
      simpa [I, theorem_9_8_initial_degree_subfamily_sec9] using hχI
    exact hχdata.1
  · intro χ hχI
    have hχdata :
        χ ∈ SH0U ∧
          Section1.IsIrreducibleCharacterOnGroup χ ∧
            Section1.degree χ = (q * a : ℂ) := by
      simpa [I, theorem_9_8_initial_degree_subfamily_sec9] using hχI
    rcases hχdata with ⟨hχSH0U, hχirr, hχdegree⟩
    rcases hSH0U with ⟨_hYle, _hMFle, hmem⟩
    rcases (hmem χ).mp hχSH0U with ⟨θ, hθirr, hθnot, hθker, hχeq⟩
    refine ⟨hχirr, θ, hθirr, hθnot, hθker, hχeq, ?_⟩
    have hq_ne : (q : ℂ) ≠ 0 := by
      exact_mod_cast (case_9_7_a_q_prime_sec9 hcase).ne_zero
    have hmul :
        (q : ℂ) * Section1.degree θ = (q : ℂ) * (a : ℂ) := by
      calc
        (q : ℂ) * Section1.degree θ =
            Section1.degree
              (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) θ) := by
          rw [Section1.degree_inducedClassFunction, hDindex]
        _ = Section1.degree χ := by
          rw [← hχeq]
        _ = (q * a : ℂ) := hχdegree
        _ = (q : ℂ) * (a : ℂ) := by
          norm_num [Nat.cast_mul]
    exact mul_left_cancel₀ hq_ne hmul


private theorem theorem_9_8_initial_constituent_degree_count_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                ∃ I : Finset (Section1.ClassFunction M),
                  I ⊆ SH0U ∧
                    I.card ≥ ((p - 1) / a) *
                      (Nat.card U / (a * Nat.card Uprime)) ∧
                    ∀ χ : Section1.ClassFunction M, χ ∈ I →
                      Section1.IsIrreducibleCharacterOnGroup χ ∧
                        ∀ θ : Section1.ClassFunction
                            ((ambientDerivedSubgroup M).subgroupOf M),
                          Section1.IsIrreducibleCharacterOnGroup θ →
                            ¬ Section1.subgroupInKernel' θ
                              ((MF.subgroupOf M).subgroupOf
                                ((ambientDerivedSubgroup M).subgroupOf M)) →
                            Section1.subgroupInKernel' θ
                              (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                                ((ambientDerivedSubgroup M).subgroupOf M)) →
                            χ = Section1.inducedCF
                              ((ambientDerivedSubgroup M).subgroupOf M) θ →
                              Section1.degree θ = (a : ℂ) := by
  intro hcase hBarU hUprime _hSH0 _hSH0C hSH0U
  rcases theorem_9_8_initial_constituent_witness_count_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u SH0U hcase hBarU hUprime hSH0U with
    ⟨I, hIsub, hIcard, hIwitness⟩
  refine ⟨I, hIsub, hIcard, ?_⟩
  intro χ hχI
  rcases hIwitness χ hχI with
    ⟨hχirr, θ0, hθ0irr, hθ0not, hθ0ker, hχeq0, hθ0deg⟩
  refine ⟨hχirr, ?_⟩
  intro θ _hθirr _hθnot _hθker hχeq
  let D : Subgroup G := ambientDerivedSubgroup M
  have hIndEq :
      Section1.inducedCF (D.subgroupOf M) θ =
        Section1.inducedCF (D.subgroupOf M) θ0 :=
    hχeq.symm.trans hχeq0
  have hdegIndEq :
      Section1.degree (Section1.inducedCF (D.subgroupOf M) θ) =
        Section1.degree (Section1.inducedCF (D.subgroupOf M) θ0) :=
    congrArg Section1.degree hIndEq
  have hidx_ne : (Subgroup.index (D.subgroupOf M) : ℂ) ≠ 0 := by
    exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := D.subgroupOf M))
  have hmul :
      (Subgroup.index (D.subgroupOf M) : ℂ) * Section1.degree θ =
        (Subgroup.index (D.subgroupOf M) : ℂ) * (a : ℂ) := by
    calc
      (Subgroup.index (D.subgroupOf M) : ℂ) * Section1.degree θ =
          Section1.degree (Section1.inducedCF (D.subgroupOf M) θ) := by
            rw [Section1.degree_inducedClassFunction]
      _ = Section1.degree (Section1.inducedCF (D.subgroupOf M) θ0) := hdegIndEq
      _ = (Subgroup.index (D.subgroupOf M) : ℂ) * Section1.degree θ0 := by
            rw [Section1.degree_inducedClassFunction]
      _ = (Subgroup.index (D.subgroupOf M) : ℂ) * (a : ℂ) := by
            rw [hθ0deg]
  exact mul_left_cancel₀ hidx_ne hmul

private theorem theorem_9_8_initial_degree_count_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                ∃ I : Finset (Section1.ClassFunction M),
                  I ⊆ SH0U ∧
                    I.card ≥ ((p - 1) / a) *
                      (Nat.card U / (a * Nat.card Uprime)) ∧
                    ∀ χ : Section1.ClassFunction M, χ ∈ I →
                      Section1.IsIrreducibleCharacterOnGroup χ ∧
                        Section1.degree χ = (q * a : ℂ) := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  rcases theorem_9_8_initial_constituent_degree_count_source_bridge_sec9
      M MF U W1 W2 H0 C Uprime p q a u SH0 SH0C SH0U hcase hBarU
      hUprime hSH0 hSH0C hSH0U with
    ⟨I, hIsub, hIcard, hIdegree⟩
  have hDindex :
      Subgroup.index ((ambientDerivedSubgroup M).subgroupOf M) = q :=
    ambientDerived_subgroupOf_index_eq_q_of_hypothesis_9_2_sec9
      M MF U W1 W2 q hcase.1
  refine ⟨I, hIsub, hIcard, ?_⟩
  intro χ hχI
  rcases hIdegree χ hχI with ⟨hχirr, hθdegree⟩
  have hχSH0U : χ ∈ SH0U := hIsub hχI
  rcases hSH0U with ⟨_hYle, _hMFle, hmem⟩
  rcases (hmem χ).mp hχSH0U with ⟨θ, hθirr, hθnot, hθker, hχeq⟩
  have hθdeg : Section1.degree θ = (a : ℂ) :=
    hθdegree θ hθirr hθnot hθker hχeq
  have hχdeg : Section1.degree χ = (q * a : ℂ) := by
    rw [hχeq, Section1.degree_inducedClassFunction, hθdeg, hDindex]
  exact ⟨hχirr, hχdeg⟩

public theorem theorem_9_8_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
                kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                  case_9_7_a_characterData M MF U H0 C Uprime p q a u SH0 SH0C SH0U := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  rcases theorem_9_8_degree_divisibility_source_bridge_sec9 M MF U W1 W2 H0 C
      Uprime p q a u SH0 SH0C SH0U hcase hBarU hUprime hSH0 hSH0C
      hSH0U with
    ⟨hdegreeDiv, hunderlyingDiv⟩
  exact
    ⟨hdegreeDiv,
      hunderlyingDiv,
      hBarU,
      theorem_9_8_reducible_subfamily_source_bridge_sec9 M MF U W1 W2 H0 C
        Uprime p q a u SH0 SH0C SH0U hcase hBarU hUprime hSH0 hSH0C
        hSH0U,
      theorem_9_8_irreducible_H0C_linear_source_bridge_sec9 M MF U W1 W2 H0 C
        Uprime p q a u SH0 SH0C SH0U hcase hBarU hUprime hSH0 hSH0C
        hSH0U,
      theorem_9_8_initial_degree_count_source_bridge_sec9 M MF U W1 W2 H0 C
        Uprime p q a u SH0 SH0C SH0U hcase hBarU hUprime hSH0 hSH0C
        hSH0U⟩

public theorem theorem_9_8
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
      Uprime = (_root_.commutator U).map U.subtype →
      kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
            (∀ χ : Section1.ClassFunction M, χ ∈ SH0 → characterDegreeDivisibleBy a χ) ∧
            case_9_7_a_characterData M MF U H0 C Uprime p q a u SH0 SH0C SH0U := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  have hchar :
      case_9_7_a_characterData M MF U H0 C Uprime p q a u SH0 SH0C SH0U :=
    theorem_9_8_source_core_sec9 M MF U W1 W2 H0 C Uprime p q a u
      SH0 SH0C SH0U hcase hBarU hUprime hSH0 hSH0C hSH0U
  exact ⟨hchar.1, hchar⟩

end Section9
