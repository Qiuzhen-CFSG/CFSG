module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Fitting
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero

/-!
# Odd ranks in the reciprocal ambient configuration

The index-two component is centerless modulo its two-core by A.3.8.
In the reversed group M=N_G(L), L is a normal C-component. Distinct
C-components commute modulo their two-cores, so the odd-prime ranks of
L and the actual outside component add. Strong quasithinness gives
m_p(K)≤1 for every odd prime dividing |L|. All reciprocal witnesses and
the original quotient maps are retained.

This proves the rank clause of 4.2.10; containment and normality are not
assumed or asserted here. Source: Aschbacher--Smith, pp.609--610.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G]

private theorem quotient_sqtk (hG : IsSQTK KnownSimple.IsKnownSimple G) :
    IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) := by
  refine ⟨?_,hG.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hG.stronglyQuasithin p hp ho)

/-- The actual intrinsic quotient of a nonnormal C-component is centerless. -/
theorem coreQuotient_center_eq_bot_of_nonnormal
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    {B : Subgroup G} (hB : B.IsCComponent) (hn : ¬ B.Normal) :
    center (B ⧸ pCore 2 B) = ⊥ := by
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  have hQ := quotient_sqtk hG
  let D := B.map (QuotientGroup.mk' (pCore 2 G))
  have hD : IsComponent (G ⧸ pCore 2 G) D :=
    Chapter1.Section02.nonnormal_twoCore_image_isComponent hQ hB hn
  have hnD : ¬ D.Normal := fun hh => hn (cComponent_normal_of_quotient_normal hB _ hh)
  let : IsQuasisimple D := hD.2
  have hf : fittingSubgroup D ≤ center D :=
    (le_solvableRadical _ inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center
  have hm := (ChapterA.SQTKStructure.ordinary_model_of_central_fitting
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hQ D hD.isCComponent hf).2
  have hz := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.center_eq_bot_of_model
    (hQ.stronglyQuasithin 3 (by decide) (by decide))
    (pCore_quotient_pCore_eq_bot 2) D hD hnD hm
  apply (eq_bot_iff_card _).mpr
  rw [Nat.card_congr (centerCongr (cComponentTwoCoreQuotientEquiv hB)).toEquiv,hz]
  exact Nat.card_unique

/-- The reciprocal index-two conclusion kills the original core quotient center. -/
theorem reciprocal_coreQuotient_center_eq_bot {L H : Subgroup G}
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hd : ReciprocalData L H) :
    center (L ⧸ pCore 2 L) = ⊥ := by
  obtain ⟨he,hL,hn,hi,_⟩ := hd
  have hLH : L ≤ H := he ▸ (map_subtype_le _).trans inf_le_right
  have hnon : ¬ (L.subgroupOf H).Normal := by
    intro hh
    let := hh
    rw [normalizer_eq_top] at hn
    rw [←hn,index_top] at hi
    norm_num at hi
  have hz := coreQuotient_center_eq_bot_of_nonnormal hH hL hnon
  let e := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hLH))
  apply (eq_bot_iff_card _).mpr
  rw [←Nat.card_congr (centerCongr e).toEquiv,hz]
  exact Nat.card_unique

/-- Distinct local components leave at most one odd-prime rank beside the
centerless normal original component, for every odd prime in its order. -/
theorem rank_le_one_of_distinct_normal_component
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (B K : Subgroup G) (hB : B.IsCComponent) (hK : K.IsCComponent) [B.Normal]
    (hne : K ≠ B) (hz : center (B ⧸ pCore 2 B) = ⊥)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hp : p ∣ Nat.card B) :
    primeRank p K ≤ 1 := by
  have hc := (Chapter1.Section02.proposition_1_2_1_two_of_A_3_7
    (fun X _ _ => ChapterA.Section03.CComponentCommutation.universal_A_3_7 X)
    (quotient_sqtk hG) hK hB hne).1.trans inf_le_right
  have hr := ResidualCentralizerRank.primeRank_sum_le_of_normal_factor ho K B
    ((commutator_mono (map_subtype_le _) le_rfl).trans hc)
    (by rw [hz]; simp)
  have hpos : 0 < primeRank p B := Nat.pos_of_ne_zero
    (fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hp)
  have htwo := hG.stronglyQuasithin p (Fact.out) ho
  omega

/-- The rank assertion of 4.2.10 holds for the actual outside component
selected in the reciprocal argument, with primes measured in the original L. -/
theorem reciprocal_component_odd_rank {L H : Subgroup G}
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hM : IsSQTK KnownSimple.IsKnownSimple (normalizer (L : Set G)))
    (hd : ReciprocalData L H)
    (K : Subgroup (normalizer (L : Set G))) (hK : K.IsCComponent)
    (hout : ¬ K ≤ H.subgroupOf (normalizer (L : Set G))) :
    ∀ p : ℕ, p.Prime → Odd p → p ∣ Nat.card L → primeRank p K ≤ 1 := by
  let M := normalizer (L : Set G)
  let B := L.subgroupOf M
  have hLH : L ≤ H := hd.1 ▸ (map_subtype_le _).trans inf_le_right
  let a : (L.subgroupOf H) ≃* L := subgroupOfEquivOfLe hLH
  let b : B ≃* L := subgroupOfEquivOfLe L.le_normalizer
  have ht : (⊤ : Subgroup L).IsCComponent := by
    simpa only [subgroupOf_self,map_top_of_surjective a.toMonoidHom a.surjective]
      using (hd.2.1.subgroupOf le_rfl).map_equiv a
  have htB : (⊤ : Subgroup B).IsCComponent := by
    simpa only [map_top_of_surjective b.symm.toMonoidHom b.symm.surjective]
      using ht.map_equiv b.symm
  let : B.Normal := (normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl
  have hB : B.IsCComponent := by
    simpa only [←MonoidHom.range_eq_map,range_subtype]
      using htB.map_subtype (inferInstance : B.Normal).isSubnormal
  have hne : K ≠ B := fun he => hout (he ▸ comap_mono hLH)
  have hz := reciprocal_coreQuotient_center_eq_bot hH hd
  let e := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have hzB : center (B ⧸ pCore 2 B) = ⊥ := by
    apply (eq_bot_iff_card _).mpr
    rw [Nat.card_congr (centerCongr e).toEquiv,hz]
    exact Nat.card_unique
  intro p hp ho hdiv
  let : Fact p.Prime := ⟨hp⟩
  exact rank_le_one_of_distinct_normal_component hM B K hB hK hne hzB ho
    (by rwa [Nat.card_congr b.toEquiv])

/-- The reciprocal witnesses with the source odd-prime rank restriction.
This is an output of the ambient construction, not an extra source premise. -/
@[expose] def ReciprocalRankCase (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ((generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H →
      ReciprocalData L H ∧
      twoFittingCore (normalizer (L : Set G)) ≤ H.subgroupOf (normalizer (L : Set G)) ∧
      center (L ⧸ pCore 2 L) = ⊥ ∧
      ∃ K : Subgroup (normalizer (L : Set G)),
        K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        generalizedFitting K = pCore 2 K ∧ ¬ K ≤ H.subgroupOf (normalizer (L : Set G)) ∧
        (¬ ⁅(conjugateSpanBy L H).subgroupOf (normalizer (L : Set G)),K⁆ ≤
          pCore 2 (normalizer (L : Set G))) ∧
        ∀ p : ℕ, p.Prime → Odd p → p ∣ Nat.card L → primeRank p K ≤ 1)

/-- The original fixed residual supplies the odd-prime rank assertion on
the same outside component of the reversed maximal-local configuration. -/
theorem reciprocal_rank_case_of_not_unique {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (ho : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (Section04.oddActorResidual L A) (normalizer (L : Set G))) :
    ReciprocalRankCase L V A := by
  obtain ⟨J,H,W,hw,hr⟩ := reciprocal_component_case_of_not_unique h D hM A hAN hcomm ho hAV hnot
  refine ⟨J,H,W,hw,?_⟩
  intro hf
  obtain ⟨hd,hfit,K,hK,hq,hfK,hout,hmoved⟩ := hr hf
  have hH := hw.2.2.2.2.2.2.1.sqtk
  exact ⟨hd,hfit,reciprocal_coreQuotient_center_eq_bot hH hd,K,hK,hq,hfK,hout,hmoved,
    reciprocal_component_odd_rank hH (h.simpleQTKE.twoLocal_sqtk hM.1.1) hd K hK hout⟩

end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
