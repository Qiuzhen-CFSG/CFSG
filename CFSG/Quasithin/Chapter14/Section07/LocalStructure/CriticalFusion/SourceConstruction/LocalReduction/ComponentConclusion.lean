module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentCatalogue
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SuzukiExclusion
public import Theory.GroupTheory.PPrimeCoreSurjection
public import Theory.Quasithin.CoprimeRank
public import Theory.Quasithin.PositiveLocalRank

/-!
# Original component catalogue, rank and three-prime core

The quadratic-actor catalogue and the actual Suzuki Borel exclusion leave
only the concrete F.9.18 component models. Nonnormality persists in the
reduced local because it contains the original Sylow subgroup; its surviving
models are binary PSL₂ and PSL₃(2). The source three-free classification now
forces every component to have positive three-rank, hence rank one or two.
A nonzero three-prime core would supply an excluded Suzuki component.
Pullback through the literal quotient gives O₃′(I) = O₂(I).

The final application produces a genuine escaping component in the full
point normalizer, with its model, rank and core conclusions. It does not
identify that component with the full residual or assert component normality.

Source: Aschbacher–Smith, 14.7.30 and 14.7.33–35, printed pp.1055–1056,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The component catalogue for an arbitrary original local, with the Suzuki
row excluded by its actual point/Borel action. -/
theorem local_component_catalogue
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) :
    Models.ComponentModel (K ⧸ pCore 2 K) :=
  (local_component_catalogue_or_suzuki h hab structural previous faithful I hI K hK).of_no_suzuki
    (local_component_not_suzuki d h hab structural previous faithful earlier I hI K hK)

/-- The remaining nonnormal branch of 14.7.32 consists of actual binary
PSL₂ or PSL₃(2) quotients. Nonnormality is retained on passing to the
reduced local because that local contains the original Sylow subgroup. -/
theorem local_nonnormal_component_models
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) (hn : ¬ K.Normal) :
    (∃ n, 2 ≤ n ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 := by
  let N := conjugateSpanBy (K.map I.subtype) (T : Subgroup G)
  let J := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  let KJ := (K.map I.subtype).subgroupOf J
  obtain ⟨_,hJI,hJ⟩ := local_component_reduced_mem_Hz h structural I hI K hK
  have hKJle : K.map I.subtype ≤ J := (le_conjugateSpanBy _ _).trans le_sup_left
  have hKI : ((K.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hK
  have hKJ : KJ.IsCComponent := hKI.subgroupOf_of_le hKJle hJI
  have hgen : conjugateSpanBy KJ ((T : Subgroup G).subgroupOf J) ⊔
      (F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_conjugateSpanBy,map_subgroupOf_eq_of_le hKJle,
      map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ),
      map_subgroupOf_eq_of_le (show F.Li L 1 ⊔ (T : Subgroup G) ≤ J from le_sup_right)]
    simpa only [←MonoidHom.range_eq_map] using (range_subtype J).symm
  have hnJ : ¬ KJ.Normal := by
    intro hnJ
    have hnorm := (normal_subgroupOf_iff_le_normalizer hKJle).mp hnJ
    have hTnorm : (T : Subgroup G) ≤ normalizer (K.map I.subtype : Set G) :=
      (F.sylow_le_of_mem_Hz hJ).trans hnorm
    have hrel := subgroupOf_mono I hTnorm
    rw [subgroupOf_normalizer_eq (map_subtype_le K)] at hrel
    have hS : ((T : Subgroup G).subgroupOf I) ≤ normalizer (K : Set I) := by
      simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hrel
    have hi := ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
      (local_star_sqtk h I hI) hK).resolve_left hn).1
    exact (T.subtype (F.sylow_le_of_mem_Hz hI)).not_dvd_index
      (by simpa only [hi, Sylow.coe_subtype] using index_dvd_of_le hS)
  let e : K ≃* KJ := (equivMapOfInjective K I.subtype I.subtype_injective).trans
    (subgroupOfEquivOfLe hKJle).symm
  let eq : (K ⧸ pCore 2 K) ≃* (KJ ⧸ pCore 2 KJ) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hm := ((local_reduced_component_catalogue h hab structural previous faithful
    J hJ KJ hKJ hgen).2 hnJ).transport eq
  rcases hm with hm | ⟨m,hm,he⟩ | hm
  · exact Or.inl hm
  · exact (local_component_not_suzuki d h hab structural previous faithful earlier I hI K hK m hm he).elim
  · exact Or.inr hm

/-- Every original local component has order divisible by three. The source
A.3.6 three-free classification and 14.7.33 exclude the only other possibility. -/
theorem local_component_three_dvd_card
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) : 3 ∣ Nat.card K := by
  by_contra hthree
  let B := K.map (QuotientGroup.mk' (pCore 2 I))
  let : Group.IsNilpotent (pCore 2 I) := pCore_isPGroup.isNilpotent
  have hB : B.IsCComponent := hK.map_quotient (pCore 2 I)
  have hB3 : ¬ 3 ∣ Nat.card B := fun hd => hthree (hd.trans (card_map_dvd _ _))
  have hc := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    (HStar I) (local_star_sqtk h I hI) (pCore_quotient_pCore_eq_bot 2) B hB
  obtain ⟨m,hm,⟨e⟩⟩ := hc.suzuki_of_three_free hB3
  exact local_component_not_suzuki d h hab structural previous faithful earlier I hI K hK m hm
    ⟨(cComponentTwoCoreQuotientEquiv hK).trans e⟩

/-- Source 14.7.34 on the original component, before taking its two-core quotient. -/
theorem local_component_threeRank
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) : primeRank 3 K = 1 ∨ primeRank 3 K = 2 := by
  have hlo := Theory.Quasithin.one_le_primeRank_of_dvd_card
    (local_component_three_dvd_card d h hab structural previous faithful earlier I hI K hK)
  have hr : primeRank 3 K ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup,
      primeRank_congr 3 (cComponentTwoCoreQuotientEquiv hK)]
    exact (primeRank_subgroup_le 3 _).trans ((local_star_sqtk h I hI).stronglyQuasithin 3 (by decide) (by decide))
  omega

/-- Unrestricted three-prime-core vanishing on the actual local star quotient.
A nonzero core would supply a genuine Suzuki component, excluded by 14.7.33. -/
theorem local_threePrimeCore_eq_bot
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    pPrimeCore 3 (HStar I) = ⊥ := by
  by_contra hne
  obtain ⟨K,hK,_,_,m,hm,he⟩ := local_threePrime_component h hab structural previous faithful I hI hne
  exact local_component_not_suzuki d h hab structural previous faithful earlier I hI K hK m hm he

/-- Source 14.7.35 with the original intrinsic cores: O₃′(I) = O₂(I). -/
theorem local_threePrimeCore_eq_twoCore
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    pPrimeCore 3 I = pCore 2 I := by
  let q := QuotientGroup.mk' (pCore 2 I)
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := I)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hc := pPrimeCore_comap_eq_of_surjective_coprime 3 q (QuotientGroup.mk'_surjective _) hcop
  rw [local_threePrimeCore_eq_bot d h hab structural previous faithful earlier I hI,
    MonoidHom.comap_bot,QuotientGroup.ker_mk'] at hc
  exact hc.symm

/-- The original full point normalizer now has a classified actual component
of three-rank one or two and no three-prime core beyond its two-core.
This does not identify the component with the full two-residual. -/
theorem original_exists_classified_component
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u}) :
    pPrimeCore 3 F.H = pCore 2 F.H ∧
      ∃ K : Subgroup F.H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        ¬ K.map F.H.subtype ≤ normalizer (L : Set G) ∧
        Models.ComponentModel (K ⧸ pCore 2 K) ∧
        (primeRank 3 K = 1 ∨ primeRank 3 K = 2) := by
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  obtain ⟨K,hK,hq,hout⟩ := local_exists_quasisimple_component d h hab structural previous faithful earlier F.H hH
  exact ⟨local_threePrimeCore_eq_twoCore d h hab structural previous faithful earlier F.H hH,
    K,hK,hq,hout,local_component_catalogue d h hab structural previous faithful earlier F.H hH K hK,
    local_component_threeRank d h hab structural previous faithful earlier F.H hH K hK⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
