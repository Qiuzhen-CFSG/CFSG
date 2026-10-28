module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.RankTwoComponents
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SuzukiSourceAt
public import Theory.GroupTheory.CComponent.ThreeCore
public import Theory.GroupTheory.PResidual.PrimeToPerfect
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.Mathieu.M22.TripleCover.ScalarAutomorphisms

/-!
# The Mathieu residual at the same original G,T

A centerless component of three-rank two makes every distinct component
three-free. The original Suzuki exclusion makes every component have
positive three-rank, so the component is unique. The same rank bound kills
the three-core; the proved Fitting equality then gives F(I/O₂(I)) = 1.
A two-group outer automorphism group now forces I = K T and O²(I) = K.
This identifies the whole residual, retaining the intrinsic two-core.

The Mathieu application supplies all model premises from the actual
K/O₂(K) ≃ M₂₂. It puts the original point residual in K and proves full
movement of the same local span. The code-module contradiction is the
remaining step of the ordinary Mathieu exclusion.
All structural inputs in these exports concern the same original G,T.
No later 14.7.47 component conclusion is assumed.
Source: Aschbacher–Smith, A.3.18, 14.7.34–36,47–48,
printed pp.51–52,1056,1059,1064, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Every original local component has order divisible by three. The source
A.3.6 three-free classification and 14.7.33 exclude the only other possibility. -/
theorem local_component_three_dvd_card_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
  exact local_component_not_suzuki_at d h hab structural previous faithful earlier I hI K hK m hm
    ⟨(cComponentTwoCoreQuotientEquiv hK).trans e⟩


/-- The source rank and core bounds identify the entire two-residual,
not merely one selected component, in every centerless rank-two row
with two-group outer automorphisms. -/
theorem local_rank_two_component_eq_residual_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent)
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K))
    (ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K))) :
    (∀ D : Subgroup I, D.IsCComponent → D = K) ∧
      fittingSubgroup (HStar I) = ⊥ ∧
      K = primeToResidual 3 I ∧ pResidual 2 I = K ∧
      K.map I.subtype ⊔ (T : Subgroup G) = I ∧
      F.Li L 1 ≤ K.map I.subtype ∧
      ⁅F.UH I,K.map I.subtype⁆ = F.UH I := by
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    WholeResidualAssembly.GuardedSource.local_component_twoCore_isQuasisimple h hab structural previous faithful I hI K hK
  have hIr : primeRank 3 I ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup]
    exact (local_star_sqtk h I hI).stronglyQuasithin 3 (by decide) (by decide)
  have hu : ∀ D : Subgroup I, D.IsCComponent → D = K := by
    intro D hD
    by_contra hne
    exact (Nat.prime_three.coprime_iff_not_dvd.mp
      (hK.other_coprime_three_of_rank hz hr hIr hD hne))
      (local_component_three_dvd_card_at d h hab structural previous faithful earlier I hI D hD)
  let : K.Normal := hK.normal_of_unique hu
  have hf : fittingSubgroup (HStar I) = ⊥ := by
    rw [WholeResidualAssembly.GuardedSource.local_fitting_eq_threeCore h hab structural previous faithful I hI]
    exact hK.threeCore_twoCore_quotient_eq_bot hz hr hIr
  have hthree : K = primeToResidual 3 I :=
    hK.eq_primeToResidual_three_of_outer_twoGroup hz hr hIr ho
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  have hgen : K ⊔ (S : Subgroup I) = ⊤ :=
    hK.sylow_sup_eq_top_of_outer_twoGroup hu hf ho S
  have hp : IsPPerfect 2 K := by
    rw [hthree]
    exact isPPerfect_primeToResidual 3 2 (by decide)
  have hres : pResidual 2 I = K := pResidual_eq_of_isPPerfect_sup K
    (S : Subgroup I) hp S.isPGroup' hgen
  have hgenG : K.map I.subtype ⊔ (T : Subgroup G) = I := by
    have he := congrArg (map I.subtype) hgen
    rwa [Subgroup.map_sup,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI),
      ←MonoidHom.range_eq_map,range_subtype] at he
  have hLI := F.Li_one_le_of_mem_Hz hI
  have hLp : IsPPerfect 2 ((F.Li L 1).subgroupOf I) :=
    (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
      (subgroupOfEquivOfLe hLI).symm.toMonoidHom (subgroupOfEquivOfLe hLI).symm.surjective
  have hLK : F.Li L 1 ≤ K.map I.subtype := by
    have hm := map_mono (f := I.subtype) (le_pResidual_of_isPPerfect _ hLp)
    rwa [map_subgroupOf_eq_of_le hLI,hres] at hm
  have hn : I ≤ normalizer (K.map I.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using
      (inferInstance : K.Normal)
  let := h.chosen.elementary
  have hmove : ⁅F.UH I,K.map I.subtype⁆ = F.UH I :=
    (conjugateSpanBy_eq_commutator_of_seed V I (K.map I.subtype) (F.Li L 1)
      (map_subtype_le K) hn hLK (seed_commutator h F)).symm
  exact ⟨hu,hf,hthree,hres,hgenG,hLK,hmove⟩

/-- The literal ordinary Mathieu component satisfies every premise of the
rank-two residual reduction. This establishes the opening containment and
full-movement step in the M₂₂ branch of 14.7.36. -/
theorem local_mathieu_component_eq_residual_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) :
    (∀ D : Subgroup I, D.IsCComponent → D = K) ∧
      fittingSubgroup (HStar I) = ⊥ ∧
      K = primeToResidual 3 I ∧ pResidual 2 I = K ∧
      K.map I.subtype ⊔ (T : Subgroup G) = I ∧
      F.Li L 1 ≤ K.map I.subtype ∧
      ⁅F.UH I,K.map I.subtype⁆ = F.UH I := by
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply bot_unique
    intro z hz
    have hh := (centerCongr e ⟨z,hz⟩).property
    change e z ∈ center Sporadic.Mathieu.M22 at hh
    rw [Sporadic.Mathieu.m22_center_eq_bot,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
    rw [primeRank_congr 3 e,Sporadic.Mathieu.m22_primeRank_three]
  have ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv,pow_one]
    exact Sporadic.Mathieu.M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two
  exact local_rank_two_component_eq_residual_at d h hab structural previous faithful earlier
    I hI K hK hz hr ho

/-- At the full original point normalizer, a Mathieu component would be
the whole source K, with its actual intrinsic two-core quotient. -/
theorem original_mathieu_component_residual_marking_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22) :
    C.map F.H.subtype = K F ∧
      Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* Sporadic.Mathieu.M22) := by
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  have hc := (local_mathieu_component_eq_residual_at d h hab structural previous faithful
    earlier F.H hH C hC e).2.2.2.1
  have he : C.map F.H.subtype = K F := by
    rw [←hc]
    rfl
  let c : C ≃* K F := (equivMapOfInjective C F.H.subtype F.H.subtype_injective).trans
    (MulEquiv.subgroupCongr he)
  exact ⟨he,⟨(QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).symm.trans e⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
