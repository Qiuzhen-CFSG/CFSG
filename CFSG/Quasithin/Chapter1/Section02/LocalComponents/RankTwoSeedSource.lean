module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRank
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.CComponent.RadicalKernel
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
public import Theory.GroupTheory.PrimeRankResidualCentralizer

/-!
# A simple-core rank-two seed selects a normal C-component

A perfect subgroup with simple two-core quotient has solvable proper kernels.
Every nonzero projection of such a subgroup retains its three-rank. Theorem A
bounds the three-rank of the actual semisimple radical-layer section, so a
rank-two seed has only one nonzero component coordinate. Perfectness lifts
containment through the radical. The nonnormal component rank bound then
forces relative normality, and A.3.6 gives a quasisimple two-core quotient.

The Section12.6 application uses the original L_v, not an abstract replacement.
The prime-to-three residual identification is proved in RankTwoSeedResidual.
Source: Aschbacher--Smith, 1.2.1 and 12.6.3, printed pp.504 and824.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
open IndexTwo
variable {G : Type*} [Group G] [Finite G]

private theorem nontrivial_image_rank
    {B X : Type*} [Group B] [Finite B] [Group X] [Finite X]
    [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hB : (⊤ : Subgroup B).IsCComponent) (hr : 2 ≤ primeRank 3 B)
    (f : B →* X) (hf : f.range ≠ ⊥) : 2 ≤ primeRank 3 f.range := by
  have hk : f.ker ≠ ⊤ := by
    intro he
    apply hf
    exact MonoidHom.range_eq_bot_iff.mpr (MonoidHom.ker_eq_top_iff.mp he)
  have hkr := kernel_le_solvableRadical_of_top_isCComponent hB f hk
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hkr)
  let : Group.IsSolvable f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  have hc : Nat.Coprime 3 (Nat.card f.rangeRestrict.ker) := by
    obtain ⟨n,hn⟩ := (PerfectCoreTwoExtension.ker_isTwoGroup f.rangeRestrict).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact hr.trans (primeRank_le_of_coprime_ker 3 f.rangeRestrict hc)

/-- A rank-two simple-core seed in the layer lies in a unique component. -/
theorem unique_component_of_simple_core_rank
    (B : Subgroup G) [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hB : (⊤ : Subgroup B).IsCComponent) (hrB : 2 ≤ primeRank 3 B)
    (hBL : B ≤ cComponentLayer G)
    (hr : primeRank 3 (cComponentLayer (G ⧸ solvableRadical G)) ≤ 2) :
    ∃! K : Subgroup G, K.IsCComponent ∧ B ≤ K := by
  classical
  let Q := G ⧸ solvableRadical G
  let E := cComponentLayer Q
  let q := QuotientGroup.mk' (solvableRadical G)
  have hfree : solvableRadical Q = ⊥ := solvableRadical_quotient_solvableRadical
  have hBne : B ≠ ⊥ := by
    intro he
    subst B
    have hz : primeRank 3 (⊥ : Subgroup G) = 0 := by
      apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
      simp
    omega
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hBne
  have hsol : ¬ Group.IsSolvable B := Group.IsPerfect.not_isSolvable B
  let f (K : ComponentIndex Q) : B →* K.1 :=
    (radicalProjection K).comp (inclusion hBL)
  have hfr (K : ComponentIndex Q) :
      (f K).range = (B.subgroupOf (cComponentLayer G)).map (radicalProjection K) := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact b.property
    · intro hx
      exact ⟨⟨x,hx⟩,rfl⟩
  obtain ⟨K,hK⟩ := exists_nontrivial_radicalProjection hsol hBL
  have hKf : (f K).range ≠ ⊥ := by rwa [hfr]
  have hKr : 2 ≤ primeRank 3 K.1 :=
    (nontrivial_image_rank hB hrB (f K) hKf).trans (primeRank_subgroup_le 3 _)
  have hzero (J : ComponentIndex Q) (hJK : J ≠ K) : (f J).range = ⊥ := by
    by_contra hn
    have hJr : 2 ≤ primeRank 3 J.1 :=
      (nontrivial_image_rank hB hrB (f J) hn).trans (primeRank_subgroup_le 3 _)
    let A := J.1.subgroupOf E
    let C := K.1.subgroupOf E
    let eJ := subgroupOfEquivOfLe (le_cComponentLayer J.property)
    let eK := subgroupOfEquivOfLe (le_cComponentLayer K.property)
    have hcomm : A ≤ centralizer (C : Set E) := by
      intro a ha c hc
      apply Subtype.ext
      exact (commutator_eq_bot_iff_le_centralizer.mp
        (J.property.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hfree K.property
          (fun he => hJK (Subtype.ext he)))) ha c hc
    have hcz : Nat.card (center C) = 1 := by
      rw [Nat.card_congr (centerCongr eK).toEquiv,
        center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hfree K.property.subnormal]
      simp
    have hadd := ResidualCentralizerRank.primeRank_add_le_of_center_coprime A C hcomm
      (show Nat.Coprime 3 (Nat.card (center C)) by rw [hcz]; decide)
    rw [primeRank_equiv 3 eJ,primeRank_equiv 3 eK] at hadd
    change primeRank 3 E ≤ 2 at hr
    omega
  have hBK : B.map q ≤ K.1 := by
    rintro x ⟨b,hb,rfl⟩
    let y : E := radicalLayerMap (inclusion hBL ⟨b,hb⟩)
    let k : K.1 := f K ⟨b,hb⟩
    have he : y = inclusion (le_cComponentLayer K.property) k := by
      apply (componentCoordinates hfree).injective
      apply funext
      intro J
      change componentProjection hfree J y =
        componentProjection hfree J (inclusion (le_cComponentLayer K.property) k)
      by_cases hJK : J = K
      · subst J
        exact (componentProjection_self hfree K k).symm
      · exact (mem_bot.mp (hzero J hJK ▸ (show f J ⟨b,hb⟩ ∈ (f J).range from
          ⟨⟨b,hb⟩,rfl⟩))).trans (componentProjection_other hfree K J (Ne.symm hJK) k).symm
    have hv := congrArg (fun a : E => (a : Q)) he
    change q b = (k : Q) at hv
    exact hv.symm ▸ k.property
  obtain ⟨C,hC,hCq⟩ := K.property.exists_map_quotient_eq (solvableRadical G)
  have hBC : B ≤ C := perfect_le_cComponent_of_map_le hC (solvableRadical G) (hCq.symm ▸ hBK)
  exact ⟨C,⟨hC,hBC⟩,fun J hJ => IndexTwo.cComponent_unique_over_nonsolvable hsol hJ.1 hC hJ.2 hBC⟩

/-- The actual semisimple section of a known-simple SQTK group has three-rank at most two. -/
theorem radical_layer_threeRank
    (hG : IsSQTK KnownSimple.IsKnownSimple G) :
    primeRank 3 (cComponentLayer (G ⧸ solvableRadical G)) ≤ 2 := by
  let Q := G ⧸ solvableRadical G
  rw [cComponentLayer_eq_componentLayer_of_solvableRadical_eq_bot
    (solvableRadical_quotient_solvableRadical (G := G))]
  have hsection : ChapterA.Section02.IsSectionOf (componentLayer Q) G :=
    (ChapterA.Section02.IsSectionOf.subgroup (componentLayer Q)).ambient_surjective
      (QuotientGroup.mk' (solvableRadical G)) (QuotientGroup.mk'_surjective _)
  have hsem : ChapterA.Section02.IsSemisimple (componentLayer Q) := componentLayer_idempotent
  exact (ChapterA.Section02.theoremA_knownSimple (G := G)).stronglyQuasithin_section
    hG.stronglyQuasithin hG.isKGroup hsection hsem 3 (by decide) (by decide)

end CFSG.Quasithin.Chapter1.Section02

namespace CFSG.Quasithin.Chapter1.Section02
open ChapterA.SQTKStructure
variable {G : Type*} [Group G] [Finite G]

private theorem sqtk_twoCore_quotient (hG : IsSQTK KnownSimple.IsKnownSimple G) :
    IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) := by
  refine ⟨?_,hG.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hG.stronglyQuasithin p hp ho)

/-- A C-component of three-rank two is normal in an SQTK group. -/
theorem rank_two_component_normal
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    {C : Subgroup G} (hC : C.IsCComponent) (hr : 2 ≤ primeRank 3 C) : C.Normal := by
  by_contra hn
  have hQ := sqtk_twoCore_quotient hG
  let := pCore_isNilpotent (p := 2) (G := G)
  let D := C.map (QuotientGroup.mk' (pCore 2 G))
  have hD : IsComponent (G ⧸ pCore 2 G) D := nonnormal_twoCore_image_isComponent hQ hC hn
  have hnD : ¬ D.Normal := fun hh => hn (cComponent_normal_of_quotient_normal hC _ hh)
  let := hD.2
  have hf : fittingSubgroup D ≤ center D :=
    (le_solvableRadical _ inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center
  have hm := (ordinary_model_of_central_fitting
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hQ D hD.isCComponent hf).2
  have hrD := NonnormalOuterSource.FourModels.odd_ranks_of_model hQ.stronglyQuasithin
    (pCore_quotient_pCore_eq_bot 2) D hD hnD hm 3 (by decide) (by decide)
  rw [←primeRank_equiv 3 (cComponentTwoCoreQuotientEquiv hC),
    primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 C) pCore_isPGroup] at hrD
  omega

/-- A perfect simple-core seed of three-rank two has a unique normal containing
C-component, whose literal two-core quotient is quasisimple. -/
theorem simple_core_rank_component_source
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (B : Subgroup G) [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hB : (⊤ : Subgroup B).IsCComponent) (hrB : 2 ≤ primeRank 3 B) :
    ∃! C : Subgroup G, C.IsCComponent ∧ B ≤ C ∧ C.Normal ∧
      IsQuasisimple (C ⧸ pCore 2 C) := by
  have hgen : cComponentLayer G = solvableResidual G :=
    proposition_1_2_1_one_of_A_3_9
      (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
        (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
        (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
          (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO)
      (sqtk_twoCore_quotient hG)
  have hBL : B ≤ cComponentLayer G := hgen.symm ▸ le_solvableResidual_of_isPerfect B
  obtain ⟨C,⟨hC,hBC⟩,hu⟩ :=
    unique_component_of_simple_core_rank B hB hrB hBL (radical_layer_threeRank hG)
  have hrC := hrB.trans (primeRank_mono 3 hBC)
  exact ⟨C,⟨hC,hBC,rank_two_component_normal hG hC hrC,
    ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank hG hC hrC⟩,
    fun J hJ => hu J ⟨hJ.1,hJ.2.1⟩⟩
end CFSG.Quasithin.Chapter1.Section02
