module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.RankTwoSeedSource
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Ambient components from the rank of a seed's radical quotient

A nontrivial image of an intrinsic C-component has solvable kernel, so its
simple radical quotient is unchanged. If that quotient has three-rank at
least two, the image cannot have cyclic Sylow three-subgroups. Thus every
nonzero component coordinate of the full seed has three-rank at least two.
The semisimple three-rank bound in an SQTK group permits only one such
coordinate. Perfectness then lifts containment through the radical, and
the existing rank-two normality theorem gives relative normality and a
quasisimple two-core quotient of the containing component.

This extends the coordinate argument in RankTwoSeedSource to seeds with
nontrivial covering centers. The application in MathieuGeneration takes
the full residual of the actual J4 component involution centralizer, whose
simple radical quotient is M22. No simplicity of the seed's two-core
quotient is needed.

Source: Aschbacher--Smith 1.2.1(1),(3), printed p.504, and the ambient
component selection in 4.4.3, printed p.623.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
open IndexTwo
variable {G : Type*} [Group G] [Finite G]

private theorem three_rank_lower_of_surjective
    {B Q : Type*} [Group B] [Finite B] [Group Q] [Finite Q]
    (f : B →* Q) (hf : Function.Surjective f) (hr : 2 ≤ primeRank 3 Q) :
    2 ≤ primeRank 3 B := by
  by_contra hn
  let P : Sylow 3 B := Classical.choice inferInstance
  have hcyc := P.isCyclic_of_odd_of_primeRank_le_one (by decide) (show primeRank 3 B ≤ 1 by omega)
  have hq := P.primeRank_le_one_of_surjective hcyc f hf
  omega

private theorem nontrivial_radical_image_rank
    {B X : Type*} [Group B] [Finite B] [Group X] [Finite X]
    (hB : (⊤ : Subgroup B).IsCComponent)
    (hr : 2 ≤ primeRank 3 (B ⧸ solvableRadical B))
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
  let e := solvableRadicalQuotientEquiv f.rangeRestrict f.rangeRestrict_surjective
  apply three_rank_lower_of_surjective (QuotientGroup.mk' (solvableRadical f.range))
    (QuotientGroup.mk'_surjective _)
  rw [←primeRank_equiv 3 e]
  exact hr

/-- A seed with radical-quotient three-rank two in the layer lies in a unique component. -/
theorem unique_component_of_radical_quotient_rank
    (B : Subgroup G) [Group.IsPerfect B]
    (hB : (⊤ : Subgroup B).IsCComponent) (hrB : 2 ≤ primeRank 3 (B ⧸ solvableRadical B))
    (hBL : B ≤ cComponentLayer G)
    (hr : primeRank 3 (cComponentLayer (G ⧸ solvableRadical G)) ≤ 2) :
    ∃! K : Subgroup G, K.IsCComponent ∧ B ≤ K := by
  classical
  have hrB0 := three_rank_lower_of_surjective (QuotientGroup.mk' (solvableRadical B))
    (QuotientGroup.mk'_surjective _) hrB
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
    (nontrivial_radical_image_rank hB hrB (f K) hKf).trans (primeRank_subgroup_le 3 _)
  have hzero (J : ComponentIndex Q) (hJK : J ≠ K) : (f J).range = ⊥ := by
    by_contra hn
    have hJr : 2 ≤ primeRank 3 J.1 :=
      (nontrivial_radical_image_rank hB hrB (f J) hn).trans (primeRank_subgroup_le 3 _)
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

/-- A perfect seed with radical-quotient three-rank two has a unique normal containing
C-component, whose literal two-core quotient is quasisimple. -/
theorem radical_rank_component_source
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (B : Subgroup G) [Group.IsPerfect B]
    (hB : (⊤ : Subgroup B).IsCComponent) (hrB : 2 ≤ primeRank 3 (B ⧸ solvableRadical B)) :
    ∃! C : Subgroup G, C.IsCComponent ∧ B ≤ C ∧ C.Normal ∧
      IsQuasisimple (C ⧸ pCore 2 C) := by
  have hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  have hrB0 := three_rank_lower_of_surjective (QuotientGroup.mk' (solvableRadical B))
    (QuotientGroup.mk'_surjective _) hrB
  have hgen : cComponentLayer G = solvableResidual G :=
    proposition_1_2_1_one_of_A_3_9
      (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
        (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
        (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
          (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO)
      hQ
  have hBL : B ≤ cComponentLayer G := hgen.symm ▸ le_solvableResidual_of_isPerfect B
  obtain ⟨C,⟨hC,hBC⟩,hu⟩ :=
    unique_component_of_radical_quotient_rank B hB hrB hBL (radical_layer_threeRank hG)
  have hrC := hrB0.trans (primeRank_mono 3 hBC)
  exact ⟨C,⟨hC,hBC,rank_two_component_normal hG hC hrC,
    ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank hG hC hrC⟩,
    fun J hJ => hu J ⟨hJ.1,hJ.2.1⟩⟩
end CFSG.Quasithin.Chapter1.Section02
