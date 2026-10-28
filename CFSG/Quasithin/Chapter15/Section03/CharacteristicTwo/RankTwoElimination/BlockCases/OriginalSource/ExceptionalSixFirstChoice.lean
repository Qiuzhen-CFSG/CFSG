module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.ExceptionalSixSecondChoice
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.ExceptionalSixPlanes
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry
public import Theory.GroupTheory.PrimeRankResidualCentralizer
/-!
# The full exceptional Â₆ exclusion in original15.3.21

In the first source choice, commutator generation places the original
sixteen in U(L). The rank-two actor contains a nontrivial cubic scalar
modulo the two-core. Its action on either definite four-group is cubic,
so each component Sylow element whose fourth power lies in the core fixes
both four-groups. An element of quotient order four thus fixes sixteen
vectors, contradicting the bound of four in the faithful F₄³ module.

The final theorem combines this argument with the second-choice central
correction. It retains the full original selected context and constructs
all scalar, plane and Sylow transports. No marked-parabolic conclusion
is a hypothesis of this consumer.
Source: Aschbacher–Smith15.3.17,15.3.21,printed pp.1126–1127; C.1.22,p.129.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open ChapterC ChapterC.ExceptionalRestrictions
variable {G : Type*} [Group G] [Finite G]

/-- The selected rank-two actor contains a lift of a nontrivial scalar cubic. -/
theorem exceptionalSix_rank_two_cubic (h : IsExceptionalAhat6Block G)
    (hrG : primeRank 3 G ≤ 2) (H : Subgroup G) (hrH : primeRank 3 H = 2) :
    ∃ y : G, y ∈ H ∧ QuotientGroup.mk' (pCore 2 G) y ∈ center _ ∧
      QuotientGroup.mk' (pCore 2 G) y ≠ 1 ∧
      (QuotientGroup.mk' (pCore 2 G) y)^3 = 1 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hk : IsPGroup 2 q.ker := by
    change IsPGroup 2 (QuotientGroup.mk' (pCore 2 G)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hr : primeRank 3 (H.map q) = 2 := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hk,hrH]
  have hrQ : primeRank 3 (G ⧸ pCore 2 G) ≤ 2 := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup]
    exact hrG
  have hZ := cubic_center_le_of_rank_two (H.map q) hr.ge hrQ h.2.2.1
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center (G ⧸ pCore 2 G)) 3
    (by rw [h.2.2.1])
  have hz1 : (z : G ⧸ pCore 2 G) ≠ 1 := by
    intro he
    have he' : z = 1 := Subtype.ext he
    rw [he',orderOf_one] at hz
    contradiction
  obtain ⟨y,hy,hyz⟩ := hZ z.property
  refine ⟨y,hy,hyz.symm ▸ z.property,hyz.symm ▸ hz1,?_⟩
  change q y ^ 3 = 1
  rw [hyz]
  exact congrArg Subtype.val (hz ▸ pow_orderOf_eq_one z)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open ChapterC Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] [Finite G]

/-- In the first choice the original sixteen lies in the actual block U,
by its commutator generation inside the local omega-center. -/
theorem exceptionalSix_firstChoice_seed
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hm : IsExceptionalAhat6Block c.L) (hYL : d.Yplus ≤ c.L)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (hVW : d.V ≤ (starV c.L d.R).map (c.L ⊔ d.R : Subgroup G).subtype)
    (hcomm : d.V = ⁅d.V,d.Yplus⁆) :
    d.V ≤ (blockU c.L).map c.L.subtype := by
  let J := c.L ⊔ d.R
  let K := c.L.subgroupOf J
  let H := d.Yplus.subgroupOf J
  let V := d.V.subgroupOf J
  have hLJ : c.L ≤ J := le_sup_left
  have hYJ : d.Yplus ≤ J := hYL.trans hLJ
  have hVJ : d.V ≤ J := hVW.trans (map_subtype_le _)
  let hnormal : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le c.L.le_normalizer hR)
  let e : K ≃* c.L := subgroupOfEquivOfLe hLJ
  have hmK : IsExceptionalAhat6Block K := exceptionalSix_of_equiv e.symm hm
  have hVstar : V ≤ starV c.L d.R := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hVW hx
    exact (show y = x from Subtype.ext he) ▸ hy
  have hVcore : V ≤ pCore 2 J := hVstar.trans (map_subtype_le _)
  have hcommJ : V = ⁅V,H⁆ := by
    apply Subgroup.map_injective J.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVJ,map_subgroupOf_eq_of_le hYJ]
    exact hcomm
  have hVU : V ≤ (blockU K).map K.subtype := by
    rw [hcommJ]
    exact (commutator_mono hVcore (show H ≤ K from comap_mono hYL)).trans
      (commutator_le_core_commutator_of_isSubnormal K (pCore 2 J)
        hnormal.isSubnormal hmK.1.twoPerfect pCore_isPGroup le_normalizer_of_normal)
  intro x hx
  obtain ⟨k,hk,heq⟩ := hVU (show (⟨x,hVJ hx⟩ : J) ∈ V from hx)
  have hkU : e k ∈ blockU c.L := by
    rw [←RankOne.Solvable.blockU_map_equiv e]
    exact mem_map_of_mem e.toMonoidHom hk
  exact ⟨e k,hkU,congrArg Subtype.val heq⟩

/-- The first-choice planes force a component Sylow element of quotient order
four to fix sixteen vectors, contradicting its actual F₄³ fixed space. -/
theorem source_15_3_21_exceptionalSix_firstChoice
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus)
    (htwo : OutsideStructure.RankTwoCase d I) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hm : IsExceptionalAhat6Block c.L)
    (hfirst : d.Yplus = d.Y) : False := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  have hYL := source_15_3_17_exceptionalSix_containment hG d hempty hM hu hmany hI c hm
  have hrank := OutsideStructure.rankTwoCase_three_rank hG d hI htwo
  have hinput := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have hVW := RankTwoElimination.OriginalSource.component_seed_le_starV
    d hinput htwo.2.2.2.2.1
  have hcomm : d.V = ⁅d.V,d.Yplus⁆ := by
    obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
      hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
    obtain ⟨hi,_,_,_⟩ := source_lemma_15_3_7_of_orthogonal_action
      hG d.T hempty d.action hM hu hmany hne
    rw [hfirst]
    exact (d.action.commutator_eq_of_residual_image d.Y
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) hi).symm
  have hVU := exceptionalSix_firstChoice_seed d c hm hYL hinput.normalizes hVW hcomm
  have hVL : d.V ≤ c.L := hVU.trans (map_subtype_le _)
  have hVU' : d.V.subgroupOf c.L ≤ blockU c.L := by
    intro v hv
    obtain ⟨u,hu,he⟩ := hVU hv
    exact (show u = v from Subtype.ext he) ▸ hu
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  have hrL : primeRank 3 c.L ≤ 2 :=
    (_root_.primeRank_le_of_injective 3 (inclusion (component_le c)) (inclusion_injective _)).trans hrI
  have hrH : primeRank 3 (d.Yplus.subgroupOf c.L) = 2 := by
    rw [primeRank_congr 3 (subgroupOfEquivOfLe hYL),hrank]
  obtain ⟨y,hy,hyz,hyne,hy3⟩ := exceptionalSix_rank_two_cubic hm hrL
    (d.Yplus.subgroupOf c.L) hrH
  obtain ⟨P,hP⟩ := h11.sylow
  obtain ⟨Q,hQ⟩ := LinearThree.Extension.SourceCases.component_sylow d c P hP
  obtain ⟨t,ht,ht4⟩ := exceptionalSix_sylow_four hm Q
  have hfix (i : OrthogonalPlaneIndex) : (t : G) ∈ centralizer (d.action.plane i : Set G) := by
    let A := (d.action.plane i).subgroupOf c.L
    have hAL : d.action.plane i ≤ c.L := (d.action.plane_le i).trans hVL
    have hAU : A ≤ blockU c.L := (comap_mono (d.action.plane_le i)).trans hVU'
    have hcA : Nat.card A = 4 :=
      (Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv).trans (d.action.card_plane i)
    have hyN : y ∈ normalizer (A : Set c.L) := by
      rw [←subgroupOf_normalizer_eq hAL]
      exact OutsideStructure.LocalBranches.y_normalizes_plane d i (hfirst ▸ hy)
    have htN : t ∈ normalizer (A : Set c.L) := by
      rw [←subgroupOf_normalizer_eq hAL]
      have htS : (t : G) ∈ d.S := by
        change t ∈ d.S.subgroupOf c.L
        rw [←hQ]
        exact ht
      exact OutsideStructure.LocalBranches.s_normalizes_plane d i htS
    have htfix := exceptionalSix_cubic_plane_fixed hm A hAU hcA y t hyN htN
      hyz hyne hy3 (ht4 ▸ pow_orderOf_eq_one _)
    intro a ha
    exact congrArg Subtype.val (htfix ⟨a,hAL ha⟩ ha)
  have hVC : d.V ≤ centralizer ({(t : G)} : Set G) := by
    have hsup : d.action.plane 1 ⊔ d.action.plane (Multiplicative.ofAdd (1 : ZMod 2)) = d.V :=
      CFSG.Quasithin.Chapter15.Section03.RankTwo.natural_planes_sup d.action (by decide)
    rw [←hsup]
    apply sup_le
    · intro v hv
      exact mem_centralizer_singleton_iff.mpr (hfix 1 v hv)
    · intro v hv
      exact mem_centralizer_singleton_iff.mpr
        (hfix (Multiplicative.ofAdd (1 : ZMod 2)) v hv)
  have htfixV : t ∈ centralizer (d.V.subgroupOf c.L : Set c.L) := by
    intro v hv
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hVC hv)
  have hbound := exceptionalSix_four_fixed_card hm t ht4 (d.V.subgroupOf c.L) hVU' htfixV
  have hcard : Nat.card (d.V.subgroupOf c.L) = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv).trans d.action.card_vector
  omega

/-- Both original choices exclude an exceptional Â₆ block, with no additional
marked-plane, scalar-field or Sylow-action hypothesis. -/
theorem source_15_3_21_exceptionalSix
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus)
    (htwo : OutsideStructure.RankTwoCase d I) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hm : IsExceptionalAhat6Block c.L) : False := by
  rcases d.choice with hfirst | hsecond
  · exact source_15_3_21_exceptionalSix_firstChoice hG d hempty hM hu hmany hI htwo hf c hm hfirst
  · exact source_15_3_21_exceptionalSix_secondChoice hG d hempty hM hu hmany hI htwo hf c hm hsecond

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
