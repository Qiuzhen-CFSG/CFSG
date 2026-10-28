module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalDisplacement
public import Theory.GroupTheory.PCoreImage

/-!
# The literal LR and LS boundary in original 15.3.23

The final original-source consumer is
`BinaryThreeLargeDistance.source_lemma_15_3_23_of_large_distance`, which feeds
`SourceRankTwo.BinaryFourAssembly.source_lemma_15_3_13_of_binary_three_large_distance`.
Its missing contradiction must retain the original simple QTKE group, local
selection, rank-two residuals, characteristic-two overgroup, component and
marked binary MS input. The false universal `EarlierMSClassifications` interface
cannot discharge this boundary. Existing conditional uses remain legacy APIs.

The source applies MS to LR. In the remaining large-distance configuration,
LR is a proper normal subgroup of LS, and its two-core is exactly
R intersect O₂(LS), strictly smaller than O₂(LS). Both groups nevertheless
have the same full commutator core [O₂(-),L]. The intrinsic third commutator
is fixed by LR, whereas its displacement by O₂(LS) has order two. In
particular the original S is not a Sylow subgroup of LR, since it is not
even contained there. Centrality in LR and the central-omega bound for S
therefore do not combine into the existing LS central-four contradiction.

The final theorem constructs these assertions from the full original inputs
and discharges the earlier MS path facts from nonabelianness and large
distance. It does not exclude the remaining point-centralizer embedding or
assert the complete corrected MS93 alternatives. Those source arguments and
final premise discharge remain with the original-source assembly owner.

Source: Aschbacher--Smith 15.3.23, printed pp.1128--1129, especially its
literal pair (LR,R); MS93 Sections 4 and 7 and Main Theorem (13), printed
pp.830--831. The distinction is also relevant to printed C.1.34(4).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

omit [Finite G] in
/-- The original S normalizes the literal source subgroup LR. -/
theorem radical_join_normalized (d : LocalData G) (L : Subgroup G)
    (hSL : d.S ≤ normalizer (L : Set G)) :
    L ⊔ d.S ≤ normalizer ((L ⊔ d.R : Subgroup G) : Set G) := by
  apply sup_le (le_sup_left.trans (L ⊔ d.R).le_normalizer)
  have hSR : d.S ≤ normalizer (d.R : Set G) :=
    le_sup_right.trans ((d.Yplus ⊔ d.S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (d.Yplus ⊔ d.S : Subgroup G))))
  exact (le_inf hSL hSR).trans (normalizer_inf_normalizer_le_normalizer_sup L d.R)

omit [Finite G] in
/-- Saturation identifies the smaller core with its literal intersection with R. -/
theorem radical_join_core_eq (d : LocalData G) (L : Subgroup G)
    (hSL : d.S ≤ normalizer (L : Set G)) (hRS : d.R ≤ d.S)
    (hsat : (L ⊔ d.R).pCoreIn 2 ≤ d.R) :
    (L ⊔ d.R).pCoreIn 2 = d.R ⊓ (L ⊔ d.S).pCoreIn 2 := by
  have hle : L ⊔ d.R ≤ L ⊔ d.S := sup_le_sup_left hRS L
  exact le_antisymm
    (le_inf hsat (pCoreIn_mono_of_normalizes hle (radical_join_normalized d L hSL)))
    ((inf_le_inf_right _ (show d.R ≤ L ⊔ d.R from le_sup_right)).trans
      (inf_pCoreIn_le_of_le 2 hle))

/-- Enlarging the literal source group from LR to LS preserves the full
commutator core, although their two-cores need not agree. -/
theorem radical_join_commutator_eq (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hSL : d.S ≤ normalizer (c.L : Set G))
    (hRS : d.R ≤ d.S) :
    ⁅(c.L ⊔ d.R).pCoreIn 2, c.L⁆ = ⁅(c.L ⊔ d.S).pCoreIn 2, c.L⁆ := by
  rw [overgroup_core_commutator_eq d c hSL]
  apply le_antisymm
  · exact (commutator_mono
      (pCoreIn_mono_of_normalizes (sup_le_sup_left hRS c.L)
        (radical_join_normalized d c.L hSL)) le_rfl).trans
      (overgroup_core_commutator_eq d c hSL).le
  · exact commutator_mono (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le c.L.le_normalizer (hRS.trans hSL))) le_rfl

/-- The original L and R both fix the same intrinsic third commutator. -/
theorem intrinsicFour_radical_join_centralizes (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    L ⊔ d.R ≤ centralizer (intrinsicFour L : Set G) := by
  have hR := radical_centralizes_reducedCentralFour_image d L e h hg b t common earlier
  rw [reducedCentralFour_image_eq_complementary_plane d L e h hg b t common earlier,
    ← intrinsicFour_eq_complementary_plane_of_MS93 d L e h hg b t common earlier] at hR
  exact sup_le (le_centralizer_iff.mp
    ((intrinsicFour_properties_of_MS93 d L b t common earlier).2.2.trans inf_le_right)) hR

/-- The same-marking core distinction and its two different actions. -/
theorem intrinsicFour_radical_boundary (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (hsat : (L ⊔ d.R).pCoreIn 2 ≤ d.R)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    (L ⊔ d.R).pCoreIn 2 = d.R ⊓ (L ⊔ d.S).pCoreIn 2 ∧
      (L ⊔ d.R).pCoreIn 2 < (L ⊔ d.S).pCoreIn 2 ∧
      L ⊔ d.R < L ⊔ d.S ∧ ¬ d.S ≤ L ⊔ d.R ∧
      ⁅intrinsicFour L, (L ⊔ d.R).pCoreIn 2⁆ = ⊥ ∧
      Nat.card (⁅intrinsicFour L, (L ⊔ d.S).pCoreIn 2⁆ : Subgroup G) = 2 := by
  have hRS := R_le_S d h.radical
  have he := radical_join_core_eq d L hg.component_normalized hRS hsat
  have hC := intrinsicFour_radical_join_centralizes d L e h hg b t common earlier
  have hz : ⁅intrinsicFour L, (L ⊔ d.R).pCoreIn 2⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (((L ⊔ d.R).pCoreIn_le 2).trans hC)
  have htwo : Nat.card (⁅intrinsicFour L, (L ⊔ d.S).pCoreIn 2⁆ : Subgroup G) = 2 := by
    rw [intrinsicFour_original_displacement_eq_fixedLine d L e h hg b t common earlier]
    exact intrinsicFour_fixed_line_card d L e h hg b t common earlier
  have hstrict : (L ⊔ d.R).pCoreIn 2 < (L ⊔ d.S).pCoreIn 2 := by
    apply lt_of_le_of_ne (he ▸ inf_le_right)
    intro heq
    rw [← heq,hz,card_bot] at htwo
    omega
  have hproper : L ⊔ d.R < L ⊔ d.S := by
    apply lt_of_le_of_ne (sup_le_sup_left hRS L)
    intro heq
    exact hstrict.ne (congrArg (fun H : Subgroup G => H.pCoreIn 2) heq)
  exact ⟨he,hstrict,hproper,(fun hS => not_le_of_gt hproper (sup_le le_sup_left hS)),hz,htwo⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The exact LR/LS distinction in the remaining original degree-three branch.
The full original ambient hypotheses and literal component marking are retained;
no universal MS classification or whole-fixed-factor equality is assumed. -/
theorem binary_three_large_distance_radical_boundary
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical) :
    ((c.L ⊔ d.R).subgroupOf (c.L ⊔ d.S)).Normal ∧
      ⁅(c.L ⊔ d.R).pCoreIn 2, c.L⁆ = ⁅(c.L ⊔ d.S).pCoreIn 2, c.L⁆ ∧
      (c.L ⊔ d.R).pCoreIn 2 = d.R ⊓ (c.L ⊔ d.S).pCoreIn 2 ∧
      (c.L ⊔ d.R).pCoreIn 2 < (c.L ⊔ d.S).pCoreIn 2 ∧
      c.L ⊔ d.R < c.L ⊔ d.S ∧
      ¬ Chapter1.IsSylowIn 2 d.S (c.L ⊔ d.R) ∧
      c.L ⊔ d.R ≤ centralizer (intrinsicFour c.L : Set G) ∧
      ⁅intrinsicFour c.L, (c.L ⊔ d.R).pCoreIn 2⁆ = ⊥ ∧
      Nat.card (⁅intrinsicFour c.L, (c.L ⊔ d.S).pCoreIn 2⁆ : Subgroup G) = 2 := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hRS := LinearThree.R_le_S d h.radical
  obtain ⟨he,hstrict,hproper,hS,hzero,htwo⟩ :=
    intrinsicFour_radical_boundary d c.L eSL h hg hcore b t common earlier
  refine ⟨(normal_subgroupOf_iff_le_normalizer (sup_le_sup_left hRS c.L)).mpr
      (radical_join_normalized d c.L hg.component_normalized),
    radical_join_commutator_eq d c hg.component_normalized hRS,he,hstrict,hproper,?_,
    intrinsicFour_radical_join_centralizes d c.L eSL h hg b t common earlier,hzero,htwo⟩
  intro hs
  exact hS (Chapter1.isSylowIn_iff.mp hs).2.1

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
