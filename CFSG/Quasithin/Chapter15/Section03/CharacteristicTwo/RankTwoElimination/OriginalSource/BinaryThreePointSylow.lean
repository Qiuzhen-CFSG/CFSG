module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCentralizer
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Source

/-!
# The original plane stabilizer is Sylow in the intrinsic point centralizer

The intrinsic third commutator is one of the two literal definite planes.
The nonidentity S-fixed involution generates its fixed line, so the ambient
centralizer of that fixed line is exactly the centralizer of the involution.
The actual Sylow conclusion of source 15.3.6 transports through these two
identities. The original ordering maximum supplies the Baumann normalizer
control through source 14.1.12; no additional fusion premise remains.

This discharges the Sylow placement needed for applying the earlier local
component theorem to the outside point centralizer. The independent reduced
MS93 Earlier input remains explicit.

Source: Aschbacher--Smith 14.1.12 and 15.3.6, printed pp.978--979,1122,
and 15.3.23, printed pp.1128--1129.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter15.Section03.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

omit [Finite G] in
private theorem point_stabilizer_eq_S (d : LocalData G) (i : OrthogonalPlaneIndex) :
    planeStabilizer d.T (d.action.plane i) = d.S := by
  apply le_antisymm
  · intro x hx
    have hn : (⟨x, d.sylow_le hx.1⟩ : d.M) ∈
        (normalizer (d.action.plane i : Set G)).subgroupOf d.M := hx.2
    rw [d.action.plane_normalizer_eq_comap, OrthogonalGeometry.setwise_plane_eq_ker] at hn
    refine ⟨hx.1, ?_⟩
    change (⟨x, d.sylow_le hx.1⟩ : d.M) ∈
      (normalizer (d.action.plane 1 : Set G)).subgroupOf d.M
    rwa [d.action.plane_normalizer_eq_comap, OrthogonalGeometry.setwise_plane_eq_ker]
  · exact le_inf inf_le_left (OutsideStructure.LocalBranches.s_normalizes_plane d i)

/-- Source 15.3.6 makes the original plane stabilizer Sylow in the actual
centralizer of each nonidentity point on the intrinsic fixed line. -/
theorem intrinsicFour_point_sylow_of_MS93 (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hBaum : normalizer (ChapterB.baumann (d.T : Subgroup G) : Set G) ≤ d.M)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (z : G) (hz : z ∈ intrinsicFour L) (hz2 : orderOf z = 2)
    (hS : d.S ≤ centralizer ({z} : Set G)) :
    ∃ P : Sylow 2 (centralizer ({z} : Set G)),
      (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S := by
  obtain ⟨i,j,hij,hm,hc,_⟩ := hg.coordinates
  have hfour : intrinsicFour L = d.action.plane i :=
    (intrinsicFour_eq_complementary_plane_of_MS93 d L e h hg b t common earlier).trans hc
  have hline : fixedPlane (d.action.plane i) (planeStabilizer d.T (d.action.plane i)) =
      zpowers z := by
    symm
    apply eq_of_le_of_card_ge
    · apply zpowers_le.mpr
      refine ⟨hfour ▸ hz, ?_⟩
      rw [point_stabilizer_eq_S]
      intro s hs
      exact mem_centralizer_singleton_iff.mp (hS hs)
    · rw [Nat.card_zpowers, hz2,
        d.action.card_plane_fixed_planeStabilizer d.T d.sylow_le i]
  have hC : centralizer
      (fixedPlane (d.action.plane i) (planeStabilizer d.T (d.action.plane i)) : Set G) =
      centralizer ({z} : Set G) := by
    rw [hline, zpowers_eq_closure, centralizer_closure]
  have hs := (source_lemma_15_3_6 d.T d.action hM hBaum i).2.2.1
  rw [hC, point_stabilizer_eq_S] at hs
  exact hs

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree.OriginalSource Chapter1 ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original binary input gives an outside SQTK involution centralizer
with the original S as an actual Sylow subgroup. -/
theorem binary_three_source_point_sylow
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
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    ∃ z : G, z ∈ intrinsicFour c.L ∧ orderOf z = 2 ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      (d.T : Subgroup G) ⊓ centralizer ({z} : Set G) = d.S ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      IsSQTK KnownSimple.IsKnownSimple (centralizer ({z} : Set G)) ∧
      primeRank 3 (centralizer ({z} : Set G)) ≤ 2 ∧
      ∃ P : Sylow 2 (centralizer ({z} : Set G)),
        (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨z,hz,hz2,hLS,hCT⟩ := intrinsicFour_point_centralizer d c.L eSL h hg b t common earlier
  have hsq := hG.involution_centralizer_sqtk hz2
  exact ⟨z,hz,hz2,hLS,hCT,(fun hCM => c.outside (le_sup_left.trans (hLS.trans hCM))),
    hsq,hsq.stronglyQuasithin 3 (by decide) (by decide),
    intrinsicFour_point_sylow_of_MS93 d c.L eSL h hg hM hBaum b t common earlier z hz hz2
      (le_sup_right.trans hLS)⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
