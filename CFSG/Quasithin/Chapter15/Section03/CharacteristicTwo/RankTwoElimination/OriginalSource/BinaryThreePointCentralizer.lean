module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.IntrinsicFour
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.Geometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThree

/-!
# An original involution centralizer in the large binary branch

The intrinsic third commutator is the complementary definite plane. Its
fixed subgroup under S therefore has order two. The nonidentity point z is
fixed by L and S, while an element of T outside S moves it into the disjoint
moving plane. Hence LS lies in C_G(z) and C_T(z) = S.

The original-input consumer supplies the residual geometry and applies the
ambient quasithin hypothesis to this literal involution centralizer. It lies
outside M and has odd-prime ranks at most two. This identifies a source-specific
overgroup for further analysis; it does not assert that S is Sylow in C_G(z)
or complete the rank-two exclusion. The independent reduced MS93 Earlier
input remains explicit, and no original-two-core fixation premise is used.

Source: Aschbacher--Smith 15.3.8 and 15.3.23, printed pp.1123,1128--1129;
Meierfrankenfeld--Stellmacher (1993), (4.5), printed pp.895--900.
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
private theorem stabilizer_eq_S (d : LocalData G) (i : OrthogonalPlaneIndex) :
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

/-- The actual intrinsic four has exactly one nonidentity S-fixed point. -/
theorem intrinsicFour_fixed_line_card (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    Nat.card (fixedPlane (intrinsicFour L) d.S) = 2 := by
  obtain ⟨i,j,hij,hm,hc,_⟩ := hg.coordinates
  rw [intrinsicFour_eq_complementary_plane_of_MS93 d L e h hg b t common earlier, hc]
  rw [← stabilizer_eq_S d i]
  exact d.action.card_plane_fixed_planeStabilizer d.T d.sylow_le i

/-- Its fixed point centralizes LS and has centralizer precisely S inside T. -/
theorem intrinsicFour_point_centralizer (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    ∃ z : G, z ∈ intrinsicFour L ∧ orderOf z = 2 ∧
      L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      (d.T : Subgroup G) ⊓ centralizer ({z} : Set G) = d.S := by
  let K := fixedPlane (intrinsicFour L) d.S
  have hcard : Nat.card K = 2 := intrinsicFour_fixed_line_card d L e h hg b t common earlier
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (by rw [hcard])
  have hz2 : orderOf (z : G) = 2 := (orderOf_injective K.subtype K.subtype_injective z).trans hz
  have hzH : (z : G) ∈ intrinsicFour L := z.property.1
  have hS : d.S ≤ centralizer ({(z : G)} : Set G) := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr (z.property.2 s hs)
  have hL : L ≤ centralizer ({(z : G)} : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr
      (((intrinsicFour_properties_of_MS93 d L b t common earlier).2.2 hzH).2 l hl)
  refine ⟨z,hzH,hz2,sup_le hL hS,le_antisymm ?_ (le_inf inf_le_left hS)⟩
  intro a ha
  by_contra haS
  have hconj := intrinsicFour_conjugate_eq_movingPlane_of_MS93 d L e h hg b t common earlier a ha.1 haS
  have hzU : (z : G) ∈ movingPlane d L := by
    rw [← hconj]
    refine mem_map.mpr ⟨z,hzH,?_⟩
    change a * (z : G) * a⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp ha.2, mul_inv_cancel_right]
  obtain ⟨i,j,hij,hm,hc,hmov,hsup,hdis⟩ := hg.coordinates
  have hzP : (z : G) ∈ d.action.plane i := by
    rw [← hc, ← intrinsicFour_eq_complementary_plane_of_MS93 d L e h hg b t common earlier]
    exact hzH
  have hz1 : (z : G) = 1 := hdis.le_bot ⟨hzU,hzP⟩
  simp only [hz1,orderOf_one] at hz2
  omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original rank-two binary input produces an actual outside SQTK
involution centralizer. Its three-rank bound is inherited from G. -/
theorem binary_three_source_point_centralizer
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
      primeRank 3 (centralizer ({z} : Set G)) ≤ 2 := by
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
    hsq,hsq.stronglyQuasithin 3 (by decide) (by decide)⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
