module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeAmbientSourceNormalizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.OriginalEarlier
public import Theory.GroupTheory.FourGroupDisplacement
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# The displacement point in the original degree-three branch

Let F be the intrinsic third commutator of Q = [O₂(L),L]. The large-distance
source identifies F with the complementary original plane. Since F centralizes
L and O₂(LS)L = LS, its displacement by the original two-core equals its
S-displacement. A nontrivial two-group action on a four-group has displacement
of order two, fixed by S. Hence [F,O₂(LS)] is exactly the original S-fixed line.

The literal source application identifies its generator with the involution
used in the point-centralizer argument. It preserves the full Sylow placement
and the rank bound for N_G(L) intersect C_G(z), and discharges CommonFacts and
Earlier from nonabelianness and large distance. This is an original-core action
calculation, not centrality in the characteristic replacement.

The remaining 15.3.23 contradiction must exclude the ambient configuration at
this displacement point. A proper local component in its point quotient is
not excluded by the normalizer rank bound alone. Final source assembly remains
with qt-rank-two-ms93; no full MS classification is asserted here.

Source: Aschbacher–Smith 15.3.23, printed pp.1128–1129; MS93 (4.4)–(4.5),
printed pp.890–900, and its characteristic replacement in Section 7.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter15.Section03.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The displacement by the original two-core is exactly the original
Sylow-fixed line of the intrinsic four. -/
theorem intrinsicFour_original_displacement_eq_fixedLine
    (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    ⁅intrinsicFour L, (L ⊔ d.S).pCoreIn 2⁆ = fixedPlane (intrinsicFour L) d.S := by
  let F := intrinsicFour L
  let J := L ⊔ d.S
  have h4 : Nat.card F = 4 := (intrinsicFour_properties_of_MS93 d L b t common earlier).2.1
  have h2 : Nat.card (fixedPlane F d.S) = 2 :=
    intrinsicFour_fixed_line_card d L e h hg b t common earlier
  have hLF : L ≤ centralizer (F : Set G) :=
    le_centralizer_iff.mpr ((intrinsicFour_properties_of_MS93 d L b t common earlier).2.2.trans inf_le_right)
  have hJF : J ≤ normalizer (F : Set G) :=
    (sup_le L.le_normalizer hg.component_normalized).trans (intrinsicFour_normalized L)
  have hSF : d.S ≤ normalizer (F : Set G) := le_sup_right.trans hJF
  have hcore : L ⊔ J.pCoreIn 2 = J := by
    have hm := congrArg (map J.subtype) b.core_sup_component
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left),
      ← MonoidHom.range_eq_map, range_subtype] at hm
    exact sup_comm _ _ |>.trans hm
  have hdisp : ⁅F,J.pCoreIn 2⁆ = ⁅F,d.S⁆ :=
    (commutator_eq_of_centralizing_sup hcore hLF ((J.pCoreIn_le 2).trans hJF)).trans
      (commutator_eq_of_centralizing_sup (rfl : L ⊔ d.S = J) hLF hSF).symm
  rw [hdisp]
  have hne : ⁅F,d.S⁆ ≠ ⊥ := by
    intro hb
    have he : fixedPlane F d.S = F :=
      inf_eq_left.mpr (commutator_eq_bot_iff_le_centralizer.mp hb)
    rw [he,h4] at h2
    omega
  have hp : IsPGroup 2 d.S := d.T.isPGroup'.to_le inf_le_left
  have hd2 := commutator_four_card_of_ne_bot F d.S hSF hp h4 hne
  exact eq_of_le_of_card_ge
    (le_inf (le_normalizer_iff_commutator_le_left.mp hSF)
      (commutator_four_le_centralizer F d.S hSF hp h4)) (by rw [hd2,h2])

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
include hG hempty hM hu hmany hI htwo hf e b t common earlier

/-- Original 15.3.23 identifies the original-core displacement with its
nontrivial fixed line, retaining the literal component and Sylow subgroup. -/
theorem binary_three_source_original_displacement_eq_fixedLine :
    ⁅intrinsicFour c.L, (c.L ⊔ d.S).pCoreIn 2⁆ = fixedPlane (intrinsicFour c.L) d.S ∧
      Nat.card (⁅intrinsicFour c.L, (c.L ⊔ d.S).pCoreIn 2⁆ : Subgroup G) = 2 := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  have he := intrinsicFour_original_displacement_eq_fixedLine d c.L eSL h hg b t common earlier
  exact ⟨he,he ▸ intrinsicFour_fixed_line_card d c.L eSL h hg b t common earlier⟩

omit common earlier in
/-- The point used by the original ambient argument is precisely the
nonidentity original-core displacement. All earlier MS path premises are
discharged from the nonabelian large-distance input. -/
theorem binary_three_large_distance_displacement_point
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical) :
    ∃ z : G, orderOf z = 2 ∧
      ⁅intrinsicFour c.L, (c.L ⊔ d.S).pCoreIn 2⁆ = zpowers z ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      (d.T : Subgroup G) ⊓ centralizer ({z} : Set G) = d.S ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      primeRank 3 (normalizer (c.L : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) ≤ 1 ∧
      ∃ P : Sylow 2 (centralizer ({z} : Set G)),
        (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S := by
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  obtain ⟨z,hz,hz2,hLS,hTS,hout,_,_,P,hP⟩ :=
    binary_three_source_point_sylow hG d hempty hM hu hmany hI htwo hf c e b t common earlier
  have hz1 : z ≠ 1 := by intro he; rw [he,orderOf_one] at hz2; omega
  obtain ⟨he,hcard⟩ := binary_three_source_original_displacement_eq_fixedLine
    hG d hempty hM hu hmany hI htwo hf c e b t common earlier
  have hline : ⁅intrinsicFour c.L, (c.L ⊔ d.S).pCoreIn 2⁆ = zpowers z := by
    symm
    apply eq_of_le_of_card_ge
    · apply zpowers_le.mpr
      rw [he]
      exact ⟨hz,fun s hs => mem_centralizer_singleton_iff.mp (hLS (mem_sup_right hs))⟩
    · rw [Nat.card_zpowers,hz2,hcard]
  exact ⟨z,hz2,hline,hLS,hTS,hout,
    (binary_three_source_point_normalizer_rank
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz hz1).2,P,hP⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
