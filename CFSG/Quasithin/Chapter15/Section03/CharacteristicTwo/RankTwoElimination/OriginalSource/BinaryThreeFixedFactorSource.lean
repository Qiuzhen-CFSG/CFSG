module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalDisplacement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FixedFourElementary

/-!
# The whole fixed factor in the original binary-three source

Write F = C_[O₂(L),L](L) and H = [[Q,Q],Q]. The original orthogonal
planes identify F intersect V with H, without an order assumption on F.
Elementarity and the literal identity Ω₁Z(S) = C_V(S) then identify C_F(S)
with the order-two fixed line of H. Moreover every nontrivial subgroup of
F normalized by Y₊S contains H: its S-fixed points meet V, and the residual
action rules out an invariant line in that intersection.

These are statements on the original whole fixed factor and original S.
They do not identify F with H or lift fixed points from F/H. The final
consumer retains the actual outside subgroup and component and discharges
the earlier MS path facts from the nonabelian large-distance hypothesis.

Source: Aschbacher--Smith 15.3.8, 15.3.12 and 15.3.23, pp.1123--1129;
MS93 (4.5), pp.895--900.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter15.Section03.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The whole component-fixed factor meets the original module in exactly
the intrinsic third commutator, with no bound on the whole factor. -/
theorem coreFixed_inf_module_eq_intrinsicFour
    (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    coreFixed L ⊓ d.V = intrinsicFour L := by
  have hHF := (intrinsicFour_properties_of_MS93 d L b t common earlier).2.2
  have hplane := intrinsicFour_eq_complementary_plane_of_MS93 d L e h hg b t common earlier
  obtain ⟨i,j,_,hm,hc,_,hsup,_⟩ := hg.coordinates
  have hHV : intrinsicFour L ≤ d.V := by
    rw [hplane,hc]
    exact d.action.plane_le i
  have hsupH : movingPlane d L ⊔ intrinsicFour L = d.V := by
    rw [hplane,hc]
    exact hsup
  have hHL : intrinsicFour L ≤ centralizer (YL d L : Set G) :=
    (hHF.trans inf_le_right).trans (centralizer_le
      ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right))
  have hcomm : intrinsicFour L ≤ centralizer (movingPlane d L : Set G) := by
    let := d.action.elementary
    exact hHV.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (hm ▸ d.action.plane_le j)))
  apply le_antisymm ?_ (le_inf hHF hHV)
  rintro x ⟨hxF,hxV⟩
  have hxprod : x ∈ (movingPlane d L : Set G) * (intrinsicFour L : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _
      (hcomm.trans (Subgroup.centralizer_le_normalizer _)),hsupH]
    exact hxV
  obtain ⟨a,ha,w,hw,rfl⟩ := hxprod
  have hxc : a*w ∈ centralizer (YL d L : Set G) :=
    ((show coreFixed L ≤ centralizer (L : Set G) from inf_le_right).trans
      (centralizer_le ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right))) hxF
  have hac : a ∈ centralizer (YL d L : Set G) :=
    (centralizer (YL d L : Set G)).mul_mem_cancel_right (hHL hw) |>.mp hxc
  have ha1 : a = 1 := hg.plane_fixed.le ⟨ha,hac⟩
  simpa only [ha1,one_mul] using (show w ∈ intrinsicFour L from hw)

/-- The fixed subgroup of the entire factor under the original S is the
intrinsic fixed line, and has order two. -/
theorem coreFixed_original_sylow_fixed_line
    (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    fixedPlane (coreFixed L) d.S = fixedPlane (intrinsicFour L) d.S ∧
      Nat.card (fixedPlane (coreFixed L) d.S) = 2 := by
  let := coreFixed_elementary_of_MS93 d L b t common earlier
  have hFS : coreFixed L ≤ d.S :=
    inf_le_left.trans (commutatorCore_le_S d L h.core_le h.radical)
  have heq : fixedPlane (coreFixed L) d.S = fixedPlane (intrinsicFour L) d.S := by
    apply le_antisymm ?_
      (inf_le_inf_right _ (intrinsicFour_properties_of_MS93 d L b t common earlier).2.2)
    rintro x ⟨hx,hc⟩
    have hxO : x ∈ centralOmegaIn d.S :=
      (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨hFS hx,elemPow_eq_one_of_isElementaryAbelian x hx,hc⟩
    rw [← (source_lemma_15_3_8 d.T d.action d.sylow_le 1).1] at hxO
    refine ⟨?_,hc⟩
    rw [← coreFixed_inf_module_eq_intrinsicFour d L e h hg b t common earlier]
    exact ⟨hx,hxO.1⟩
  exact ⟨heq,heq ▸ intrinsicFour_fixed_line_card d L e h hg b t common earlier⟩

/-- Every nontrivial Y₊S-invariant subgroup of the whole fixed factor
contains the same intrinsic four. No assertion on the quotient F/H is used. -/
theorem intrinsicFour_le_normalized_coreFixed
    (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (A : Subgroup G) (hAF : A ≤ coreFixed L) (hne : A ≠ ⊥)
    (hn : d.Yplus ⊔ d.S ≤ normalizer (A : Set G)) :
    intrinsicFour L ≤ A := by
  let := coreFixed_elementary_of_MS93 d L b t common earlier
  let : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.of_injective (inclusion hAF) (inclusion_injective hAF)
  have hAS : A ≤ d.S := hAF.trans
    (inf_le_left.trans (commutatorCore_le_S d L h.core_le h.radical))
  let N := A.subgroupOf d.S
  let : N.Normal := normal_subgroupOf_of_le_normalizer (le_sup_right.trans hn)
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hne
  let : Nontrivial N := (subgroupOfEquivOfLe hAS).toEquiv.nontrivial
  let : Fact (IsPGroup 2 d.S) := ⟨d.T.isPGroup'.to_le inf_le_left⟩
  obtain ⟨x,hxne,hxZ⟩ := exists_nontrivial_center_mem_normal (p := 2) N
  have hxO : ((x : d.S) : G) ∈ centralOmegaIn d.S := by
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨(x : d.S).property,elemPow_eq_one_of_isElementaryAbelian _ x.property,?_⟩
    intro s hs
    exact congrArg Subtype.val (mem_center_iff.mp hxZ ⟨s,hs⟩)
  have hxV : ((x : d.S) : G) ∈ d.V := by
    rw [← (source_lemma_15_3_8 d.T d.action d.sylow_le 1).1] at hxO
    exact hxO.1
  let B := A ⊓ d.V
  have hBne : B ≠ ⊥ := by
    intro hb
    exact hxne (Subtype.ext (Subtype.ext (hb.le ⟨x.property,hxV⟩)))
  have hBH : B ≤ intrinsicFour L := by
    rw [← coreFixed_inf_module_eq_intrinsicFour d L e h hg b t common earlier]
    exact inf_le_inf_right _ hAF
  have hdiv : Nat.card B ∣ 4 := by
    rw [← (intrinsicFour_properties_of_MS93 d L b t common earlier).2.1]
    exact card_dvd_of_le hBH
  have hBtwo : Nat.card B ≠ 2 := by
    intro htwo
    have hYM : d.Yplus ≤ d.M := by
      rw [hg.first_choice]
      exact Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc
    have hYB : d.Yplus ≤ normalizer (B : Set G) :=
      (le_inf (le_sup_left.trans hn) (hYM.trans d.action.normalizes)).trans
        inf_normalizer_le_normalizer_inf
    have hBY : B ≤ centralizer (d.Yplus : Set G) :=
      le_centralizer_iff.mp (hYB.trans (normalizer_le_centralizer_of_card_two B htwo))
    have hz : fixedPlane d.V d.Yplus = ⊥ := by
      rw [hg.first_choice]
      exact d.action.fixedPlane_eq_bot_of_residual_image
        (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) h.image
    exact hBne (le_bot_iff.mp (hz ▸ le_inf inf_le_right hBY))
  have hB1 : Nat.card B ≠ 1 := fun hc => hBne (card_eq_one.mp hc)
  have hB3 : Nat.card B ≠ 3 := by
    intro hc
    rw [hc] at hdiv
    norm_num at hdiv
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hle := Nat.le_of_dvd (by decide : 0 < 4) hdiv
  have heq : B = intrinsicFour L := eq_of_le_of_card_ge hBH (by
    rw [(intrinsicFour_properties_of_MS93 d L b t common earlier).2.1]
    omega)
  exact heq ▸ inf_le_left

/-- The opposite residual has no nonidentity fixed point anywhere in the
whole component-fixed factor, not only in the intrinsic four. -/
theorem coreFixed_opposite_residual_fixed_eq_bot
    (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    coreFixed L ⊓ centralizer (YC d L : Set G) = ⊥ := by
  by_contra hne
  have hnF : d.Yplus ⊔ d.S ≤ normalizer (coreFixed L : Set G) :=
    (sup_le h.normalizes_component hg.component_normalized).trans
      (Extension.SourceCases.FixedFour.coreFixed_normalized L)
  have hn : d.Yplus ⊔ d.S ≤
      normalizer (coreFixed L ⊓ centralizer (YC d L : Set G) : Set G) :=
    (le_inf hnF (hg.centralizer_residual_normalized.trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hHC := (intrinsicFour_le_normalized_coreFixed d L e h hg b t common earlier
    _ inf_le_left hne hn).trans inf_le_right
  have hHL : intrinsicFour L ≤ centralizer (YL d L : Set G) :=
    ((intrinsicFour_properties_of_MS93 d L b t common earlier).2.2.trans inf_le_right).trans
      (centralizer_le ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right))
  have hHY : intrinsicFour L ≤ centralizer (d.Yplus : Set G) := by
    apply le_centralizer_iff.mp
    rw [h.generation]
    exact sup_le (le_centralizer_iff.mp hHL) (le_centralizer_iff.mp hHC)
  have hHV : intrinsicFour L ≤ d.V :=
    (coreFixed_inf_module_eq_intrinsicFour d L e h hg b t common earlier).symm.le.trans inf_le_right
  have hz : fixedPlane d.V d.Yplus = ⊥ := by
    rw [hg.first_choice]
    exact d.action.fixedPlane_eq_bot_of_residual_image
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) h.image
  have hbot : intrinsicFour L = ⊥ := le_bot_iff.mp (hz ▸ le_inf hHV hHY)
  have hcard := (intrinsicFour_properties_of_MS93 d L b t common earlier).2.1
  rw [hbot,card_bot] at hcard
  omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.CoreActions LinearThree.Extension.SourceCases
open LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal original large-distance source supplies the intersection,
fixed-line and invariant-subgroup conclusions for its whole fixed factor. -/
theorem binary_three_large_distance_fixed_factor_source
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
    coreFixed c.L ⊓ d.V = intrinsicFour c.L ∧
      fixedPlane (coreFixed c.L) d.S = fixedPlane (intrinsicFour c.L) d.S ∧
      Nat.card (fixedPlane (coreFixed c.L) d.S) = 2 ∧
      coreFixed c.L ⊓ centralizer (YC d c.L : Set G) = ⊥ ∧
      ∀ A : Subgroup G, A ≤ coreFixed c.L → A ≠ ⊥ →
        d.Yplus ⊔ d.S ≤ normalizer (A : Set G) → intrinsicFour c.L ≤ A := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  obtain ⟨hfix,hcard⟩ := coreFixed_original_sylow_fixed_line d c.L eSL h hg b t common earlier
  exact ⟨coreFixed_inf_module_eq_intrinsicFour d c.L eSL h hg b t common earlier,
    hfix,hcard,coreFixed_opposite_residual_fixed_eq_bot d c.L eSL h hg b t common earlier,
    intrinsicFour_le_normalized_coreFixed d c.L eSL h hg b t common earlier⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
