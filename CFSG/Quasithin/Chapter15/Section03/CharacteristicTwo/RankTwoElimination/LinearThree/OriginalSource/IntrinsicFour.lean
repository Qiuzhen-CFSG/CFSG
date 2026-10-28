module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FixedFourPlane
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.OriginalCharacteristicFour
/-!
# An intrinsic four-group in the original binary component

The actual MS93 source four is the third lower-central subgroup of the
commutator core. This identity makes its image invariant under every
normalizer of the original component. The first-choice orthogonal geometry
therefore places that entire four in V and identifies it with [V,Y_C].
Both planes now lie in the original commutator core, and elements of T
outside S exchange the intrinsic four with the moving plane.

The fixed-factor order assumption of FixedFourPlane is discharged for this
intrinsic source four. No identification with the entire component-fixed
factor is used. The original R fixes the source four; fixation by the
possibly larger O₂(LS) remains a separate issue.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5), printed pp.895--900;
Aschbacher--Smith 15.3.23, printed pp.1128--1129.
-/

public section
open Subgroup
open scoped Pointwise
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter15.Section03.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The intrinsic third lower-central subgroup of the original component core. -/
@[expose] def intrinsicFour (L : Subgroup G) : Subgroup G :=
  ⁅⁅commutatorCore L, commutatorCore L⁆, commutatorCore L⁆

omit [Finite G] in
private theorem normalizer_le_normalizer_third (K : Subgroup G) :
    normalizer (K : Set G) ≤ normalizer (⁅⁅K,K⁆,K⁆ : Subgroup G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp hg]

omit [Finite G] in
/-- Component normalization preserves the intrinsic third commutator. -/
theorem intrinsicFour_normalized (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer (intrinsicFour L : Set G) :=
  (normalizer_le_normalizer_commutatorCore L).trans
    (normalizer_le_normalizer_third (commutatorCore L))

private theorem intrinsicFour_eq_map (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    intrinsicFour L = t.reducedCentralFour.map (L ⊔ d.S).subtype := by
  rw [t.reducedCentralFour_eq_third_commutator common earlier,
    map_commutator, map_commutator]
  change ⁅⁅commutatorCore L, commutatorCore L⁆, commutatorCore L⁆ =
    ⁅⁅(sourceQ (L.subgroupOf (L ⊔ d.S))).map (L ⊔ d.S).subtype,
      (sourceQ (L.subgroupOf (L ⊔ d.S))).map (L ⊔ d.S).subtype⁆,
      (sourceQ (L.subgroupOf (L ⊔ d.S))).map (L ⊔ d.S).subtype⁆
  rw [sourceQ_map_subtype le_sup_left b.component]

/-- The literal MS93 input makes this intrinsic subgroup an elementary four fixed by L. -/
theorem intrinsicFour_properties_of_MS93 (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    IsElementaryAbelian 2 (intrinsicFour L) ∧ Nat.card (intrinsicFour L) = 4 ∧
      intrinsicFour L ≤ coreFixed L := by
  rw [intrinsicFour_eq_map d L b t common earlier]
  have hF := t.reducedCentralFour_elementary common earlier
  let := hF
  refine ⟨IsElementaryAbelian.map (L ⊔ d.S).subtype, ?_, ?_⟩
  · rw [card_map_of_injective (L ⊔ d.S).subtype_injective]
    exact t.reducedCentralFour_card common earlier
  · apply (map_mono (le_inf (t.reducedCentralFour_le_commutatorCore common earlier)
      (t.reducedCentralFour_centralizes_component earlier))).trans
    change (sourceFixed (L.subgroupOf (L ⊔ d.S))).map (L ⊔ d.S).subtype ≤ coreFixed L
    rw [sourceFixed_map le_sup_left b.component]

private theorem normalized_fixed_four_eq_plane (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (H : Subgroup G) [IsElementaryAbelian 2 H] (hcard : Nat.card H = 4)
    (hHS : H ≤ d.S) (hn : d.Yplus ⊔ d.S ≤ normalizer (H : Set G))
    (hHL : H ≤ centralizer (L : Set G)) : H = ⁅d.V, YC d L⁆ := by
  have hHV := normalized_four_le_module d hg.first_choice h.image H hcard hHS hn
  obtain ⟨i,j,hij,hL,hC⟩ := hg.factors
  have hm : movingPlane d L = d.action.plane j := by
    change ⁅d.V, YL d L⁆ = _
    rw [hL]
    exact (residualY_fullActionCoordinateFacts d.action h.image).commutator i j hij
  have hc : ⁅d.V, YC d L⁆ = d.action.plane i := by
    rw [hC]
    exact (residualY_fullActionCoordinateFacts d.action h.image).commutator j i hij.symm
  have hW : d.action.plane i ≤ centralizer (YL d L : Set G) := by
    rw [hL]
    exact le_centralizer_iff.mp (centralizingFactor_le _ _)
  have hcomm : d.action.plane i ≤ centralizer (movingPlane d L : Set G) := by
    let := d.action.elementary
    exact (d.action.plane_le i).trans
      ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le (hm ▸ d.action.plane_le j)))
  have hsup : movingPlane d L ⊔ d.action.plane i = d.V := by
    rw [hm]
    exact natural_planes_sup d.action hij.symm
  rw [hc]
  apply eq_of_le_of_card_ge
  · intro x hx
    have hxV : x ∈ (movingPlane d L : Set G) * (d.action.plane i : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _
        (hcomm.trans (Subgroup.centralizer_le_normalizer _)), hsup]
      exact hHV hx
    obtain ⟨u,hu,w,hw,rfl⟩ := hxV
    have hxc : u*w ∈ centralizer (YL d L : Set G) :=
      (hHL.trans (centralizer_le ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right))) hx
    have huc : u ∈ centralizer (YL d L : Set G) :=
      (centralizer (YL d L : Set G)).mul_mem_cancel_right (hW hw) |>.mp hxc
    have hu1 : u = 1 := hg.plane_fixed.le ⟨hu,huc⟩
    simpa only [hu1,one_mul] using (show w ∈ d.action.plane i from hw)
  · rw [d.action.card_plane, hcard]

/-- The original residual geometry identifies the intrinsic four without a fixed-factor bound. -/
theorem intrinsicFour_eq_complementary_plane_of_MS93 (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    intrinsicFour L = ⁅d.V, YC d L⁆ := by
  obtain ⟨he,hcard,hle⟩ := intrinsicFour_properties_of_MS93 d L b t common earlier
  let := he
  exact normalized_fixed_four_eq_plane d L e h hg _ hcard
    ((hle.trans inf_le_left).trans (commutatorCore_le_S d L h.core_le h.radical))
    ((sup_le h.normalizes_component hg.component_normalized).trans (intrinsicFour_normalized L))
    (hle.trans inf_le_right)

/-- Both original definite planes lie in the component core, with the order premise discharged. -/
theorem module_le_commutatorCore_of_MS93 (d : LocalData G)
    {I : Subgroup G} (c : ComponentWitness d I)
    [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (b : BinaryMS.Input κ (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    d.V ≤ commutatorCore c.L := by
  obtain ⟨i,_,_,_,hc,_,hsup,_⟩ := hg.coordinates
  have hfour : intrinsicFour c.L = d.action.plane i :=
    (intrinsicFour_eq_complementary_plane_of_MS93 d c.L e h hg b t common earlier).trans hc
  rw [← hsup, ← hfour]
  exact sup_le ((movingPlane_le_coreCenter d c hg.component_normalized h.core_le h.radical).trans
    (map_subtype_le _))
    ((intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.2.trans inf_le_left)
/-- The literal included replacement four is the original complementary plane. -/
theorem reducedCentralFour_image_eq_complementary_plane (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    t.reducedCentralFour.map (L ⊔ d.S).subtype = ⁅d.V, YC d L⁆ := by
  rw [← intrinsicFour_eq_map d L b t common earlier]
  exact intrinsicFour_eq_complementary_plane_of_MS93 d L e h hg b t common earlier

/-- The original radical fixes the actual included source four. -/
theorem radical_centralizes_reducedCentralFour_image (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    d.R ≤ centralizer (t.reducedCentralFour.map (L ⊔ d.S).subtype : Set G) := by
  rw [← intrinsicFour_eq_map d L b t common earlier]
  obtain ⟨he,hcard,hle⟩ := intrinsicFour_properties_of_MS93 d L b t common earlier
  let := he
  exact radical_centralizes_normalized_four d hg.first_choice h.image _ hcard
    ((hle.trans inf_le_left).trans (commutatorCore_le_S d L h.core_le h.radical))
    ((sup_le h.normalizes_component hg.component_normalized).trans (intrinsicFour_normalized L))

/-- Every element of T outside S exchanges the intrinsic four and the moving plane. -/
theorem intrinsicFour_conjugate_eq_movingPlane_of_MS93 (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (a : G) (ha : a ∈ (d.T : Subgroup G)) (haS : a ∉ d.S) :
    (intrinsicFour L).conjBy a = movingPlane d L := by
  obtain ⟨i,j,hij,hm,hc,_⟩ := hg.coordinates
  rw [intrinsicFour_eq_complementary_plane_of_MS93 d L e h hg b t common earlier, hc, hm]
  exact outside_S_exchanges_planes d hij a ha haS

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
