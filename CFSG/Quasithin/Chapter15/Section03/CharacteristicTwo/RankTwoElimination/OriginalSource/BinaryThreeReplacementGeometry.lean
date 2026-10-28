module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCentralizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.OriginalSylowBridge

/-!
# Original Sylow geometry of the binary MS replacement

The characteristic replacement is normalized by the original Sylow subgroup.
Its central omega contains the intrinsic four and its conjugate complementary
plane, hence the whole original local module. It therefore lies in the original
module centralizer, while its overgroup does not contain the original plane
stabilizer. The final consumer supplies the literal original rank-two data.

Source: Aschbacher--Smith 15.3.23, printed pp.1128--1129, and
Meierfrankenfeld--Stellmacher (1993), (4.5), printed pp.895--900.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter15.Section03.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

private theorem characteristic_sylow_image_normalized (d : LocalData G) (L : Subgroup G)
    (C : Subgroup (d.S.subgroupOf (L ⊔ d.S))) [C.Characteristic] :
    (d.T : Subgroup G) ≤ normalizer
      ((C.map (d.S.subgroupOf (L ⊔ d.S)).subtype).map (L ⊔ d.S).subtype : Set G) := by
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hn : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hi)
  have hc := normalizer_le_normalizer_characteristic_map
    (L ⊔ d.S).subtype (L ⊔ d.S).subtype_injective (d.S.subgroupOf (L ⊔ d.S)) C
  rw [map_subgroupOf_eq_of_le (show d.S ≤ L ⊔ d.S from le_sup_right)] at hc
  exact hn.trans hc

theorem replacement_normalized_by_original_sylow (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b) :
    (d.T : Subgroup G) ≤ normalizer
      (t.reduction.ambient.map (L ⊔ d.S).subtype : Set G) := by
  let := t.reduction.characteristic
  exact characteristic_sylow_image_normalized d L t.reduction.subgroup

theorem module_le_replacement_omega (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    d.V ≤ omegaCenter (t.reduction.ambient.map (L ⊔ d.S).subtype) := by
  let W := (t.replacementOmega.map (d.S.subgroupOf (L ⊔ d.S)).subtype).map
    (L ⊔ d.S).subtype
  have hW : W = omegaCenter (t.reduction.ambient.map (L ⊔ d.S).subtype) := by
    rw [omegaCenter_map _ _ (L ⊔ d.S).subtype_injective,
      omegaCenter_map _ _ (d.S.subgroupOf (L ⊔ d.S)).subtype_injective]
    rfl
  let := t.replacementOmega_characteristic
  have hn : (d.T : Subgroup G) ≤ normalizer (W : Set G) :=
    characteristic_sylow_image_normalized d L t.replacementOmega
  have hfour : intrinsicFour L ≤ W := by
    have hm := map_mono (f := (L ⊔ d.S).subtype)
      (t.reducedCentralFour_le_replacementOmega common earlier)
    rw [reducedCentralFour_image_eq_complementary_plane d L e h hg b t common earlier,
      ← intrinsicFour_eq_complementary_plane_of_MS93 d L e h hg b t common earlier] at hm
    exact hm
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hnot : ¬ (d.T : Subgroup G) ≤ d.S := by
    intro hTS
    have ht : d.S.subgroupOf (d.T : Subgroup G) = ⊤ := by
      exact top_unique (fun x _ => hTS x.property)
    rw [ht, index_top] at hi
    omega
  obtain ⟨a,ha,haS⟩ := SetLike.not_le_iff_exists.mp hnot
  have hmoving : movingPlane d L ≤ W := by
    rw [← intrinsicFour_conjugate_eq_movingPlane_of_MS93 d L e h hg b t common earlier a ha haS]
    have hm := map_mono (f := (MulAut.conj a).toMonoidHom) hfour
    have he : W.map (MulAut.conj a).toMonoidHom = W :=
      mem_normalizer_iff_map_conj_eq.mp (hn ha)
    rw [he] at hm
    exact hm
  obtain ⟨i,j,hij,hm,hc,hact,hsup,hdis⟩ := hg.coordinates
  rw [← hW, ← hsup]
  refine sup_le hmoving ?_
  rw [← hc, ← intrinsicFour_eq_complementary_plane_of_MS93 d L e h hg b t common earlier]
  exact hfour

theorem replacement_le_original_radical (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    t.reduction.ambient.map (L ⊔ d.S).subtype ≤ d.R := by
  have hV := module_le_replacement_omega d L e h hg b t common earlier
  rw [h.radical]
  apply le_inf
  · exact ((map_mono (f := (L ⊔ d.S).subtype) (map_subtype_le t.reduction.subgroup)).trans
      (map_subgroupOf_eq_of_le (show d.S ≤ L ⊔ d.S from le_sup_right)).le).trans inf_le_left
  · intro x hx v hv
    exact ((mem_omegaCenter_iff.mp (hV hv)).2.2 x hx).symm

theorem original_sylow_not_le_replacement (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    ¬ d.S ≤ t.reduction.overgroup.map (L ⊔ d.S).subtype := by
  have hHR : d.R ≤ centralizer (intrinsicFour L : Set G) := by
    have hr := radical_centralizes_reducedCentralFour_image d L e h hg b t common earlier
    rw [reducedCentralFour_image_eq_complementary_plane d L e h hg b t common earlier,
      ← intrinsicFour_eq_complementary_plane_of_MS93 d L e h hg b t common earlier] at hr
    exact hr
  have hHL : L ≤ centralizer (intrinsicFour L : Set G) :=
    le_centralizer_iff.mp ((intrinsicFour_properties_of_MS93 d L b t common earlier).2.2.trans
      inf_le_right)
  have hcentral : t.reduction.overgroup.map (L ⊔ d.S).subtype ≤
      centralizer (intrinsicFour L : Set G) := by
    change (L.subgroupOf (L ⊔ d.S) ⊔ t.reduction.ambient).map (L ⊔ d.S).subtype ≤ _
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show L ≤ L ⊔ d.S from le_sup_left)]
    exact sup_le hHL ((replacement_le_original_radical d L e h hg b t common earlier).trans hHR)
  intro hS
  have hfix : fixedPlane (intrinsicFour L) d.S = intrinsicFour L :=
    inf_eq_left.mpr (le_centralizer_iff.mp (hS.trans hcentral))
  have hcard := intrinsicFour_fixed_line_card d L e h hg b t common earlier
  rw [hfix, (intrinsicFour_properties_of_MS93 d L b t common earlier).2.1] at hcard
  omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree.OriginalSource Chapter1 ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

theorem binary_three_source_replacement_geometry
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
    (d.T : Subgroup G) ≤ normalizer
        (t.reduction.ambient.map (c.L ⊔ d.S).subtype : Set G) ∧
      d.V ≤ omegaCenter (t.reduction.ambient.map (c.L ⊔ d.S).subtype) ∧
      t.reduction.ambient.map (c.L ⊔ d.S).subtype ≤ d.R ∧
      ¬ d.S ≤ t.reduction.overgroup.map (c.L ⊔ d.S).subtype := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  exact ⟨replacement_normalized_by_original_sylow d c.L b t,
    module_le_replacement_omega d c.L eSL h hg b t common earlier,
    replacement_le_original_radical d c.L eSL h hg b t common earlier,
    original_sylow_not_le_replacement d c.L eSL h hg b t common earlier⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
