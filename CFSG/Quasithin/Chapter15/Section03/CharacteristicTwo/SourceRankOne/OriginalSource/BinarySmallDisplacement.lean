module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightSmallDisplacement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryFirstPlane
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryLargeCenter
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryAssembly

/-!
# Excluding the original large binary component by its first line

The original first plane has commutator exactly the involution line Z_S ∩ V₁
with the component's commutator core. This line is fixed by the original local
group. Three-subgroup rotation places the displacement of [V₁,L] inside that
line; the genuine large-core small-displacement theorem makes [V₁,L]
centralize the core. A second rotation, using [Q,L]=Q, forces [V₁,Q]=1,
contradicting the nontrivial first line.

All core and line inclusions are transported through the actual component
and replacement embeddings. No centrality of the original two-core on the
replacement's fixed four-group is assumed. The replacement wrapper retains
only the earlier prescribed critical-path replacement theorem.

Source: Aschbacher--Smith 15.3.31, printed p.1132; C.1.34(4), printed
pp.136--137; Meierfrankenfeld--Stellmacher (1993), section 7.
-/

public section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinarySmallDisplacement
open RankOneConfiguration SmallExtension SmallExtension.CentralCover SmallExtension.CentralCover.LinearThree
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass} {d : LocalData G}
  {I : Subgroup G} {c : ComponentWitness d I} (s : SourceData κ d c)

include s
private theorem core_full_commutation :
    ⁅extensionCore c.L,c.L⁆ = extensionCore c.L := by
  let := component_isPerfect_of_containment d c s.contains
  exact commutator_isPPerfect_idempotent c.L (c.L.pCoreIn 2)
    (by
      intro N hN hp
      let := hN
      by_contra hne
      let : Nontrivial (c.L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
      let : Group.IsNilpotent (c.L ⧸ N) := hp.isNilpotent
      exact Group.IsPerfect.not_isSolvable (c.L ⧸ N) inferInstance) (isPGroup_pCoreIn 2 c.L)
    (c.L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image c.L (pCore 2 c.L)))

private theorem line_normalized
    (hfixed : d.ZS ⊓ d.V₁ ≤ centralizer (c.L : Set G)) :
    I ≤ normalizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G) := by
  rw [s.generated]
  apply sup_le
  · exact (le_centralizer_iff.mp hfixed).trans (Subgroup.centralizer_le_normalizer _)
  · exact (le_centralizer_iff.mp
      (show d.ZS ⊓ d.V₁ ≤ centralizer (d.S : Set G) from
        inf_le_left.trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)

private theorem first_commutator_near_center
    (hfixed : d.ZS ⊓ d.V₁ ≤ centralizer (c.L : Set G))
    (hline : ⁅d.V₁,extensionCore c.L⁆ ≤ d.ZS ⊓ d.V₁) :
    ⁅⁅d.V₁,c.L⁆,extensionCore c.L⁆ ≤ d.ZS ⊓ d.V₁ := by
  have hn := line_normalized s hfixed
  have hQI : extensionCore c.L ≤ I :=
    (le_normalizer_iff_commutator_le_right.mp
      ((pCoreIn_le 2 c.L).trans c.L.le_normalizer)).trans (component_le c)
  apply commutator_commutator_le_of_rotate_of_le_normalizer
    (s.first_plane_control.1.trans hn) ((component_le c).trans hn) (hQI.trans hn)
  · rw [commutator_comm c.L,core_full_commutation s,commutator_comm]
    exact hline
  · exact (commutator_mono (by rwa [commutator_comm] :
        ⁅extensionCore c.L,d.V₁⁆ ≤ d.ZS ⊓ d.V₁) le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr hfixed).le |>.trans bot_le

private theorem first_plane_centralizes_core_of_near_center
    (hfixed : d.ZS ⊓ d.V₁ ≤ centralizer (c.L : Set G))
    (hline : ⁅d.V₁,extensionCore c.L⁆ ≤ d.ZS ⊓ d.V₁)
    (hVL : ⁅d.V₁,c.L⁆ ≤ extensionCore c.L)
    (hnear : ∀ A : Subgroup G, A ≤ extensionCore c.L →
      ⁅A,extensionCore c.L⁆ ≤ d.ZS ⊓ d.V₁ →
      A ≤ centralizer (extensionCore c.L : Set G)) :
    ⁅d.V₁,extensionCore c.L⁆ = ⊥ := by
  have hc := hnear _ hVL (first_commutator_near_center s hfixed hline)
  have hzero : ⁅⁅extensionCore c.L,c.L⁆,d.V₁⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm c.L d.V₁]
      exact commutator_eq_bot_iff_le_centralizer.mpr hc
    · exact commutator_eq_bot_iff_le_centralizer.mpr (hline.trans hfixed)
  rw [core_full_commutation s,commutator_comm] at hzero
  exact hzero


private def recoordinate (m : CenterModel c.L natural) (a : SL) : CenterModel c.L natural where
  quotientIso := m.quotientIso.trans (MulAut.conj a)
  moduleIso := m.moduleIso.trans (LinearModels.FullCenter.actionEquiv (ρ := natural) a)
  intertwining l z := by
    change Multiplicative.ofAdd (natural a (m.coordinates (centerConjugate c.L l z)).toAdd) = _
    rw [m.coordinates_conjugate]
    apply congrArg Multiplicative.ofAdd
    change natural a (natural (m.actorMap l) (m.coordinates z).toAdd) =
      natural (a * m.actorMap l * a⁻¹) (natural a (m.coordinates z).toAdd)
    rw [map_mul,map_mul]
    simp only [Module.End.mul_apply,inv_self_apply]
  core_centralizes := m.core_centralizes

private theorem first_plane_commutator_le_core
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (m : CenterModel c.L natural) : ⁅d.V₁,c.L⁆ ≤ extensionCore c.L := by
  let W := MarkedModelAssembly.G2Coordinates.quotientPlane m d.V₂
  have hi := MarkedModelAssembly.G2Coordinates.planeMap_injective m
    s.plane_le_coreCenter s.contains (s.line.plane_fixed_trivial d)
  have hc : Nat.card W = 4 :=
    (MarkedModelAssembly.G2Coordinates.quotientPlane_card m s.plane_le_coreCenter hi).trans
      (d.action.card_plane _)
  have hd : Module.finrank (ZMod 2) W = 2 := MarkedModelAssembly.plane_dimension W hc
  have hn : d.M ⊓ c.L ≤ normalizer (d.V₂ : Set G) := by
    rw [s.component_parabolic]
    exact inf_le_right
  have hp : ((d.M ⊓ c.L).subgroupOf c.L).map m.actorMap =
      LinearModels.PlaneGeometry.stabilizer W := by
    apply Subgroup.eq_of_le_of_card_ge
      (MarkedModelAssembly.G2Coordinates.quotientPlane_stabilized m s.plane_le_coreCenter hn)
    change Nat.card (LinearModels.PlaneGeometry.stabilizer W) ≤ _
    rw [s.binary_centerModel_parabolic_card hm m,natural_plane_stabilizer_card W hd]
  obtain ⟨a,ha⟩ := LinearModels.PlaneGeometry.exists_plane_coordinates W hd
  have hY : d.Yplus.subgroupOf c.L = (primeToResidual 3 ((d.M ⊓ c.L).subgroupOf c.L)).map
      ((d.M ⊓ c.L).subgroupOf c.L).subtype := by
    rw [s.component_residual]
    apply Subgroup.map_injective (f := c.L.subtype) Subtype.val_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans inf_le_right),
      map_embedded_primeToResidual_of_hom, map_subgroupOf_eq_of_le inf_le_right]
  obtain ⟨ht,hr⟩ := LinearModels.PlaneGeometry.marked_mem_image m.actorMap
    ((d.M ⊓ c.L).subgroupOf c.L) (d.Yplus.subgroupOf c.L) hY W hp a ha
  have hstar := s.binary_star_centralizer_of_coefficients (recoordinate m a) ht hr
  exact (commutator_mono (le_inf s.first_plane_control.1 s.first_plane_control.2.1) le_rfl).trans
    (s.commutator_le_core_of_star_centralizer hstar)

private theorem false_of_near_center
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (m : CenterModel c.L natural)
    (hnear : ∀ A : Subgroup G, A ≤ extensionCore c.L →
      ⁅A,extensionCore c.L⁆ ≤ d.ZS ⊓ d.V₁ →
      A ≤ centralizer (extensionCore c.L : Set G)) : False := by
  obtain ⟨he,hfixed⟩ := BinaryFirstPlane.firstLine_action_of_centerModel s hm m
  have hz := first_plane_centralizes_core_of_near_center s hfixed he.le
    (first_plane_commutator_le_core s hm m) hnear
  have hc := BinaryFirstPlane.firstLine_card (d := d)
  rw [← he,hz,card_bot] at hc
  omega


omit s [Finite G] in
private theorem original_core_map (s : SourceData KnownSimple.IsKnownSimple d c) :
    (ChapterC.BinaryMS.commutatorCore (c.L.subgroupOf I)).map I.subtype = extensionCore c.L := by
  change (⁅pCore 2 I,c.L.subgroupOf I⁆).map I.subtype = _
  rw [map_commutator,map_subgroupOf_eq_of_le (component_le c)]
  change ⁅I.pCoreIn 2,c.L⁆ = extensionCore c.L
  rw [extensionCore_eq_overgroup d c s.contains s.normal]

omit s in
private theorem false_of_local_core
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* LinearThree.SL)
    (t : ChapterC.BinaryMS.MS93.InputSetup (source_binaryMSInput s e))
    (common : ChapterC.BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    False := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (c.L ⧸ pCore 2 c.L) := (e.trans Matrix.PSL3Two.equiv).isSimpleGroup
  let m := source_binary_large_centerModel s e t common earlier
  obtain ⟨he,hfixed⟩ := BinaryFirstPlane.firstLine_action_of_centerModel s hm m
  have hlineQ : d.ZS ⊓ d.V₁ ≤ extensionCore c.L := by
    rw [← he]
    exact (BinaryFirstPlane.first_plane_core_displacement s).trans (inf_le_left.trans inf_le_left)
  have hQI : extensionCore c.L ≤ I := original_core_map s ▸ map_subtype_le _
  have hlineI := hlineQ.trans hQI
  have hlineC : d.ZS ⊓ d.V₁ ≤ centralizer (I : Set G) := by
    apply le_centralizer_iff.mpr
    rw [s.generated]
    exact sup_le (le_centralizer_iff.mp hfixed)
      (le_centralizer_iff.mp (inf_le_left.trans inf_le_right))
  have hcore : (extensionCore c.L).subgroupOf I =
      ChapterC.BinaryMS.commutatorCore (c.L.subgroupOf I) := by
    apply map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hQI,original_core_map s]
  apply false_of_near_center s hm m
  intro A hA hcomm
  have hAI := hA.trans hQI
  have hA0 : A.subgroupOf I ≤ ChapterC.BinaryMS.commutatorCore (c.L.subgroupOf I) := by
    rw [← hcore]; exact comap_mono hA
  have hN0 : (d.ZS ⊓ d.V₁).subgroupOf I ≤
      ChapterC.BinaryMS.commutatorCore (c.L.subgroupOf I) := by
    rw [← hcore]; exact comap_mono hlineQ
  have hcentral : (d.ZS ⊓ d.V₁).subgroupOf I ≤ center I := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hlineC hx y y.property)
  have hcard : Nat.card ((d.ZS ⊓ d.V₁).subgroupOf I) ≤ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hlineI).toEquiv,
      BinaryFirstPlane.firstLine_card]
  have hcomm0 : ⁅A.subgroupOf I,ChapterC.BinaryMS.commutatorCore (c.L.subgroupOf I)⁆ ≤
      (d.ZS ⊓ d.V₁).subgroupOf I := by
    intro x hx
    have hx' := mem_map_of_mem I.subtype hx
    rw [map_commutator,map_subgroupOf_eq_of_le hAI,original_core_map s] at hx'
    exact hcomm hx'
  have hc := t.large_core_small_displacement common earlier hA0 hN0 hcentral hcard hcomm0
  intro a ha x hx
  exact congrArg Subtype.val (hc (show (⟨a,hAI ha⟩ : I) ∈ A.subgroupOf I from ha)
    ⟨x,hQI hx⟩ (hcore ▸ hx))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinarySmallDisplacement


namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open RankOneConfiguration SmallExtension SmallExtension.CentralCover SmallExtension.CentralCover.LinearThree
open ChapterC BinaryMS.MS93 BinaryMS.MS93.DistanceEight.PathCentrality
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

/-- The actual large binary branch is impossible from the earlier MS core facts;
no additional action or component-recognition premise is needed. -/
theorem source_binary_large_false
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* LinearThree.SL)
    (t : InputSetup (source_binaryMSInput s e))
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) : False :=
  BinarySmallDisplacement.false_of_local_core s hm e t common earlier

/-- Prescribed critical-path replacement supplies all earlier large-core facts
at the original MS input, completing the source contradiction. -/
theorem source_binary_large_false_of_replacement
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* LinearThree.SL)
    (t : InputSetup (source_binaryMSInput s e))
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (replacement : ∀ {a a'} (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p) :
    False :=
  source_binary_large_false s hm e t common
    (Source44.SourceEarlier.earlier common hb replacement)

/-- The original binary small-component branch retains only prescribed
replacement; the abelian and distance-four branches are already discharged. -/
theorem source_linearThree_false_of_replacement
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (m : Parabolics.RankTwoParabolicMarking d I c.L LinearThree.SL Parabolics.linearThreeParabolic)
    (replacement : ∀ (e : (c.L ⧸ pCore 2 c.L) ≃* LinearThree.SL)
      (t : InputSetup (source_binaryMSInput s e)),
      CommonFacts t.reduction.radical t.source t.geometry →
      4 < t.geometry.b t.reduction.radical → ∀ {a a'}
      (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p) :
    False := by
  apply source_linearThree_false_of_large_distance s m
  intro e t hc hb
  obtain ⟨common⟩ := t.commonFacts hc
  exact source_binary_large_false_of_replacement s (.linearThree m) e t common hb
    (replacement e t common hb)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
