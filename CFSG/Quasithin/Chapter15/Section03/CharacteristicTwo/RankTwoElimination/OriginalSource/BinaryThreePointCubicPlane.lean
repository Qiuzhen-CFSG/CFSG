module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCubicConjugate
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointNaturalSeed
public import Theory.Representation.PSL3Two.CubicPlaneMovement
public import Theory.GroupTheory.PrimeOrderLift

/-!
# The original cubic pair moves and fixes the actual opposed four

The first cubic survives the exact natural-eight actor kernel. A faithful
binary-three cubic fixes at most two natural vectors, so it cannot fix the
original moving four. The second cubic lies in the exchanged component and
therefore fixes the exchanged intrinsic four pointwise. All actors and
planes remain literal subgroups of the original group.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem natural_cubic_moves_plane
    (L V U : Subgroup G) (hUV : U ≤ V) (hU : Nat.card U=4)
    (a : L →* SL(3,ZMod 2)) (hak : a.ker=pCore 2 L)
    (hs : HasSectionModel L V ⊥ a (Representation.specialLinearNatural (k := ZMod 2) 3))
    (g : L) (hg : orderOf (g:G)=3) :
    ∃ u : G, u ∈ U ∧ (g:G)*u*(g:G)⁻¹≠u := by
  obtain ⟨_,hLV,_,hn,e,he⟩ := hs
  let := hn
  let q := QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf V)
  have hq : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    rw [QuotientGroup.ker_mk',bot_subgroupOf]
  let j : U → (Fin 3 → ZMod 2) := fun u => (e (q ⟨u,hUV u.property⟩)).toAdd
  have hj : Function.Injective j := by
    intro u v hh
    have h := hq (e.injective (Multiplicative.toAdd.injective hh))
    exact Subtype.ext (congrArg (fun z : V => (z:G)) h)
  have hgo : orderOf g=3 := (Subgroup.orderOf_coe g).symm.trans hg
  have hga : orderOf (a g)=3 :=
    (a.orderOf_map_eq_of_coprime_of_isPGroup_ker (hak ▸ pCore_isPGroup) g
      (by rw [hgo]; decide)).trans hgo
  have hga0 : a g≠1 := by intro hh; rw [hh,orderOf_one] at hga; omega
  obtain ⟨u,hu⟩ := BinaryLinearThree.cubic_moves_injected_four hU j hj (a g)
    (by simpa only [hga] using pow_orderOf_eq_one (a g)) hga0
  refine ⟨u,u.property,?_⟩
  intro hfix
  let v : V := ⟨u,hUV u.property⟩
  have hh := he g v v hfix.symm
  exact hu hh.symm

/-- The existing original point cubic pair also has a genuine moved point
in the opposed four, which the second cubic fixes pointwise. -/
theorem intrinsicFour_point_cubics_move_opposed_plane
    (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple (c.L.subgroupOf (c.L ⊔ d.S))
      (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hz : z ∈ intrinsicFour c.L)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let U := (intrinsicFour c.L).conjBy g
    ∃ a v u : G, a ∈ YL d c.L ∧ v ∈ c.L.conjBy g ∧
      orderOf a=3 ∧ orderOf v=3 ∧
      a ∈ centralizer ({z} : Set G) ∧ v ∈ centralizer ({z} : Set G) ∧
      a*v=v*a ∧ v ∉ YL d c.L ∧
      a ∈ normalizer U ∧ v ∈ centralizer (U : Set G) ∧
      U ≤ ⁅coreCenter c.L,c.L⁆ ∧ u ∈ U ∧ a*u*a⁻¹≠u := by
  let U := (intrinsicFour c.L).conjBy g
  have hU : U=movingPlane d c.L :=
    intrinsicFour_conjugate_eq_movingPlane_of_MS93 d c.L e h hg b t common earlier g hgT hgS
  obtain ⟨a,v,haY,hvL,ha,hv,haz,hvz,hav,hvY⟩ :=
    intrinsicFour_point_conjugate_cubics d c e h hg b t common earlier z hz g hgT hgS
  have hYL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hUZ : U ≤ coreCenter c.L := hU ▸
    movingPlane_le_coreCenter d c hg.component_normalized h.core_le h.radical
  have hUV : U ≤ ⁅coreCenter c.L,c.L⁆ := by
    obtain ⟨_,_,_,_,_,hmove,_⟩ := hg.coordinates
    rw [hU,←hmove]
    exact commutator_mono (hU ▸ hUZ) hYL
  obtain ⟨α,_,hα,hs⟩ :=
    CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.binary_three_original_natural_seed
      d c.L b t common hb
  obtain ⟨u,hu,hmove⟩ := natural_cubic_moves_plane c.L _ U hUV
    (hU ▸ hg.plane_card) α hα hs ⟨a,hYL haY⟩ ha
  have haN : a ∈ normalizer U := by
    rw [hU]
    exact normalizer_commutator_ge_right d.V (YL d c.L) haY
  have hHL : intrinsicFour c.L ≤ centralizer (c.L : Set G) :=
    (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.2.trans inf_le_right
  have hvU : v ∈ centralizer (U : Set G) := by
    obtain ⟨v₀,hv₀,rfl⟩ := hvL
    rintro u ⟨u₀,hu₀,rfl⟩
    simpa only [map_mul] using
      congrArg (MulAut.conj g).toMonoidHom ((hHL hu₀) v₀ hv₀).symm
  exact ⟨a,v,u,haY,hvL,ha,hv,haz,hvz,hav,hvY,haN,hvU,hUV,hu,hmove⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- The full original source supplies a moved point of the actual opposed
four for the first cubic and pointwise fixation by the second cubic. -/
theorem binary_three_source_cubics_move_opposed_plane
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
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hz : z ∈ intrinsicFour c.L)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let U := (intrinsicFour c.L).conjBy g
    ∃ a v u : G, a ∈ YL d c.L ∧ v ∈ c.L.conjBy g ∧
      orderOf a=3 ∧ orderOf v=3 ∧
      a ∈ centralizer ({z} : Set G) ∧ v ∈ centralizer ({z} : Set G) ∧
      a*v=v*a ∧ v ∉ YL d c.L ∧
      a ∈ normalizer U ∧ v ∈ centralizer (U : Set G) ∧
      U ≤ ⁅coreCenter c.L,c.L⁆ ∧ u ∈ U ∧ a*u*a⁻¹≠u := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  let := hW
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hgeo⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  exact intrinsicFour_point_cubics_move_opposed_plane
    d c eSL h hgeo b t common earlier hb z hz g hgT hgS

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
