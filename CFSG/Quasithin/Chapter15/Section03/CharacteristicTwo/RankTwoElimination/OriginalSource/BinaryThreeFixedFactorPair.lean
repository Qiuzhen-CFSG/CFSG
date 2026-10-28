module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeFixedFactorSource
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The full exchanged fixed factors in original 15.3.23

The whole component-fixed factor F and its actual T-minus-S conjugate are
disjoint. Indeed the conjugate centralizes the original opposite residual,
whose fixed subgroup on F is trivial. Both factors are normal in S, hence
commute. Their join is therefore an elementary group containing the original
V and normalized by both Y and T, with order |F| squared.

The full original consumer also proves that L cannot normalize this join:
15.3.7 would put L in M. This retains the entire original fixed factors and
the same exchanger. No bound on |F|, fixed-point lifting from F/H, or final
15.3.23 contradiction is claimed.

Source: Aschbacher--Smith 15.3.7--8,15.3.12 and15.3.23, pp.1122--1129.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

omit [Finite G] in
/-- The same source exchanger sends the whole fixed factor into the
centralizer of the opposite residual, with its original label retained. -/
theorem coreFixed_conjugate_centralizes_opposite_residual
    (d : LocalData G) (L : Subgroup G) (hg : ResidualGeometry d L)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    (coreFixed L).conjBy g ≤ centralizer (YC d L : Set G) := by
  rintro x ⟨f,hf,rfl⟩
  apply mem_centralizer_iff.mpr
  intro y hy
  rw [← hg.exchange g hgT hgS] at hy
  obtain ⟨a,ha,rfl⟩ := hy
  rw [← map_mul,← map_mul]
  apply congrArg (MulAut.conj g).toMonoidHom
  exact hf.2 a (((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right) ha)

/-- The actual exchanged whole factors form a direct elementary pair,
containing the original orthogonal module and normalized by Y and T. -/
theorem coreFixed_conjugate_pair
    (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let F := coreFixed L
    let W := F ⊔ F.conjBy g
    Disjoint F (F.conjBy g) ∧ F.conjBy g ≤ centralizer (F : Set G) ∧
      IsElementaryAbelian 2 W ∧ d.V ≤ W ∧ W ≤ d.S ∧
      d.Y ⊔ (d.T : Subgroup G) ≤ normalizer (W : Set G) ∧
      Nat.card W = Nat.card F ^ 2 := by
  let F := coreFixed L
  let W := F ⊔ F.conjBy g
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hi)
  have hSa : d.S.map (MulAut.conj g).toMonoidHom = d.S :=
    mem_normalizer_iff_map_conj_eq.mp (hTS hgT)
  have hYa : d.Y.map (MulAut.conj g).toMonoidHom = d.Y :=
    mem_normalizer_iff_map_conj_eq.mp
      ((d.sylow_le.trans (OutsideStructure.LocalBranches.m_normalizes_y d)) hgT)
  have hYSF : d.Y ⊔ d.S ≤ normalizer (F : Set G) := by
    apply (sup_le ?_ hg.component_normalized).trans
      (Extension.SourceCases.FixedFour.coreFixed_normalized L)
    rw [← hg.first_choice]
    exact h.normalizes_component
  have hYSFg : d.Y ⊔ d.S ≤ normalizer (F.conjBy g : Set G) := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hYSF
    rwa [Subgroup.map_sup,hYa,hSa,map_equiv_normalizer_eq] at hh
  have hFS : F ≤ d.S :=
    inf_le_left.trans (commutatorCore_le_S d L h.core_le h.radical)
  have hFgS : F.conjBy g ≤ d.S := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hFS
    rwa [hSa] at hh
  have hdis : Disjoint F (F.conjBy g) := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    have hc := coreFixed_conjugate_centralizes_opposite_residual d L hg g hgT hgS
    exact (inf_le_inf_left F hc).trans
      (coreFixed_opposite_residual_fixed_eq_bot d L e h hg b t common earlier).le
  have hcomm : F.conjBy g ≤ centralizer (F : Set G) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    apply (le_inf ?_ ?_).trans hdis.eq_bot.le
    · exact le_normalizer_iff_commutator_le_left.mp (hFgS.trans (le_sup_right.trans hYSF))
    · exact le_normalizer_iff_commutator_le_right.mp (hFS.trans (le_sup_right.trans hYSFg))
  let := coreFixed_elementary_of_MS93 d L b t common earlier
  let : IsElementaryAbelian 2 (F.conjBy g) := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hW : IsElementaryAbelian 2 W := IsElementaryAbelian.sup_of_le_centralizer hcomm
  have hHF := (intrinsicFour_properties_of_MS93 d L b t common earlier).2.2
  have hmove : movingPlane d L ≤ F.conjBy g := by
    rw [← intrinsicFour_conjugate_eq_movingPlane_of_MS93 d L e h hg b t common earlier g hgT hgS]
    exact map_mono hHF
  have hVW : d.V ≤ W := by
    obtain ⟨i,_,_,_,hC,_,hsup,_⟩ := hg.coordinates
    have hH : intrinsicFour L = d.action.plane i :=
      (intrinsicFour_eq_complementary_plane_of_MS93 d L e h hg b t common earlier).trans hC
    rw [← hsup,← hH]
    exact sup_le (hmove.trans le_sup_right) (hHF.trans le_sup_left)
  have hYSW : d.Y ⊔ d.S ≤ normalizer (W : Set G) :=
    (le_inf hYSF hYSFg).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hTW : (d.T : Subgroup G) ≤ normalizer (W : Set G) :=
    index_two_normalizes_conjugatePair d.S (d.T : Subgroup G) F hi g hgT hgS
      (le_sup_right.trans hYSF) (le_sup_right.trans hYSW)
  have hcard : Nat.card W = Nat.card F ^ 2 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint F (F.conjBy g)
      (hcomm.trans (Subgroup.centralizer_le_normalizer _)) hdis]
    have hconj : Nat.card (F.conjBy g) = Nat.card F :=
      card_map_of_injective (MulAut.conj g).injective
    rw [hconj,pow_two]
  exact ⟨hdis,hcomm,hW,hVW,sup_le hFS hFgS,sup_le (le_sup_left.trans hYSW) hTW,hcard⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.CoreActions LinearThree.Extension.SourceCases
open LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full original source supplies a normalized elementary pair of whole
fixed factors, and forces genuine component movement of that same pair. -/
theorem binary_three_large_distance_fixed_factor_pair
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
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let F := coreFixed c.L
    let W := F ⊔ F.conjBy g
    Disjoint F (F.conjBy g) ∧ F.conjBy g ≤ centralizer (F : Set G) ∧
      IsElementaryAbelian 2 W ∧ d.V ≤ W ∧ W ≤ d.S ∧
      d.Y ⊔ (d.T : Subgroup G) ≤ normalizer (W : Set G) ∧
      Nat.card W = Nat.card F ^ 2 ∧ ¬ c.L ≤ normalizer (W : Set G) := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  obtain ⟨hdis,hcomm,helem,hV,hS,hn,hcard⟩ :=
    coreFixed_conjugate_pair d c.L eSL h hg b t common earlier g hgT hgS
  refine ⟨hdis,hcomm,helem,hV,hS,hn,hcard,?_⟩
  intro hLn
  have hFne : coreFixed c.L ≠ ⊥ := by
    intro hzero
    have hHbot : intrinsicFour c.L = ⊥ := le_bot_iff.mp
      ((intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.2.trans hzero.le)
    have hHcard := (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.1
    rw [hHbot,card_bot] at hHcard
    omega
  have hFS : coreFixed c.L ≤ d.S :=
    inf_le_left.trans (commutatorCore_le_S d c.L h.core_le h.radical)
  have hSF := hg.component_normalized.trans
    (Extension.SourceCases.FixedFour.coreFixed_normalized c.L)
  have hSn := (inf_le_left : d.S ≤ (d.T : Subgroup G)).trans (le_sup_right.trans hn)
  have hY := Y_le_component_sylow d c.L hg.generation g hgT (hg.exchange g hgT hgS)
  have hunique := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action
    hM hu hmany hne).2.2.2.2.1
  exact outside_conjugatePair_contradiction d c.outside hFne hFS g hgT hgS
    (d.action.planeStabilizer_index_two d.T d.sylow_le 1) hSF (sup_le hLn hSn) hY hunique

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
