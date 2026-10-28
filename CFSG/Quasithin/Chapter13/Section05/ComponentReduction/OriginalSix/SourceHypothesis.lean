module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.Configuration
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.PointG2
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.ParabolicCentralizer
public import CFSG.Quasithin.Chapter13.Section05.F9Application.OrdinaryLifting
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.LocalSetup

/-!
# The original ordinary A₆ application of F.9

The selected escaping subgroup in the source Hz family supplies the local
containments and characteristic two. The earlier G.2 application supplies
plane noncentrality from its nonabelian seed closure. Parabolic generation
then gives the seed centralizer containment, ordinary quadratic lifting gives
F.9(e), and the index-two seed argument bounds the actual normal-core kernel.
This constructs F.9 before selecting the component and its full configuration.
No F.9 hypothesis or universal F.9 family is assumed.
Source: Aschbacher–Smith13.5.7 and13.5.18–21, pp.918,922–923.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Section08.SourceCompletion Section07.NaturalAction Recognition Recognition.Configuration
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionQuotients.FiveSeed.BarMarking
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
include d

/-- The actual six-point action proves reducedness in LT. -/
theorem source_reduced : IsPReduced 2 (D.V.subgroupOf D.LT) := by
  let : (D.V.subgroupOf D.LT).Normal := PlaneGeometry.local_module_normal d
  let : IsElementaryAbelian 2 (D.V.subgroupOf D.LT) := PlaneGeometry.local_module_elementary d
  refine ⟨inferInstance,inferInstance,?_⟩
  have hk : (permutation d).ker =
      centralizer (D.V.subgroupOf D.LT : Set D.LT) :=
    ChapterC.RankOne.SymmetricSix.natural_six_kernel_eq_centralizer
      (D.V.subgroupOf D.LT) (permutation d) (PlaneGeometry.localCoordinate d)
      (PlaneGeometry.localCoordinate_conjugation d)
  let f := QuotientGroup.liftEquiv
    (centralizer (D.V.subgroupOf D.LT : Set D.LT))
    (permutation d).rangeRestrict_surjective
    ((permutation d).ker_rangeRestrict.trans hk).symm
  have hh := pCore_map_iso 2 f
  rw [PlaneGeometry.permutation_range_twoCore d] at hh
  exact (map_eq_bot_iff_of_injective _ f.injective).mp hh

include e
/-- The literal source F.9.1 hypothesis for an escaping nonabelian Hz member. -/
theorem source_hypothesis
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T D.Gz M)
    (hU : ¬IsMulCommutative D.UH) : D.Hypothesis := by
  have hHN : D.H ≤ normalizer (D.V₁ : Set G) := d.first_normalizer ▸ hH.2.1
  have hm := source_point_plane_noncentral d D.H hHN hU
  have hc := AmbientSource.source_parabolic_centralizer d e h1221 hm
  have hTJ : (D.T : Subgroup G) ≤ D.H := le_sup_right.trans hH.1.2
  have hVJ : D.V ≤ D.H := d.chosen.le_sylow.trans hTJ
  have hHe : D.H ∈ Chapter1.He G := Chapter1.lemma_1_1_4_6 D.T
    (d.counterexample.qtke.evenCharacteristic D.T) ⟨hH.1.1,hTJ⟩
  have hchar : generalizedFitting D.H = pCore 2 D.H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp hHe)
  have hNL : normalizer (D.V : Set G) ≤ normalizer (D.L : Set G) :=
    h1221.normal_subgroup_normalizer_le d.normalizes_L
      (d.chosen.le_sylow.trans le_sup_right) d.chosen.ne_bot d.normalizes_V
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h1221.simpleQTKE D.T h1221.maximal_faithful.1
  have horb : componentOrbit D.L (D.T : Subgroup G) = D.L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer D.L D.T D.L le_rfl d.normalizes_L)
      (le_componentOrbit D.L D.T)
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → D.LT ≤ N → N = M := by
    simpa only [ChapterF.Section09.Setup.LT,horb,←d.local_normalizer] using hu.normalizer_unique
  have hcontrol : D.H ⊓ normalizer (D.Vplus : Set G) ≤ normalizer (D.V : Set G) :=
    (inf_le_inf_right _ hH.2.1).trans ((PointAction.normalizer_intersection_source d hc).trans inf_le_right)
  have hL1 : D.L₁ = sourceOne D.L D.T D.V₁ := by
    have hh := normalizer_residual_eq D.L D.V₁ (D.T : Subgroup G) D.T.isPGroup' d.normalizes_L
    change sourceOne D.L D.T D.V₁ =
      (pResidual 2 (D.L ⊓ normalizer (D.V₁ : Set G) : Subgroup G)).map
        (D.L ⊓ normalizer (D.V₁ : Set G)).subtype at hh
    rw [←d.first_normalizer] at hh
    exact hh.symm
  have hP : D.V₁ ≤ D.Vplus := d.line_le_plane.trans d.plane_le_seed
  have hlt : D.V₁ < D.Vplus := lt_of_le_of_ne hP (by
    intro he
    have hec := congrArg (fun A : Subgroup G => Nat.card A) he
    rw [d.line_card,d.seed_card] at hec
    contradiction)
  have hq : IsQuasisimple (D.L ⧸ pCore 2 D.L) := IsQuasisimple.of_mulEquiv e.symm
  refine {
    elementary := d.chosen.elementary
    residual := (pResidual_eq_top_iff 2 D.L).mpr d.counterexample.local_component.2.1.2.1
    normalizes_L := d.normalizes_L
    characteristic_L := d.counterexample.local_component.2.1.2.2
    V_le_LT := d.chosen.le_sylow.trans le_sup_right
    reduced := source_reduced d
    sylow_centralizer := (PlaneGeometry.local_sylow_centralizer d hq).symm
    point_card := d.line_card
    normalizes_point := d.line_stable
    point_lt := hlt
    plus_le := d.seed_le
    H_centralizes := hH.2.1
    local_le := hH.1.2
    characteristic_H := hchar
    kernel_core := ?_
    local_normalizes := by
      rw [hL1]
      exact sup_le (Section07.ModelExclusions.point_residual_normalizes_seed d) d.seed_stable
    irreducible := by
      intro A hPA hAU hn
      rw [hL1] at hn
      exact source_seed_interval d A hPA hAU hn
    normalizer_control := le_inf inf_le_left hcontrol
    generated_core := sup_twoCore_eq_bot_of_unique D.LT D.H M huniq hH.2.2
    commutator_lifting := fun g hg hcomm hs hsecond =>
      QuadraticSource.ordinary_source_commutator_lifting d e hm g (hH.2.1 hg) hc hcomm hs hsecond }
  exact normalCore_point_kernel_le_of_index_two D.T D.L D.H M D.V D.Vplus D.V₁
    d.chosen.elementary.isPGroup d.seed_le (NormalBranch.SourceOrthogonal.seed_index d)
    hVJ hP hH.2.1 hcontrol hTJ d.normalizes_L
    (le_sup_left.trans d.normalizes_V) hNL (local_centralizer_le_core d e)
    huniq hH.2.2 hHe

/-- Original component selection with all F.9 and seed-centralizer inputs
constructed from the selected source subgroup. -/
theorem source_exists_component
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T D.Gz M)
    (hU : ¬IsMulCommutative D.UH) :
    ∃ C : Subgroup G, C ≤ D.H ∧ (C.subgroupOf D.H).IsCComponent ∧
      IsQuasisimple (Section08.Source.starImage D.H C) ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Section08.Source.starImage D.H C) ∧
      ⁅Section08.Source.starImage D.H C,Section08.Source.starImage D.H D.V⁆ ≠ ⊥ := by
  have h := source_hypothesis d e h1221 hH hU
  exact exists_component d h e hU h1221
    (AmbientSource.source_parabolic_centralizer d e h1221
      (source_point_plane_noncentral d D.H (d.first_normalizer ▸ hH.2.1) hU))

/-- The complete original configuration with no supplied F.9 hypothesis. -/
theorem source_exists_configuration
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T D.Gz M)
    (hU : ¬IsMulCommutative D.UH) :
    ∃ h : D.Hypothesis, ∃ K : Subgroup G, ∃ s : Selected D K,
      let := componentCentralizer_normal s h
        (selected_star_local_normalization s h
          d.counterexample.qtke (selected_H_mem h))
      Recognition.Configuration.SourceConfiguration s h D.L₁ le_rfl := by
  have h := source_hypothesis d e h1221 hH hU
  exact ⟨h,exists_source_configuration d h e hU h1221
    (AmbientSource.source_parabolic_centralizer d e h1221
      (source_point_plane_noncentral d D.H (d.first_normalizer ▸ hH.2.1) hU))⟩
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
