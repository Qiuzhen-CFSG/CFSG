module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalOrdinaryTransvections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.Assembly

/-!
# Excluding the actual A₇ component in the original ordinary source

The original component theorem supplies relative normality, its Sylow
supplement and the local residual. Its faithful A₇ image has order 2520,
whereas a transvection in the ordinary source would force the whole actor
to have order 720. Thus the original action has no rank-one displacement.

The selected critical pair consequently has both strict denominators and
the required rank bound. The original reciprocal, seed and fixed-space
calculations then construct the precise inputs to the seven-point
exclusion, on the same component and literal conjugation action.

Source: Aschbacher–Smith, 13.8.18 and 13.8.24, printed pp.953,958–959.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension CriticalGeometry
open ComponentSieve ComponentSieve.Seven ComponentSieve.Seven.OriginalSource
open Seven.PairsBranch Seven.PairsBranch.ModuleSelection
open FieldComponents.HigherFieldReduction.ExternalModules
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- An actual component of an original ordinary source overgroup cannot
have two-core quotient A₇. All geometry and earlier local clauses are
constructed from the same original flag and plane noncentrality. -/
theorem original_seven_component_false_of_plane_noncentral
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (sourceOne L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) : False := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hH
  let : (V₁.subgroupOf (Source.UH H V₃)).Normal := inferInstance
  let := vh_elementary d hH
  let := LocalFitting.local_solvable d
  have hF9 := hF9all H hH
  have hm' : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥ := by
    rwa [← d.first_normalizer]
  have hcentral := Section05.AmbientSource.source_parabolic_centralizer
    (localNaturalSetup d) eL hmax hm'
  have hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    apply hm
    apply bot_unique
    rw [commutator_comm] at he
    exact (commutator_mono le_rfl d.plane_le_seed).trans_eq he
  have earlier := original_earlier_inputs_of_ordinary_plane_noncentral d eL hmax hF9all hm
  have groups := FieldComponents.LinearThree.OriginalExclusion.original_linear_group_facts
    d hmax hF9all hcentral hcomm
  have hN := groups.component_normal hH hKH hK
  have hKT := (groups.supplement hH hKH hK).symm
  have hLK := groups.base_le_component hH hKH hK
  have hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) := by
    apply le_antisymm
    · rw [← hKT]
      exact sup_le_sup_left le_sup_right K
    · exact sup_le hKH hH.1.2
  have hqs := (SolvableSource.component_fitting_source d hmax hF9all hcentral hcomm
    (Components.EarlierResidual.original_source d hmax) hH K hK).2
  have hcardK : Nat.card (Source.starImage H K) = 2520 := by
    rw [Nat.card_congr (Seven.LocalGeometry.starAlternatingEquiv H K hKH hK eK).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hcard : 720 < Nat.card (Source.Hstar H) := by
    have hle := Nat.card_le_card_of_injective (Source.starImage H K).subtype
      (Source.starImage H K).subtype_injective
    rw [hcardK] at hle
    omega
  let a := Comparison.conjugationAction (d.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point
  let ρ := a.representation
  have hρ : Seven.PairsBranch.CentralAction.IsSourceAction H V₃ V₁ ρ := a.conjugation
  have hno := original_no_rank_one_of_star_card_gt720 d eL hmax hF9all hm hH hcard ρ hρ
  obtain ⟨w⟩ := CriticalSource.exists_selected_witness d hH hF9 hgen hK hN hqs
    hcentral hcomm ρ hρ hno
  have hr := source_reciprocal_inputs d hH hF9 hgen hK hN eK hcentral hcomm ρ hρ
    w.pair w.strict_base w.strict_endpoint w.comparison
  have hs : Seven.LocalGeometry.SecondCase H (sourceOne L T V₁) T (Source.UH H V₃)
      (w.pair.Ugamma V₃) w.pair.Vgamma (w.pair.Aone V₁) V₁ ρ :=
    ⟨w.strict_endpoint, w.strict_base, w.positive, w.comparison,
      w.quadratic_member.1, w.quadratic_member.2.1, w.quadratic_member.2.2,
      w.conjugator, w.conjugate_le_core⟩
  have hc : Seven.SourceExclusion.Earlier w.pair K (sourceOne L T V₁)
      (zero L) (plus L T V₁) G₁ M V₃ V₁ ρ := {
    member := hH
    component_le := hKH
    component := hK
    component_normal := hN
    supplement := hKT
    local_le_component := hLK
    base_solvable := inferInstance
    sylow := source_sylow hH
    two_group := T.isPGroup'
    theta := groups.theta H hH
    solvable_overgroups := groups.solvable_overgroups
    flag := d.seed_le
    line_le := d.line_le_uh H
    source_action := hρ
    transvection_models := fun g _ hg =>
      (hno g ((fixedCodim_zpowers_eq_displacement_rank ρ g).symm.trans hg)).elim
    covered_nine := source_covered_nine d
    edge := hr.edge
    terminal_core := hr.terminal_core
    Vgamma_le := hr.Vgamma_le
    Vgamma_placement := ⟨w.conjugator, w.conjugate_le_core⟩
    alternatives := Or.inr (Or.inr hs)
    reciprocal_inputs := fun _ => hr
    Vgamma_quadratic := w.quadratic
    local_models := Or.inl ⟨eL⟩
    six_local_card := LocalFitting.ordinary_core_card d
    covered_local_rank := source_covered_local_rank d
    covered_residuals := source_covered_residual_data d
    generated := source_generated_original d hKH hN hLK
    monolith := (source_structure hH hKH hK hN hKT eK).2.2
    seed_nontrivial := seed_nontrivial d
    seed_commutator := Section07.ModelExclusions.seed_commutator_point_residual (localNaturalSetup d)
    seed_normalized := source_seed_normalized d
    seed_irreducible := source_seed_irreducible_original d hH ρ hρ
    seed_rank := source_seed_rank d
    seed_centralized := source_zero_centralizes_seed d
    small_modules := fun φ hi hKφ => source_small_quadratic φ hi _ hKφ
    alternating_natural := alternating_natural d earlier ρ
    no_strong := sevenPointNoStrongInput
    recognition := sevenPointRecognitionInput
    strict_centralizer := by
      intro W hW hRank hKW
      have hKQ := nontrivial_on_quotient_of_generated ρ W (Source.starImage H K) hW.1
        (source_linear_generated_original d hKH hN hLK ρ hρ)
      exact (source_no_rank_one_configuration_from_geometry d hH hF9 K hKH hK hN hKT eK ρ hρ
        W w.pair hKW hKQ hRank w.comparison w.rank_gt_one).elim }
  let data : Seven.SourceExclusion.LocalData L T H V K (sourceOne L T V₁)
      (zero L) (plus L T V₁) G₁ M V₃ V₁ := {
    elementary_U := inferInstance
    elementary_V := inferInstance
    denominator_normal := inferInstance
    pair := w.pair
    representation := ρ
    earlier := hc }
  exact data.not_alternatingSeven ⟨eK⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
