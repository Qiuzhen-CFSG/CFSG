module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.Assembly
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Assembly
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.OriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitCubic
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Complete

/-!
# The original rank-four orthogonal marking

The original flag, fusion and local component data construct the source
selection hypotheses. The selection simultaneously identifies the intrinsic
K/O₂(K) and its plus image with SL₄(2), and retains the diagram action and
the middle-node parabolic. These choices give the literal source action
configuration, with no component-classification callback.

The complete corrected B.5.1 theorem then recognizes the actual moved
section and marks its seed stabilizer and component centralizer with one
actor. The intrinsic quotient marking proves that the plus kernel is a
two-group. The six-dimensional coordinates belong to U_K/C_{U_K}(K).

The genuine original flag/local, fusion, 13.3.2 and 13.6.3 inputs remain.
The small-model exclusion and reduced SL₄/SL₅ catalogue also remain explicit;
their source assembly must precede the full centralizer contradiction.

Source: Aschbacher--Smith, 13.6.23 and the following paragraph, printed p.933
(combined manuscript of 1 March 2004).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
open LocalAction LocalAction.OrthogonalModule
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

private theorem component_orbit_knownSimple
    {X : Type u} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (hO : pCore 2 X = ⊥)
    (B : Subgroup X) (hB : B.IsCComponent) :
    B.Normal ∨ (normalizer (B : Set X)).index = 2 ∧
      Chapter1.Section02.NonnormalCComponentModel B := by
  by_cases hn : B.Normal
  · exact Or.inl hn
  · right
    have hq := (ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hX hO hB).resolve_left hn
    exact ChapterA.SQTKStructure.NonnormalOuterSource.nonnormal_component_index_and_model
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hX hO B ⟨hB.subnormal,hq⟩ hn

variable
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G))
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (hsmall : ∀ B ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module),
      ¬ Nonempty (plusImage B L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz B ≃* SL(3, ZMod 2)))
    (hmodels : ∀ B ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module),
      Nonempty (plusImage B L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz B ≃* SL(4, ZMod 2)) ∨
      Nonempty (plusImage B L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz B ≃* SL(5, ZMod 2)))
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))

include d V₃ earlier standing hm hfusion hform hfailure h1332 h63 hL hz hsmall hmodels hK

/-- Original source selection supplies every field of the literal action
configuration, together with its intrinsic rank-four quotient. -/
theorem action_configuration_of_original_source :
    ∃ _c : Recognition.SourceAction.Configuration KnownSimple.IsKnownSimple
        K L V T (markedZ d.flag.module) (markedV d.flag.module),
      Nonempty ((K ⧸ pCore 2 K) ≃* SL(4, ZMod 2)) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hr := geometric_reduction_of_earlier_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion hform hfailure
  let := hr.module_reduced.2.1
  have hSyl : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.flag.module))
      (Gv (markedV d.flag.module)) :=
    ⟨c.reductions.centralizerSylow,c.reductions.sylow_image⟩
  have hchar := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion
  have hlocal := standing.qtke.involution_centralizer_sqtk (marked_orders d.flag.module).2
  have hcore : Gv (markedV d.flag.module) ∈ Chapter1.H G := by
    intro he
    apply hr.module_nontrivial
    exact bot_unique ((hr.module_central.trans (map_subtype_le _)).trans_eq he)
  have hfit := FittingCenter.fitting_eq_center_knownSimple L (T : Subgroup G) _ _
    (markedZ_mem_Gv d.flag.module) hlocal hSyl hr.star_twoCore
    (Solvable.no_solvable_member_original_source d V₃ earlier standing.qtke hm
      standing.counterexample hfusion hform hfailure)
  have h14 := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion
  have hR (B : Subgroup G)
      (hB : B ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)) :
      pCore 2 (Gplus B L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz) = ⊥ :=
    LinearThree.CentralAction.ModuleAlternatives.plus_twoCore_eq_bot B L (T : Subgroup G)
      _ _ hB.1.1 hL hz hSyl
  have hcontain (B : Subgroup G)
      (hB : B ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)) :
      Lv L (markedV d.flag.module) ≤ B := by
    apply (containment_and_noncontainment_original_source d V₃ earlier standing hm hfusion
      h1332 h63 hB hL hz ?_).1
    rcases hmodels B hB with h4 | h5
    · obtain ⟨e⟩ := h4
      exact .linear 4 (by omega) ⟨e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide)).symm⟩
    · obtain ⟨e⟩ := h5
      exact .linear 5 (by omega) ⟨e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide)).symm⟩
  have hcontrol (B : Subgroup G) (hB : B ∈ Chapter1.LIn (Gv (markedV d.flag.module))
      (Tv (T : Subgroup G) (markedV d.flag.module)))
      (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (B : Set G))
      (hmove : ¬ B ≤ centralizer ({markedZ d.flag.module} : Set G)) :=
    component_control_of_replacement_source T L standing h1332 h63 _ _ d.flag.z_central
      (d.V_le_T (map_mem d.flag.module _)) (markedV_ne_one d.flag.module)
      ((orderOf_eq_prime_iff.mp (marked_orders d.flag.module).2).1)
      hSyl d.flag_centralizer_index hchar B hB hn hmove
  obtain ⟨e,b,eK,hres,_,_,_,_,_,_,_,hP,t,ht,ha,_⟩ :=
    Selection.source_rankFour_selection
      (fun _ _ _ => ChapterA.Section03.SourceComponents.containment_knownSimple)
      (fun _ _ _ => component_orbit_knownSimple)
      (ChapterA.SQTKStructure.a36Input_of_theoremsAC
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
      K L (T : Subgroup G) _ _ hlocal hcore hSyl hL hz c.residual_card
      (markedLv_not_centralizes_seed d.flag.module) hr.star_twoCore hfit hR h14
      (fun B hB hn hm => (hcontrol B hB hn hm).2.2.symm) hcontain hsmall hmodels hK
  refine ⟨{
    standing := ⟨standing.qtke,standing.local_component,standing.no_larger_field,
      standing.no_linear,standing.no_alternating_nine,standing.no_sporadic,standing.five_minimal⟩
    marking := d.flag.module
    marked_z := rfl
    marked_v := rfl
    a5 := standing.a5
    counterexample := standing.counterexample
    lv_invariant := hL
    seed_fixed := hz
    sylow := hSyl
    seed_omega := markedZ_mem_Tv_omega d
    v_order := (marked_orders d.flag.module).2
    characteristic_two := hchar
    selected := hK
    invariant := h14 K hK
    lv_le := hcontain K hK
    seed_moved := markedLv_not_centralizes_seed d.flag.module
    earlier_control := fun B hB hn hm =>
      ⟨(hcontrol B hB hn hm).1,(hcontrol B hB hn hm).2.1,(hcontrol B hB hn hm).2.2.symm⟩
    residual := hres
    linear_four := e
    diagram := ⟨t,ht,by simpa only [Selection.plusComponentAction_eq] using ha⟩
    basis := b
    middle_parabolic := hP },⟨eK⟩⟩

open Theory.SpecificGroups.SymmetricEight

/-- The original rank-four source selects its six-dimensional orthogonal
section and marks the seed stabilizer with the same actor. The actual plus
kernel is a two-group; all B.5 classification inputs are discharged. -/
theorem orthogonal_marking_of_original_source :
    ∃ c : Recognition.SourceAction.Configuration KnownSimple.IsKnownSimple
        K L V T (markedZ d.flag.module) (markedV d.flag.module),
      IsPGroup 2 (plusMk K L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) c.lv_invariant c.seed_fixed).ker ∧
    letI := c.elementary
    ∃ m : NaturalMovedSection K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) c.lv_invariant c.seed_fixed,
      (∀ w : Additive (WK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)), w ∈ m.upper.toSubmodule ↔
        (w.toMul : G) ∈ UX L (markedZ d.flag.module) (markedV d.flag.module) (starImage (markedZ d.flag.module) (markedV d.flag.module) K)) ∧
      Module.finrank (ZMod 2) (m.upper.toSubmodule ⧸ m.central.toSubmodule) = 6 ∧
      (∀ g w, m.orthogonalCoordinates K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) c.lv_invariant c.seed_fixed
          (m.central.quotientRepresentation g w) =
        (Atlas.Order20160A8.DeletedEight.orthogonalHom (m.actor g)).val
          (m.orthogonalCoordinates K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) c.lv_invariant c.seed_fixed w)) ∧
      (seedStabilizer K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) c.lv_invariant c.seed_fixed).map
        m.actor.toMonoidHom = A6ShadowTwoLocals.fourStabilizer ∧
      (plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) c.lv_invariant c.seed_fixed (K ⊓ Gv (markedZ d.flag.module))).map
        m.actor.toMonoidHom = alternatingGroup (Fin 8) ⊓ A6ShadowTwoLocals.fourStabilizer ∧
      (((plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) c.lv_invariant c.seed_fixed (K ⊓ Gv (markedZ d.flag.module))).map
        m.actor.toMonoidHom).subgroupOf (alternatingGroup (Fin 8))).map
          FourBlockParabolic.equiv.toMonoidHom = BinaryLinear.parabolic FourBlockParabolic.plane := by
  obtain ⟨c,⟨eK⟩⟩ := action_configuration_of_original_source d V₃ earlier standing hm
    hfusion hform hfailure h1332 h63 hL hz hsmall hmodels hK
  exact ⟨c,source_plusMk_kernel_isPGroup c eK,
    source_orthogonal_seed_marking c SourceB5.classification.quasisimple⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal
