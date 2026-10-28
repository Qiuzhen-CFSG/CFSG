module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Adequate
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.ThompsonNormalization
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.OriginalSource
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Containment.KnownSimple
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Source
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralNormality

/-!
# An actual Y_z component from the original 13.6 setup

The completed A and C theorems supply A.3.9 component generation and the
normal-or-index-two conclusion of A.3.8. The literal maximum elementary
images supply C.1.16(1), and the adequate B.5 classifier gives the Fitting
center equality from the proved solvable exclusion. Component selection
and lifting then produce the actual K, its ordinary component image, the
Thompson commutator identity, and membership in Y_z.

On the original marked setup, the proved 13.6.6--9 reduction supplies every
local Sylow, characteristic-two, module and Thompson premise; 13.6.13 is
supplied by its original-source adapter. Only the same earlier source
configuration, fusion, and contrary containment premises remain. In
particular this theorem introduces no classification, solvable-exclusion,
component-normalization or residual-generation assumption.
Source: Aschbacher--Smith, paragraph after13.6.13, printed p.929.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u

private theorem ccomponent_generation_knownSimple
    {X : Type u} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (hO : pCore 2 X = ⊥) :
    cComponentLayer X = solvableResidual X :=
  ChapterA.Section03.SourceComponents.GenerationCore.generation
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)) hX hO

private theorem ccomponent_orbit_knownSimple
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

variable {G : Type u} [Group G] [Finite G]

/-- Lift a literal moved component with every universal earlier theorem supplied. -/
theorem exists_mem_Yz_knownSimple
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hcore : Gv v ∈ Chapter1.H G)
    (hF : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hstarCore : pCore 2 (Gstar z v) = ⊥)
    (hJne : JGstar z v ≠ ⊥)
    (hexclude : ∀ X ∈ XFamily L T z v, ¬ Group.IsSolvable X) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn (Gv v) ∧
      IsComponent (Gstar z v) (starImage z v K) ∧
      ⁅starImage z v K, starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        starImage z v K ∧ K ∈ Yz L T z v := by
  have hfit := FittingCenter.fitting_eq_center_knownSimple L T z v hz hlocal hSyl hstarCore hexclude
  exact exists_mem_Yz_of_JGstar_fitting_eq_center
    (fun _ _ _ => ccomponent_generation_knownSimple)
    (fun _ _ _ => ccomponent_orbit_knownSimple)
    sourceC116One L T z v hz hlocal hcore hF hSyl hstarCore hJne hfit

open A5Module ComponentReduction InitialSieve
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The original source configuration constructs a member of Y_z with its exact star image. -/
theorem exists_mem_Yz_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G)) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn (Gv (markedV d.flag.module)) ∧
      IsComponent (Gstar (markedZ d.flag.module) (markedV d.flag.module))
        (starImage (markedZ d.flag.module) (markedV d.flag.module) K) ∧
      ⁅starImage (markedZ d.flag.module) (markedV d.flag.module) K,
        starImage (markedZ d.flag.module) (markedV d.flag.module)
          (Stellmacher.elementaryAbelianMaxJ (Tv (T : Subgroup G) (markedV d.flag.module)))⁆ =
        starImage (markedZ d.flag.module) (markedV d.flag.module) K ∧
      K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  have r := geometric_reduction_of_earlier_source d V₃ earlier hG hm hcounter hfusion hform hfailure
  let := r.module_reduced.2.1
  have hcore : Gv (markedV d.flag.module) ∈ Chapter1.H G := by
    intro he
    apply r.module_nontrivial
    apply bot_unique
    exact (r.module_central.trans (map_subtype_le _)).trans_eq he
  exact exists_mem_Yz_knownSimple L (T : Subgroup G) _ _ (markedZ_mem_Gv d.flag.module)
    (hG.involution_centralizer_sqtk (marked_orders d.flag.module).2) hcore
    (generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier hG hm hcounter hfusion)
    ⟨c.reductions.centralizerSylow,c.reductions.sylow_image⟩ r.star_twoCore r.globalThompson
    (Solvable.no_solvable_member_original_source d V₃ earlier hG hm hcounter hfusion hform hfailure)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
