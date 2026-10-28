module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticDistanceTwo
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalTensorAssembly

/-!
# Original Chapter13 application of the distance-two exclusion

The original restricted action and nilpotent commutator induction exclude
critical distance two without secondary flag or movement premises. This
consumer retains only the original critical-distance reduction in the
symplectic branch. Earlier Cartan, A5-pair and other model rows remain with
their source producers.

Source: Aschbacher--Smith 9.3.10, pp.734--735, and 13.3.2(2), pp.884--885;
MS93 (3.6), pp.870--871. This is conditional assembly, not the full source
classification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02 Chapter10 Chapter10.SourceA5TensorModel ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Apply the proved distance-two exclusion in the original minimal setup.
The earlier original-distance reduction remains an explicit source premise. -/
theorem exists_original_minimal_point_control_of_tensor_distance_two_source
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnormal : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.NonzeroCoreCartanNormalization)
    (hzero : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.ZeroCoreLineCentralization)
    (hcontain : A5PairContainment G)
    (hrows : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.LinearAndG2Exclusion)
    (hsource : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.SymplecticDistanceTwoSource) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ SourceFullModuleCubicBound D ∧
      SourceLocalModuleCubicBound D ∧
      (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) := by
  apply exists_original_minimal_point_control_of_tensor_source_inputs h e hn ht htn hmany
    hnormal hzero hcontain hrows
  intro D hD m
  exact symplecticPlaneRecognition_of_distance_two_source (hsource D hD m)


end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
