module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticFlags
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalTensorAssembly

/-!
# Original Chapter13 application of the secondary flag contradiction

The original secondary commutator and nonquadratic critical action are proved.
Actual flag coordinates on the opposite layer would contradict these facts.
This consumer retains distance two and construction of those coordinates as
explicit premises. The earlier Cartan, A5-pair, and other model rows remain
with their original source producers.
Source: Aschbacher--Smith9.3.10, pp.734--735, and13.3.2(2), pp.884--885;
MS93 (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02 Chapter10 Chapter10.SourceA5TensorModel ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Apply the actual flag contradiction to the original minimal Chapter13 setup.
The distance and flag construction are explicit earlier-source premises. -/
theorem exists_original_minimal_point_control_of_tensor_secondary_flag_source
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
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.SymplecticSecondaryFlagSource) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ SourceFullModuleCubicBound D ∧
      SourceLocalModuleCubicBound D ∧
      (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) := by
  apply exists_original_minimal_point_control_of_tensor_source_inputs h e hn ht htn hmany
    hnormal hzero hcontain hrows
  intro D hD m
  exact symplecticPlaneRecognition_of_secondary_flag_source (hsource D hD m)


end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
