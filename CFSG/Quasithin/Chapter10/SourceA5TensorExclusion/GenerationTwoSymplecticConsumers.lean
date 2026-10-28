module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticAssembly
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalTensorAssembly

/-!
# Original Chapter13 application of the marked symplectic quotient

The natural quotient of the original full module and its kernel placement
are proved in GenerationTwoSymplecticNatural. Consequently the Chapter13
point-control application now uses the constructed marked plane-local
surjection. Only whole-block recognition remains in the symplectic row.
That source argument stays with qt-d-tensor-sp4-plane; final tensor exclusion stays with
qt-d-tensor-exclusion.

Source: Aschbacher--Smith 9.3.10 and its concluding paragraph, pp.734--735;
13.3.2(2), pp.884--885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02 Chapter10 Chapter10.SourceA5TensorModel ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Apply the constructed original natural quotient to the reselected minimal
setup; whole-block and marked plane-local recognition remain explicit. -/
theorem exists_original_minimal_point_control_of_tensor_block_marked_plane
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
    (hblock : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.SymplecticBlockRecognition)
    (hquot : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.SymplecticMarkedPlaneQuotient) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ SourceFullModuleCubicBound D ∧
      SourceLocalModuleCubicBound D ∧
      (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) := by
  apply exists_original_minimal_point_control_of_tensor_source_inputs h e hn ht htn hmany
    hnormal hzero hcontain hrows
  intro D hD m
  exact m.symplecticPlaneRecognition_of_block_marked_quotient (hblock D hD m) (hquot D hD m)

/-- The original minimal point-control application with the entire marked
plane construction discharged; a bound on the whole intrinsic core suffices. -/
theorem exists_original_minimal_point_control_of_tensor_core_bound
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
    (hbound : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.SymplecticCoreBound) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ SourceFullModuleCubicBound D ∧
      SourceLocalModuleCubicBound D ∧
      (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) := by
  apply exists_original_minimal_point_control_of_tensor_source_inputs h e hn ht htn hmany
    hnormal hzero hcontain hrows
  intro D hD m
  exact symplecticPlaneRecognition_of_core_bound (hbound D hD m)

/-- Preserve the whole-block application, passing its order conclusion to
the original plane maps in the numerical whole-core consumer. -/
theorem exists_original_minimal_point_control_of_tensor_block
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
    (hblock : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.SymplecticBlockRecognition) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ SourceFullModuleCubicBound D ∧
      SourceLocalModuleCubicBound D ∧
      (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) := by
  apply exists_original_minimal_point_control_of_tensor_core_bound h e hn ht htn hmany
    hnormal hzero hcontain hrows
  intro D hD m
  exact symplecticCoreBound_of_block (hblock D hD m)

/-- The center-free secondary-orbit route feeds the same original Chapter13 consumer.
Its earlier distance and secondary source premises remain explicit. -/
theorem exists_original_minimal_point_control_of_tensor_secondary_source
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
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.SymplecticSecondarySource) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ SourceFullModuleCubicBound D ∧
      SourceLocalModuleCubicBound D ∧
      (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) := by
  apply exists_original_minimal_point_control_of_tensor_source_inputs h e hn ht htn hmany
    hnormal hzero hcontain hrows
  intro D hD m
  exact symplecticPlaneRecognition_of_secondary_source (hsource D hD m)

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
