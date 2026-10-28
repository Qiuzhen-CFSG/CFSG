module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.PointControl
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalCubicComplete

/-!
# Original Chapter13 consumer of the conditional tensor exclusion

Reselect the minimal fundamental setup, retain both established cubic
bounds, and apply the tensor assembly to its actual module. Each remaining
source contract is required only on a minimal setup. No irreducibility
statement about an arbitrary fixed setup is used.
Source: Aschbacher--Smith 13.3.2(2), pp.884--885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02 Chapter10 Chapter10.SourceA5TensorModel ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Apply the same conditional tensor assembly to the reselected minimal
setup of original13.3.2, retaining both proved cubic bounds. -/
theorem exists_original_minimal_point_control_of_tensor_source_inputs
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
    (hplane : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.SymplecticPlaneRecognition) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ SourceFullModuleCubicBound D ∧
      SourceLocalModuleCubicBound D ∧
      (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) := by
  obtain ⟨D,hD,hfull,hlocal,_⟩ := exists_original_minimal_cubic_setup_complete h e hmany
  exact ⟨D,hD,hfull,hlocal,source_a5_point_control_of_tensor_source_inputs D e hn ht htn hD hmany
    (hnormal D hD) (hzero D hD) hcontain (hrows D hD) (hplane D hD)⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
