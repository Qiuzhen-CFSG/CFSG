module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMinimalCubic
public import CFSG.Quasithin.Chapter10.SourceA5PointInspectionComplete

/-!
# Original A₅ point control with the component inspection discharged

Choose the minimal fundamental setup on the original G,T,L. The complete
point-component inspection applies to every nonidentity vector, including
the fixed kernel. The proper-seed theorem supplies the chosen irreducible
section after tensor exclusion. Thus only the independent local cubic bound
and tensor exclusion remain in this original Chapter13 application.

Source: Aschbacher–Smith10.2.9–12 and13.3.2(2), pp.750–754,884–885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02 Chapter10 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original minimal setup has point control and weak closure after the
two independent local-cubic and tensor obligations are supplied. -/
theorem exists_original_minimal_point_control_after_tensor_exclusion
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ SourceFullModuleCubicBound D ∧
      (SourceLocalModuleCubicBound D → ¬ Nonempty (SourceA5TensorModel D e) →
        (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
          1 < globalW D.fullModule (T : Subgroup G)) := by
  obtain ⟨D,hD,hc,_⟩ := exists_original_minimal_cubic_setup h e hmany
  exact ⟨D,hD,hc,fun hl hnot =>
    source_a5_point_control_after_tensor_exclusion D e hn ht htn hD hl hmany hnot⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
