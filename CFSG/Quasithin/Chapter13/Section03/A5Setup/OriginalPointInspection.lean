module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMinimalCubic
public import CFSG.Quasithin.Chapter10.SourceA5PointInspectionAssembly

/-!
# The original Chapter13 point branch after constrained inspection

Choose a minimal fundamental setup for the original G,T,L and retain its
proved full cubic bound. The completed constrained inspection reduces the
point-centralizer and weak-closure inputs to the actual quasisimple markings.
The local cubic bound, tensor exclusion and quasisimple markings remain
explicit independent source obligations on this same chosen setup.

Source: Aschbacher–Smith10.2.9–12 and13.3.2(2), pp.750–754,884–885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02 Chapter10 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
local instance (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The same original setup feeds point control using only the remaining
quasisimple marking branch of the component inspection. -/
theorem exists_original_minimal_point_control_of_quasisimple_markings
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ SourceFullModuleCubicBound D ∧
      (SourceLocalModuleCubicBound D → ¬ Nonempty (SourceA5TensorModel D e) →
        (∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
          Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
            (centralizer ({v} : Set G)) → SourceA5PointQuasisimpleMarkingInput D v) →
        (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
          1 < globalW D.fullModule (T : Subgroup G)) := by
  obtain ⟨D,hD,hc,_⟩ := exists_original_minimal_cubic_setup h e hmany
  exact ⟨D,hD,hc,fun hl hnot hmarks =>
    source_a5_point_control_of_quasisimple_markings D e hn ht htn hD hl hmany hnot hmarks⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
