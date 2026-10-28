module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMinimalCubic
public import CFSG.Quasithin.Chapter10.SourceA5ModuleAlternatives

/-!
# Original Chapter 13 choice for the tensor and point-control branches

Choose a minimal fundamental setup without changing the original G, T or L.
The multiple-overgroup hypothesis gives its full cubic bound. For this same
chosen setup, the independent local cubic bound supplies full/local equality
and either the marked tensor model or the moved-module control needed by the
point argument. The tensor exclusion and marked component inspection then
give point-centralizer containment and the weak-closure lower bound.

The local cubic, tensor exclusion and point inspection remain explicit source
inputs. The original Baumann-normalizer theorem is discharged internally.

Source: Aschbacher--Smith 10.2.9--12 and 13.3.2(2), pp.750--754,884--885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02 Chapter10 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

local instance originalAlternativesMovedElementary
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The chosen original setup exposes both source branches at the same seed. -/
theorem exists_original_minimal_module_alternatives
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ SourceFullModuleCubicBound D ∧
      (SourceLocalModuleCubicBound D →
        D.fullModule = D.moduleSubgroup ∧
          (Nonempty (SourceA5TensorModel D e) ∨
            (originalMovedQuotientAction D e).IsIrreducible ∧
            (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) ∧
            normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)) := by
  obtain ⟨D,hD,hc,_⟩ := exists_original_minimal_cubic_setup h e hmany
  exact ⟨D,hD,hc,fun hl =>
    source_a5_original_tensor_or_moved_control D e hn ht htn hD hl hmany⟩

/-- The chosen setup's non-tensor point branch has no extra Baumann input. -/
theorem exists_original_minimal_point_control
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
            (centralizer ({v} : Set G)) → SourceA5PointComponentInspection D e t v) →
        (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
          1 < globalW D.fullModule (T : Subgroup G)) := by
  obtain ⟨D,hD,hc,_⟩ := exists_original_minimal_cubic_setup h e hmany
  exact ⟨D,hD,hc,fun hl hnot hinspect =>
    source_a5_point_control_of_no_tensor D e hn ht htn hD hl hmany hnot hinspect⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
