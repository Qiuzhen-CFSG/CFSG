module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalModuleAlternatives
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalPointControl
public import CFSG.Quasithin.Chapter10.SourceA5PointControlComplete

/-!
# Original Chapter 13 A₅ consumers with both cubic bounds discharged

Choose the minimal fundamental setup on the original G, T and L. The actual
multiple-overgroup premise gives both its local and full cubic bounds. The
same chosen setup therefore has the tensor-or-moved alternative without an
extra numerical premise, and point control after its tensor model is excluded.
The older conditional interfaces remain available unchanged.

Source: Aschbacher--Smith 3.1.8, 10.2.9--12 and 13.3.2(2),
printed pp.576,750--754,884--885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02 Chapter10 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

local instance originalCompleteMovedElementary
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The original minimal setup has both literal cubic bounds. -/
theorem exists_original_minimal_cubic_setup_complete
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ SourceFullModuleCubicBound D ∧
      SourceLocalModuleCubicBound D ∧
      IsSemisimpleRepresentation (originalMovedQuotientAction D e) ∧
      BinaryOffender.fixedSpace (originalMovedQuotientAction D e) ⊤ = ⊥ ∧
      ∀ S : Subrepresentation (originalMovedQuotientAction D e),
        S.toRepresentation.IsIrreducible → Module.finrank (ZMod 2) S.toSubmodule = 4 := by
  obtain ⟨D,hD,hfull,hs,hfixed,hfour⟩ := exists_original_minimal_cubic_setup h e hmany
  exact ⟨D,hD,hfull,source_local_module_cubic_bound_of_many D hmany,hs,hfixed,hfour⟩

/-- The actual chosen setup has the tensor-or-moved alternative with its
local cubic premise discharged by the original numerical source theorem. -/
theorem exists_original_minimal_module_alternatives_complete
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ SourceFullModuleCubicBound D ∧
      SourceLocalModuleCubicBound D ∧ D.fullModule = D.moduleSubgroup ∧
      (Nonempty (SourceA5TensorModel D e) ∨
        (originalMovedQuotientAction D e).IsIrreducible ∧
        (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) ∧
        normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal) := by
  obtain ⟨D,hD,hfull,hlocal,_⟩ := exists_original_minimal_cubic_setup_complete h e hmany
  exact ⟨D,hD,hfull,hlocal,
    source_a5_original_tensor_or_moved_control_of_many D e hn ht htn hD hmany⟩

/-- The original point-control consumer now retains only the true tensor
exclusion; no numerical or point-inspection callback remains. -/
theorem exists_original_minimal_point_control_after_tensor_exclusion_complete
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ SourceFullModuleCubicBound D ∧
      SourceLocalModuleCubicBound D ∧
      (¬ Nonempty (SourceA5TensorModel D e) →
        (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
          1 < globalW D.fullModule (T : Subgroup G)) := by
  obtain ⟨D,hD,hfull,hlocal,_⟩ := exists_original_minimal_cubic_setup_complete h e hmany
  exact ⟨D,hD,hfull,hlocal,fun hnot =>
    source_a5_point_control_after_tensor_exclusion_of_many D e hn ht htn hD hmany hnot⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
