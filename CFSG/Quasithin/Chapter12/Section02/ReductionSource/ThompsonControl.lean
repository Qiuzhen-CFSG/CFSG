module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceThompsonControl

/-!
# Original Chapter 12 Thompson branches without earlier callbacks

Hypothesis 12.2.1 constructs one actual Fundamental Setup. The original
multiple-maximal-local hypothesis supplies its outside comparison subgroup.
If J(T) centralizes V_M, the Baumann normalizer is contained in M and the
full fixed layer vanishes. If that layer is nonzero, the actual local
module is an FF-module and L₀=[L₀,J(T)]. These are the source branches
used before the remaining Chapter 10 module classification and normalization.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
3.2.2(6), 3.2.10(1,8), 10.2.1 and 12.2.2, printed pp.579,583,742,795.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Both original Thompson branches on the same FSU selected from the
literal Chapter 12 input; 3.1.1 and all local choices are discharged. -/
theorem Hypothesis1221.exists_original_thompson_control
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      (elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) →
        normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal ∧
        D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) ∧
      (letI := D.module_elementary
       D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥ →
        localOrbit T L = ⁅localOrbit T L, elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
          Representation.BinaryOffender.IsFFModule
            (ChapterD.UniqueFactor.imageRepresentation (localJoin T L) D.moduleSubgroup
              D.join_normalizes_module)) := by
  obtain ⟨D⟩ := h.exists_original_fundamentalSetup
  refine ⟨D, ?_, Chapter10.source_full_fixed_conclusions D hmany⟩
  intro hJ
  refine ⟨Chapter10.source_baumann_normalizer_le_of_centralizes D hJ, ?_⟩
  exact Chapter10.source_fullModule_fixed_eq_bot_of_many D hmany
    (hJ.trans (centralizer_le (le_componentOrbit D.moduleSubgroup D.maximalLocal)))

end CFSG.Quasithin.Chapter12.Section02
