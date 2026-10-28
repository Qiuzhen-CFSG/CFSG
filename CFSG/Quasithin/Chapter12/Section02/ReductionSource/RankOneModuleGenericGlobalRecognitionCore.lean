module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCatalogue

/-!
# The core bound in the original Chapter12 generic pair

The concrete model comparisons now prove the bound
[O₂(RS):O₂(R)] ≤ 2 for the very same selected factor and
S = O₂(N_G(L) ∩ H). Thus the existing exchanged-component and diagram
exclusions identify R with O²(H) using only genuine exhaustive comparison
and the original uniqueness input. No separate core-bound premise remains.

Exhaustive comparison and ambient completion recognition remain obligations
of qt-d-1222-rankone-generic-global. Original uniqueness retains its producer
qt-d-1222-rankone-global-uniqueness. The whole-residual U₅(4) and general
Ree alternatives, and both odd Cartans in the full overlap, are retained.
This conditional local deduction does not assert GlobalExit.

Source: Aschbacher–Smith 5.2.6, printed pp.650–651, and its original
Chapter12 application, printed p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual selected factor is O²(H), conditional on exhaustive
comparison and original uniqueness. The model calculations discharge the
core bound, including the exceptional degree-two unitary extension. -/
theorem rankOne_global_residual_preparation_of_concrete_comparisons
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hcomparison : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R → Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))) :
    ∃ A B : Subgroup G, Global.Preparation T L H A B (residual H) ∧
      Group.IsPerfect (residual H) := by
  apply D.rankOne_global_residual_preparation_of_comparisons h hmany hn hpsl
    hH hpar hthree hN hunique _ hcomparison
  intro A B R d hp
  exact d.core_index_le_two_of_comparison (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp (hcomparison A B R d hp)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
