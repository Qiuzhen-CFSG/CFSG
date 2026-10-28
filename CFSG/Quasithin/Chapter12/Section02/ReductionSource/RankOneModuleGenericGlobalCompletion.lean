module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalCompletion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!+# The original Chapter12 pair and its Sylow enlargement

The core identity O₂(KT) = O₂(KS), K = O²(H), follows directly from
the original chosen-module setup, independently of classification. Once
the selected factor is K, the actual local completion is normal in
X = ⟨L,H⟩, and both groups have solvable residual ⟨L,K⟩. The original
uniqueness implication also forces O₂(X) = 1.

The last application uses the existing whole-residual preparation and
retains genuine exhaustive comparison and original uniqueness as inputs.
It does not assert X = G, identify a global model, or prove GlobalExit.
Classification and completion recognition remain with
qt-d-1222-rankone-generic-global; original uniqueness retains
qt-d-1222-rankone-global-uniqueness as its producer.

Source: Aschbacher–Smith 5.2.5–7, printed pp.650–652, and the Chapter12
application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Source 5.2.6's core identity on the original H and S, with no comparison
or uniqueness premise. The whole ambient Sylow is not substituted for S. -/
theorem rankOne_global_residual_sylow_core
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    (residual H ⊔ (T : Subgroup G)).pCoreIn 2 =
      (residual H ⊔ Global.sourceS L H).pCoreIn 2 :=
  Global.residual_sylow_core_eq_sourceS D.sylow_normalizes_component hH.1.1.2

/-- Core-free Sylow enlargement and the two literal solvable residuals for
the whole-residual pair. These are local completion facts, not ambient recognition. -/
theorem rankOne_global_residual_completion
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) :
    ((ChapterF.Source.generated ![L,residual H] (Global.sourceS L H)).subgroupOf
      (L ⊔ H)).Normal ∧
    ChapterF.Source.generated ![L,residual H] (Global.sourceS L H) ⊔ (T : Subgroup G) = L ⊔ H ∧
    pCore 2 (L ⊔ H : Subgroup G) = ⊥ ∧
    (solvableResidual (L ⊔ H : Subgroup G)).map (L ⊔ H).subtype = L ⊔ residual H ∧
    (solvableResidual (ChapterF.Source.generated ![L,residual H] (Global.sourceS L H))).map
      (ChapterF.Source.generated ![L,residual H] (Global.sourceS L H)).subtype = L ⊔ residual H := by
  have hpL := Chapter1.mem_L_isPerfect
    (RankOneModule.faithfulMaximalFamily_of_hypothesis h).1.1
  exact ⟨Global.residual_completion_normal_in_pair D.sylow_normalizes_component hH.1.1.2,
    Global.residual_completion_sup_sylow D.sylow_normalizes_component hH.1.1.2,
    d.residual_pair_twoCore_eq_bot,
    Global.residual_pair_solvableResidual D.sylow_normalizes_component hH.1.1.2 hpL hp,
    Global.residual_completion_solvableResidual D.sylow_normalizes_component hH.1.1.2 hpL hp⟩

/-- Apply the core and completion calculations to the actually selected pair.
Exhaustive comparison and original uniqueness still require their source proofs. -/
theorem rankOne_global_residual_completion_of_concrete_comparisons
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
      Group.IsPerfect (residual H) ∧
      (residual H ⊔ (T : Subgroup G)).pCoreIn 2 =
        (residual H ⊔ Global.sourceS L H).pCoreIn 2 ∧
      ((ChapterF.Source.generated ![L,residual H] (Global.sourceS L H)).subgroupOf
        (L ⊔ H)).Normal ∧
      ChapterF.Source.generated ![L,residual H] (Global.sourceS L H) ⊔ (T : Subgroup G) = L ⊔ H ∧
      pCore 2 (L ⊔ H : Subgroup G) = ⊥ ∧
      (solvableResidual (L ⊔ H : Subgroup G)).map (L ⊔ H).subtype = L ⊔ residual H ∧
      (solvableResidual (ChapterF.Source.generated ![L,residual H] (Global.sourceS L H))).map
        (ChapterF.Source.generated ![L,residual H] (Global.sourceS L H)).subtype = L ⊔ residual H := by
  obtain ⟨A,B,d,hp⟩ := D.rankOne_global_residual_preparation_of_concrete_comparisons
    h hmany hn hpsl hH hpar hthree hN hunique hcomparison
  exact ⟨A,B,d,hp,D.rankOne_global_residual_sylow_core hH,
    D.rankOne_global_residual_completion h hH d hp⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
