module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Linear
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Original linear extensions in the Chapter 12 selected pair

Apply the normalized-Borel reduction to every prepared perfect selected R,
using the original chosen-module input and HStar membership. The resulting
concrete comparisons feed the existing residual-preparation theorem, which
constructs a preparation with right factor O²(H). Its selector, uniqueness
input and both full-Borel markings are retained.

The last theorem is conditional on original marked linear-extension data
for every preparation. It is a linear-row consumer, not exhaustive DGS
classification: the shared source assembly must construct the alternatives,
and the remaining rows and final GlobalExit still require their proofs.

Source: Aschbacher–Smith F.1.12, pp.263–264, 5.2.6, pp.650–651,
and the original Chapter 12 application, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Apply original linear-extension collapse to any selected perfect right
factor in the literal Chapter 12 setup. -/
theorem rankOne_global_comparison_of_original_linear
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) (point : Bool)
    (e : Global.OriginalLinear.Marking L R (Global.sourceS L H) F point) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.concreteComparison_of_original_linear
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp F hm hF point e

/-- On the original linear-extension source branch the existing selector
identifies the SAME R with the whole residual. The assumption provides broad
marked original extensions for every preparation, not pure comparisons. -/
theorem rankOne_global_residual_preparation_of_original_linear_extensions
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
    (hmark : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R → ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
        (m : ℕ) (_ : 0 < m) (_ : Nat.card F = 2^m) (point : Bool),
        Nonempty (Global.OriginalLinear.Marking L R (Global.sourceS L H) F point)) :
    ∃ A B : Subgroup G, Global.Preparation T L H A B (residual H) ∧
      Group.IsPerfect (residual H) := by
  apply D.rankOne_global_residual_preparation_of_concrete_comparisons
    h hmany hn hpsl hH hpar hthree hN hunique
  intro A B R d hp
  obtain ⟨F, hfield, hfin, hchar, m, hm, hF, point, ⟨e⟩⟩ := hmark A B R d hp
  exact D.rankOne_global_comparison_of_original_linear h hmany hn hpsl hH
    d hp F hm hF point e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
