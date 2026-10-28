module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.AbelianSourceModel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.NonabelianSourceModel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.SourceModelTransport

/-!
# The direct module split for the original binary linear-three source

An actual binary MS input supplies a natural or doubled-natural conjugation
quotient on U=[Z(O₂(K)),K]. The abelian core produces one or two copies;
both nonabelian critical-distance cases produce one copy. The quotient actor
remains onto SL₃(2), with intrinsic two-core kernel. Thus the original
13.6.22 argument can use its natural-module centralizer calculation without
first assembling every clause of the C.1.34 classification.

Only the genuine prescribed-replacement source premise remains explicit in
the larger-distance branch. The original join-to-component transport is
re-exported for the checked-center and marked-involution consumer.

Source: Aschbacher--Smith C.1.34 and 13.6.22, printed pp.136--137 and 932--933.
-/

public section
open Subgroup Representation
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open MSSourceModels BinaryMS BinaryMS.MS93 BinaryMS.MS93.DistanceEight.PathCentrality
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {K R : Subgroup G}

/-- The literal source subgroup has the natural-or-doubled quotient needed
by the original marked-involution argument. -/
theorem source_models_of_replacement (h : BinaryMS.Input κ K R)
    (replacement : ∀ (t : InputSetup h),
      CommonFacts t.reduction.radical t.source t.geometry →
      4 < t.geometry.b t.reduction.radical → ∀ {a a'}
      (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators _ p → PrescribedReplacement _ p) :
    (∃ m : ConjugationQuotientModel K (sourceU K) BinaryLinearThree.W,
      Function.Surjective m.actor ∧ m.actor.ker = pCore 2 K) ∨
    (∃ m : ConjugationQuotientModel K (sourceU K)
        (BinaryLinearThree.W.prod BinaryLinearThree.W),
      Function.Surjective m.actor ∧ m.actor.ker = pCore 2 K) := by
  by_cases hc : IsMulCommutative (commutatorCore K)
  · obtain ⟨e,hm | hm⟩ := abelian_source_models h hc
    · obtain ⟨m,hm⟩ := hm
      left
      refine ⟨m, ?_, ?_⟩
      · rw [hm]; exact linearThreeActor_surjective e
      · rw [hm]; exact linearThreeActor_kernel e
    · obtain ⟨m,hm⟩ := hm
      right
      refine ⟨m, ?_, ?_⟩
      · rw [hm]; exact linearThreeActor_surjective e
      · rw [hm]; exact linearThreeActor_kernel e
  · exact Or.inl (nonabelian_source_model_of_replacement h hc replacement)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
