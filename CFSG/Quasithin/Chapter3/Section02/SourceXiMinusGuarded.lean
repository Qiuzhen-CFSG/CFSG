module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.StarNormalizer
public import CFSG.Quasithin.Chapter3.Section01.Source318Guarded
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.SmallSupport.Completion
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.ReducedModule
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.Nontrivial

/-!
# Faithful starred radicals under the original standing guard

The original 3.2.13 argument uses 3.1.8 at the actual maximal normalizer
of X. Retain the standing outside-local witness at that normalizer, apply
the public fixed-local implication, and use the original reduced module
and its exact Sylow centralizer. The prime restriction and canonical
five-factor argument then give the same Xi-minus conclusion.

Source: Aschbacher--Smith 3.2.13, pp.584--585, using 3.1.8, p.576,
and the standing hypothesis following 2.1.1.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.SourceXiMinus
open Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
universe u
variable {G : Type u} [Group G] [Finite G]

theorem sourceModule_cubicRatio_of_guarded318
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.GuardedSourceTheorem318One G) (T : Sylow 2 G)
    {X : Subgroup G} (hX : X ∈ Chapter1.XiStarF G (T : Subgroup G))
    (hout : Chapter3.HasMaximalOutside T (normalizer (X : Set G))) :
    Representation.BinaryOffender.cubicRatio (sourceRepresentation hX.1.1) ≤ 2 := by
  obtain ⟨hmax, hu⟩ := Chapter1.XiEmbedding.normalizer_unique_of_XiStar_knownSimple hG T hX.2
  have hunique (N : Subgroup G) (hN : IsMaximalTwoLocal N)
      (hle : X ⊔ (T : Subgroup G) ≤ N) : N = normalizer (X : Set G) := by
    have hm : N ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ X ⊔ (T : Subgroup G) ≤ M} := ⟨hN, hle⟩
    rw [hu] at hm
    exact Set.mem_singleton_iff.mp hm
  have hAt := Chapter3.sourceTheorem318OneAt_of_guarded h318 hmax hX.1.1.invariant hout
  exact hAt.cubicRatio_le X hX.1.1.perfect X.le_normalizer
    inferInstance hmax (sup_le X.le_normalizer hX.1.1.invariant) hunique
    (sourceModule (T : Subgroup G) X) (sourceModule_reduced T hX.1.1)
    (source_sylow_centralizer_eq_core T hX.1.1 (sourceModule_ne_bot_of_mem_XiF hX.1))

theorem source_XiStarF_subset_XiMinus_of_guarded318
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.GuardedSourceTheorem318One G) (T : Sylow 2 G)
    (hout : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      (T : Subgroup G) ≤ M → Chapter3.HasMaximalOutside T M) :
    Chapter1.XiStarF G (T : Subgroup G) ⊆ Chapter3.XiMinus G (T : Subgroup G) := by
  intro X hX
  exact source_mem_XiMinus_of_module_conditions T hX.1.1 (sourceModule_reduced T hX.1.1)
    ((sourceKernelInFrattini_iff hX.1.1).mpr
      (source_kernel_le_frattini hX.1.1 (sourceModule_ne_bot_of_mem_XiF hX.1)))
    (sourceModule_cubicRatio_of_guarded318 hG h318 T hX
      (hout _ (Chapter1.XiEmbedding.normalizer_unique_of_XiStar_knownSimple hG T hX.2).1
        hX.1.1.invariant))

end CFSG.Quasithin.Chapter3.SourceXiMinus
