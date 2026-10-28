module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.StarNormalizer
public import CFSG.Quasithin.Chapter3.Section01.Source318
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.SmallSupport.Completion
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.ReducedModule
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.Nontrivial

/-!
# The general faithful starred Xi-minus implication

The complete intrinsic embedding theorem proves the original starred
normalizer and uniqueness assertions. Faithful Xi membership supplies the
nonzero module V=[R₂(XT),X]; its reducedness and exact Sylow centralizer
instantiate the genuine earlier Theorem 3.1.8(1). The previously proved
prime restriction and canonical five-factor argument then give Xi-minus.

The reused generic leaves currently live below the Chapter 15 application,
but impose no Chapter 15 source hypothesis. Their import closure is acyclic,
and their public interfaces are unchanged. Only the universal original
3.1.8(1) implication remains with its independent qrc source producer.
Source: Aschbacher–Smith, Lemma 3.2.13, printed pp.584–585.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.SourceXiMinus
open Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
universe u
variable {G : Type u} [Group G] [Finite G]

theorem sourceModule_cubicRatio_of_318
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.SourceTheorem318One G) (T : Sylow 2 G)
    {X : Subgroup G} (hX : X ∈ Chapter1.XiStarF G (T : Subgroup G)) :
    Representation.BinaryOffender.cubicRatio (sourceRepresentation hX.1.1) ≤ 2 := by
  obtain ⟨hmax, hu⟩ := Chapter1.XiEmbedding.normalizer_unique_of_XiStar_knownSimple hG T hX.2
  have hunique (N : Subgroup G) (hN : IsMaximalTwoLocal N)
      (hle : X ⊔ (T : Subgroup G) ≤ N) : N = normalizer (X : Set G) := by
    have hm : N ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ X ⊔ (T : Subgroup G) ≤ M} := ⟨hN, hle⟩
    rw [hu] at hm
    exact Set.mem_singleton_iff.mp hm
  exact h318 T X (normalizer (X : Set G)) hX.1.1.perfect X.le_normalizer
    inferInstance hmax (sup_le X.le_normalizer hX.1.1.invariant) hunique
    (sourceModule (T : Subgroup G) X) (sourceModule_reduced T hX.1.1)
    (source_sylow_centralizer_eq_core T hX.1.1 (sourceModule_ne_bot_of_mem_XiF hX.1))

theorem source_XiStarF_subset_XiMinus_of_318
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.SourceTheorem318One G) (T : Sylow 2 G) :
    Chapter1.XiStarF G (T : Subgroup G) ⊆ Chapter3.XiMinus G (T : Subgroup G) := by
  intro X hX
  exact source_mem_XiMinus_of_module_conditions T hX.1.1 (sourceModule_reduced T hX.1.1)
    ((sourceKernelInFrattini_iff hX.1.1).mpr
      (source_kernel_le_frattini hX.1.1 (sourceModule_ne_bot_of_mem_XiF hX.1)))
    (sourceModule_cubicRatio_of_318 hG h318 T hX)

end CFSG.Quasithin.Chapter3.SourceXiMinus
