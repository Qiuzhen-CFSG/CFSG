module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalNormalizationReduction
public import Theory.GroupTheory.MaximalTwoLocalTransport
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalCubicComplete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup.At

/-!
# Original Chapter 13 normalization after tensor exclusion

The original uniform A5 hypothesis supplies maximal faithfulness. Reselecting
its minimal fundamental setup preserves G,T,L, and the completed Hall and
natural-generation contradiction removes the separated branch. The remaining
input is the actual tensor exclusion on that same minimal setup.
The uniform Chapter 13 callback also retains the same ambient G: Sylow
conjugacy transports its actual multiple-overgroup hypothesis, while the
uniform A5 clause supplies the literal A5 quotient at every Sylow subgroup.

Source: Aschbacher--Smith 10.2.3(4), 10.2.12--13 and 13.3.2(2),
printed pp.746--747,754--755 and884--885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02 Chapter10
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Full normalization and the actual Chapter 12 module choice for the
original Chapter 13 A5 component, conditional only on tensor exclusion
in the genuine multiple-overgroup branch. -/
theorem original_a5_normalizes_after_tensor_exclusion_of_many
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnot : ∀ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule → ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
      ¬ Nonempty (SourceA5TensorModel D e)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      ∃ V : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T L V) :=
  (hypothesis1221 h e).a5_normalizes_and_chosen_after_tensor_exclusion_of_many e hmany hnot

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality

namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalNormalizationReduction
open Chapter10
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The exact Chapter 13.6 normalization callback in the uniform A5 branch.
The given multiple-overgroup hypothesis transports to every Sylow subgroup
of the same ambient group; only the A5 tensor source remains explicit. -/
theorem normalization_after_tensor_exclusion_of_many
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : ∀ S : Sylow 2 G, SourceA5TensorExclusionAt S) :
    ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
      (S : Subgroup G) ≤ normalizer (I : Set G) := by
  apply normalization_of_A5_source h e
  intro S I hI hAI
  obtain ⟨eI⟩ := hAI
  have hS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  exact (hI.a5_normalizes_and_chosen_after_tensor_exclusion_of_many eI hS
    (fun D hD hn => htensor S I D eI hD hS hn)).1

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalNormalizationReduction
