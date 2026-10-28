module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OriginalSourceComplete
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalPairNormalization

/-!
# Original A5 normalization after genuine pair containment

The same original source hypotheses now imply Sylow normalization and
select an actual chosen module, because the A5 pair theorem and tensor
exclusion are proved. The separate original 13.3.2 module classification
still supplies the invariant flag needed to construct Context. That
remaining module theorem is retained explicitly; no classification is
inferred merely from this normalization result.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter10 Chapter10.SourceA5TensorModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original hypotheses imply normalization and supply an actual chosen
module; there is no remaining pair-containment or tensor premise. -/
theorem original_a5_normalizes_from_source_of_many
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      ∃ V : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T L V) :=
  original_a5_normalizes_of_pair_containment_of_many h e hmany a5PairContainment_from_source

/-- After proved normalization, the genuine earlier original module clause
constructs the flag and actual Context at the same G,T,L. -/
theorem exists_context_from_original_modules
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : SourceCompletion.OriginalAlternatingFiveModules1332At T L) :
    ∃ V V₁ V₂ V₃ : Subgroup G, V₂ ≤ V₃ ∧
      Nonempty (Section05.A5Source.Context T L V V₁ V₂ V₃) :=
  exists_context_of_pair_containment_and_original_modules h e hmany
    a5PairContainment_from_source hmodules

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
