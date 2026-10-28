module
public import CFSG.Quasithin.Chapter10.SourceA5Normalization
public import CFSG.Quasithin.Chapter10.SourceNormalizationSurvivor

/-!
# Conditional assembly of the original Chapter 10 normalization

The original A5 branch is eliminated by its actual tensor exclusion and
the proved Hall/natural-generation contradiction. The non-A5 branch uses
the independent marked linear-three survivor and the source replacement
construction, then applies the same A5 argument to the replacement.
The multiple-overgroup application has three explicit source obligations:
tensor exclusion, the non-A5 survivor and the actual replacement.
The universal conditional API additionally retains the singleton-overgroup
branch. The guarded applications do not require that optional branch;
these theorems are not unconditional proofs of 10.0.1.
Source: Aschbacher--Smith 10.0.1 and the final paragraph of 10.3,
printed pp.741 and756--757.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original normalization endgame in the actual multiple-overgroup
branch, with each independent earlier-source obligation explicit. -/
theorem source_normalizes_of_source_branches_of_many
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : SourceA5TensorExclusionAt T)
    (hreduction : SourceNonnormalReductionAt T)
    (hreplacement : SourceLinearThreeReplacementAt T)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) := by
  classical
  by_contra hn
  by_cases hA : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  · obtain ⟨e⟩ := hA
    exact hn (source_a5_normalizes_after_tensor_exclusion_of_many e hG hL hf hq hmany
      (fun D hD hne => htensor L D e hD hmany hne))
  · obtain ⟨D, ⟨s⟩⟩ := hreduction hmany L hL hf hq hn hA
    obtain ⟨R, hR, hRf, hRq, hRn, ⟨eR⟩⟩ := hreplacement hmany L D s
    exact hRn (source_a5_normalizes_after_tensor_exclusion_of_many eR hG hR hRf hRq
      hmany (fun E hE hne => htensor R E eR hE hmany hne))


/-- The normalization statement without a hidden standing guard. The
singleton branch is a separate input, not part of Hypothesis 12.2.3. -/
theorem source_normalizes_of_source_branches
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hsingle : SourceSingleOvergroupExclusionAt T)
    (htensor : SourceA5TensorExclusionAt T)
    (hreduction : SourceNonnormalReductionAt T)
    (hreplacement : SourceLinearThreeReplacementAt T)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) := by
  by_cases hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard
  · exact source_normalizes_of_source_branches_of_many hG hmany htensor
      hreduction hreplacement hL hf hq
  · by_contra hn
    exact hsingle (Nat.le_of_not_gt hmany) L hL hf hq hn

end CFSG.Quasithin.Chapter10
