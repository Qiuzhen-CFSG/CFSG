module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.SpanIdentities.RowFive.Checks

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.SpanCertificates.RowFive
open Subgroup

set_option maxRecDepth 8192 in
/-- Every element with centralizer index at most two lies in the prescribed
E64 row, and those elements generate that row, in the literal candidate. -/
public theorem identity : indexTwoSpan (coreCandidate 5) =
    (ambient (container 5)).subgroupOf (coreCandidate 5) := by
  rw [coreCandidate_eq_word_closure, ambient_eq_word_closure]
  change indexTwoSpan (closure (Set.range gen)) =
    (closure (Set.range target)).subgroupOf (closure (Set.range gen))
  apply enumeration.span_eq target
  · intro i hi
    have he : enumeration.element i = eval target (upperWord i) := by
      apply Held.eq_of_four_point_images
      rw [← eval_map representation target targetPerm targetPerm_eq (upperWord i)]
      change ∀ v : Fin 4, representation (elem i) _ = _
      rw [← perm_eq]
      exact upper_check i (by simpa only [counts_check] using hi)
    rw [he]
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    exact subset_closure ⟨a, rfl⟩
  · intro a
    refine ⟨lowerWord a, ?_, ?_⟩
    · intro i hi
      rw [counts_check]
      exact lower_selected a i hi
    · apply Held.eq_of_four_point_images
      rw [← targetPerm_eq a]
      rw [← eval_map representation enumeration.element perm (fun i => perm_eq i) (lowerWord a)]
      exact lower_check a

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.SpanCertificates.RowFive
