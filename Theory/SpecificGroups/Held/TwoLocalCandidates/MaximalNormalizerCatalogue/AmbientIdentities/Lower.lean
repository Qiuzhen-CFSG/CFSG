module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.Lower0
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.Lower1
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.Lower2
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.Lower3
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.Lower4

import Mathlib.Tactic.FinCases

/-!
# Lower inclusions for the five Held ambient normalizers

The checked images of the six elementary generators show that each conjugated
candidate generator normalizes the indicated elementary subgroup. Closure then
proves containment of the entire candidate. The reverse containment is a separate
ambient calculation; candidate maximality is neither assumed nor asserted.

Source: GLS3 Table 5.3p and the literal ATLAS max3/max4/max5 words.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open Subgroup LocalPairs.SylowGeometry.Calculations AmbientIdentities

private theorem ambient_eq_word_closure (j : Fin 22) :
    ambient j = closure {x : He | ∃ w ∈ generatorWords j, (word w : He) = x} := by
  unfold ambient entry
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨word w, ⟨w, hw, rfl⟩, rfl⟩

private theorem ambient_eq_row_closure (k : Fin 5) :
    ambient (distinguished k) = closure (Set.range (rowGenerator k)) := by
  apply le_antisymm
  · rw [ambient_eq_word_closure]
    apply (closure_le _).mpr
    have he : ∀ k : Fin 5, ∀ w ∈ generatorWords (distinguished k),
        ∃ j : Fin 6, rowWord k j = w := by decide +kernel
    rintro x ⟨w, hw, rfl⟩
    obtain ⟨j, hj⟩ := he k w hw
    exact subset_closure ⟨j, congrArg (fun w => (word w : He)) hj⟩
  · apply (closure_le _).mpr
    rintro x ⟨j, rfl⟩
    exact rowGenerator_mem k j

private theorem checked_conjugation (k : Fin 5) (t : Fin 2) (j : Fin 6) :
    mappedGenerator k t * rowGenerator k j * (mappedGenerator k t)⁻¹ =
      rowProduct k (conjugateFactors k t j) := by
  fin_cases k
  · exact conjugation_0 t j
  · exact conjugation_1 t j
  · exact conjugation_2 t j
  · exact conjugation_3 t j
  · exact conjugation_4 t j

private theorem mappedGenerator_mem_normalizer (k : Fin 5) (t : Fin 2) :
    mappedGenerator k t ∈ normalizer (ambient (distinguished k) : Set He) := by
  rw [ambient_eq_row_closure]
  apply mem_normalizer_closure_of_conjugates
  rintro x ⟨j, rfl⟩
  rw [checked_conjugation, ← ambient_eq_row_closure]
  exact rowProduct_mem k _

private theorem candidate_eq_generator_closure (i : Fin 3) :
    subgroup i = closure (Set.range (fun t => (Cores.localGenerator i t : He))) := by
  have h := congrArg (fun K : Subgroup (subgroup i) => K.map (subgroup i).subtype)
    (Cores.localGenerator_closure i)
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h.symm

/-- The full conjugated candidate lies in the actual ambient normalizer.
This is only the lower inclusion of the desired identity. -/
public theorem conjugated_candidate_le_normalizer (k : Fin 5) :
    (subgroup (candidate k)).map (MulAut.conj (conjugator k)).toMonoidHom ≤
      normalizer (ambient (distinguished k) : Set He) := by
  rw [candidate_eq_generator_closure, MonoidHom.map_closure, ← Set.range_comp]
  apply (closure_le _).mpr
  rintro x ⟨t, rfl⟩
  exact mappedGenerator_mem_normalizer k t

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue
