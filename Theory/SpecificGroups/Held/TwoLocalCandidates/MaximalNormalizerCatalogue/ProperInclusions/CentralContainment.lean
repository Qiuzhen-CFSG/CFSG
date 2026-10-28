module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.Row2
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.Row4
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.Row6
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.Row7
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.Row13
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.Row14
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.Row15
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.Row17

import Mathlib.Tactic.FinCases

/-!
# Eight Held normalizers fix the common involution

In each of rows 2, 4, 6, 7, 13, 14, 15 and 17, the common involution is the
unique element fixing 42 letters with no partner having a forbidden number
of common fixed letters. That number is 6 in rows 4 and 7, and 10 otherwise.
Conjugation preserves this signature, so every row normalizer fixes the
involution and normalizes row 0, its cyclic subgroup.

The small binary row covers and signature counts are kernel checked against
the actual degree-2058 action. This proof needs no simplicity, group order,
classification, or full-representative enumeration premise. Strictness is
established separately by the existing separating witnesses.

Source: ATLAS HeG1-p2058B0 and max3W1, GLS3 Table 5.3p; these containments
support Aschbacher–Smith condition E, printed pp.3–4 and 481–482.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open Subgroup CentralContainment

private theorem central_rows_cover : ∀ j : Fin 22,
    (∀ k : Fin 5, j ≠ distinguished k) → container j = 0 → ∃ k : Fin 8, row k = j := by
  decide +kernel

private theorem central_rows_signature (k : Fin 8) :
    Signature (row k) (bad k) centralWord ∧
      ∀ x, Signature (row k) (bad k) x → x = centralWord := by
  fin_cases k
  · exact row2_signature
  · exact row4_signature
  · exact row6_signature
  · exact row7_signature
  · exact row13_signature
  · exact row14_signature
  · exact row15_signature
  · exact row17_signature

/-- All eight nondistinguished rows whose prescribed container is zero have
normalizer contained in the normalizer of the common involution subgroup. -/
public theorem normalizer_le_normalizer_zero_of_container_eq_zero (j : Fin 22)
    (hj : ∀ k : Fin 5, j ≠ distinguished k) (hc : container j = 0) :
    normalizer (ambient j : Set He) ≤ normalizer (ambient 0 : Set He) := by
  obtain ⟨k, rfl⟩ := central_rows_cover j hj hc
  exact containment_of_signature (row k) (bad k)
    (central_rows_signature k).1 (central_rows_signature k).2

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue
