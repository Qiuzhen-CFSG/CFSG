module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.Normalizer0
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.Normalizer1
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.Normalizer2
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.Normalizer3
import Mathlib.Tactic.FinCases

/-!
# Seventeen strictness witnesses for Held normalizers

For sixteen rows a normalizing element would preserve common fixed points.
A literal element of the proposed containing normalizer fails that test. For
row 18 the same argument uses the invariant pair `{557, 1016}`. Membership
in each containing normalizer is already checked by generator conjugation.

Thus the reverse inclusion fails for every nondistinguished row. This proves
strictness once the forward inclusions have independently been established;
it does not claim those forward inclusions.

Source: the ATLAS degree-2058 action and GLS3 Table 5.3p. The elementary words
are the published catalogue rows; `source/verify.py` reproduces the witnesses.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions
open Subgroup

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_1 :
    witness 3 ∉ normalizer (ambient 1 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 1 (witness 3) 593 ?_ 0 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_2 :
    witness 0 ∉ normalizer (ambient 2 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 2 (witness 0) 379 ?_ 0 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_3 :
    witness 1 ∉ normalizer (ambient 3 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 3 (witness 1) 44 ?_ 0 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_4 :
    witness 0 ∉ normalizer (ambient 4 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 4 (witness 0) 480 ?_ 1 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_5 :
    witness 1 ∉ normalizer (ambient 5 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 5 (witness 1) 352 ?_ 0 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_6 :
    witness 0 ∉ normalizer (ambient 6 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 6 (witness 0) 480 ?_ 0 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_7 :
    witness 0 ∉ normalizer (ambient 7 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 7 (witness 0) 480 ?_ 1 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_8 :
    witness 1 ∉ normalizer (ambient 8 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 8 (witness 1) 44 ?_ 0 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_10 :
    witness 3 ∉ normalizer (ambient 10 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 10 (witness 3) 593 ?_ 0 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_12 :
    witness 2 ∉ normalizer (ambient 12 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 12 (witness 2) 557 ?_ 0 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_13 :
    witness 0 ∉ normalizer (ambient 13 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 13 (witness 0) 480 ?_ 0 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_14 :
    witness 0 ∉ normalizer (ambient 14 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 14 (witness 0) 480 ?_ 0 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_15 :
    witness 0 ∉ normalizer (ambient 15 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 15 (witness 0) 480 ?_ 0 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_16 :
    witness 1 ∉ normalizer (ambient 16 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 16 (witness 1) 44 ?_ 0 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_17 :
    witness 0 ∉ normalizer (ambient 17 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 17 (witness 0) 480 ?_ 2 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_19 :
    witness 2 ∉ normalizer (ambient 19 : Set He) := by
  apply not_mem_normalizer_of_fixed_point 19 (witness 2) 480 ?_ 0 ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem witness_not_mem_18 :
    witness 1 ∉ normalizer (ambient 18 : Set He) := by
  apply not_mem_normalizer_of_pair 18 (witness 1) 557 1016 ?_ 0 ?_
  · decide +kernel
  · decide +kernel

/-- A checked actual Held element separates each containing normalizer from
the corresponding nondistinguished normalizer. No forward inclusion is assumed. -/
public theorem exists_separating_element (j : Fin 22)
    (hj : ∀ k : Fin 5, j ≠ distinguished k) :
    ∃ g : He, g ∈ normalizer (ambient (container j) : Set He) ∧
      g ∉ normalizer (ambient j : Set He) := by
  fin_cases j
  · exact (hj 0 rfl).elim
  · exact ⟨witness 3, witness_mem_3, witness_not_mem_1⟩
  · exact ⟨witness 0, witness_mem_0, witness_not_mem_2⟩
  · exact ⟨witness 1, witness_mem_1, witness_not_mem_3⟩
  · exact ⟨witness 0, witness_mem_0, witness_not_mem_4⟩
  · exact ⟨witness 1, witness_mem_1, witness_not_mem_5⟩
  · exact ⟨witness 0, witness_mem_0, witness_not_mem_6⟩
  · exact ⟨witness 0, witness_mem_0, witness_not_mem_7⟩
  · exact ⟨witness 1, witness_mem_1, witness_not_mem_8⟩
  · exact (hj 1 rfl).elim
  · exact ⟨witness 3, witness_mem_3, witness_not_mem_10⟩
  · exact (hj 2 rfl).elim
  · exact ⟨witness 2, witness_mem_2, witness_not_mem_12⟩
  · exact ⟨witness 0, witness_mem_0, witness_not_mem_13⟩
  · exact ⟨witness 0, witness_mem_0, witness_not_mem_14⟩
  · exact ⟨witness 0, witness_mem_0, witness_not_mem_15⟩
  · exact ⟨witness 1, witness_mem_1, witness_not_mem_16⟩
  · exact ⟨witness 0, witness_mem_0, witness_not_mem_17⟩
  · exact ⟨witness 1, witness_mem_1, witness_not_mem_18⟩
  · exact ⟨witness 2, witness_mem_2, witness_not_mem_19⟩
  · exact (hj 3 rfl).elim
  · exact (hj 4 rfl).elim

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions
