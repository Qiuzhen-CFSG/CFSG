module

public import Theory.SpecificGroups.Tits.R1Certificate.Data
public import Theory.SpecificGroups.Tits.Atlas1600ParrottData

/-!
# Excluding nonempty coset words from the r5 centralizer

For each of the 4717 immutable words in the ambient R₁ coset certificate,
either the word is empty or its Atlas permutation fails to commute with r5
on one of the points 0, 1, 2. The kernel checks this single traversal of
the word list. It avoids repeatedly indexing the large representative array.
The result applies in particular to all 1755 surviving representatives.

The words and permutations are the existing certified data for Parrott's
presentation; no computed group order or centralizer identity is assumed.
Source: Parrott, *A Characterization of the Tits' Simple Group* (1972),
pp.672,683–684; application: Aschbacher–Smith 2.3.9(7), printed p.526.
-/

namespace Tits.RelativeParabolicNormalizers.FirstCentralizerCertificate

open Theory.GroupTheory.CosetEnumeration Atlas1600ParrottData

private def z : Equiv.Perm (Fin 1600) := s1Perm * s5Perm ^ 2

private def separates (w : Word ParrottGenerator) (p : Fin 1600) : Bool :=
  decide ((eval permutation w * z) p ≠ (z * eval permutation w) p)

private def test (w : Word ParrottGenerator) : Bool :=
  w.isEmpty || separates w 0 || separates w 1 || separates w 2

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem checked : R1Certificate.input.reps.toList.all test = true := by
  decide +kernel

/-- A stored representative commuting with r5 is literally the empty word.
Out-of-range indices also give the empty default word. -/
public theorem representative_word_eq_nil_of_commute (i : Nat) (hc :
    representative permutation R1Certificate.input i * (s1Perm * s5Perm ^ 2) =
      (s1Perm * s5Perm ^ 2) * representative permutation R1Certificate.input i) :
    R1Certificate.input.reps.getD i [] = [] := by
  have hall := List.all_eq_true.mp checked
  by_cases hi : i < R1Certificate.input.reps.size
  · rw [← Array.getElem_eq_getD (h := hi) []]
    have ht := hall _ (Array.getElem_mem_toList hi)
    have hc' : eval permutation R1Certificate.input.reps[i] * z =
        z * eval permutation R1Certificate.input.reps[i] := by
      simpa only [representative, z, ← Array.getElem_eq_getD (h := hi) []] using hc
    simpa only [test, separates, hc', ne_eq, not_true_eq_false, decide_false,
      Bool.or_false, List.isEmpty_iff] using ht
  · simp [Array.getD, hi]

end Tits.RelativeParabolicNormalizers.FirstCentralizerCertificate
