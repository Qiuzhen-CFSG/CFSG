module

public import GorensteinWalter.ASevenOddClosureDefs
import Mathlib.Tactic

/-!
# Elimination of the explicit odd-closure candidates in A₇

Among the 71 permutations in `a7OddClosureCandidates`, only elements of
`a7U` pass two rounds of the odd-closure test. For each other candidate,
we select two explicit Sylow actors and one of the two product operations
at each step. The resulting permutation has an even cycle. The proof
projects the corresponding necessary condition and checks its negation
by kernel reduction. It never searches over all permutations or trusts
an external enumeration result.

This is the elimination half of the concrete containment calculation needed
for ABG, II.5 Lemma9(i), article p49 (PDF page50). Completeness of the
first-round candidate list is a separate prerequisite, not asserted here.
The witness choices were found by a finite permutation experiment; each
obstruction is checked independently by Lean.
-/

namespace GorensteinWalter

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
public theorem a7_oddClosureTest_two_mem_U_of_mem_candidates (x : A7) (hx : x ∈ a7OddClosureCandidates)
    (htest : a7OddClosureTest 2 x) : x ∈ a7U := by
  simp only [a7OddClosureCandidates, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change _ = 1 ∨ _ = a7a ∨ _ = a7a ^ 2
    decide
  · change _ = 1 ∨ _ = a7a ∨ _ = a7a ^ 2
    decide
  · change _ = 1 ∨ _ = a7a ∨ _ = a7a ^ 2
    decide
  · have hgood := ((htest.2 1).1.2 1).2
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).2
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).2
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).2.2 2).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 0).1.2 1).1
    exfalso
    revert hgood
    decide +kernel
  · have hgood := ((htest.2 1).1.2 1).2
    exfalso
    revert hgood
    decide +kernel

end GorensteinWalter
