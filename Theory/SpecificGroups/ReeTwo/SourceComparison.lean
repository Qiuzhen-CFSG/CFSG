module

public import Theory.SpecificGroups.ReeTwo.Relations

/-!
# The forced root-2 commutator at q = 2

Shinoda (1975), (2.3), printed p. 81, includes a final root-11 factor
in `[α₂(1), α₃(1)]`. The other printed relations force the formula
without this factor. We prove that implication in an arbitrary group:
first expand `[a²,b] = [a,b]^a [a,b]`, then collect a nineteen-letter
word using only the core relations. In particular this is not an
inference from the cardinality or from a computer algebra system.

The theorem `printed_rootTwoThree_forces_last_roots_trivial` pinpoints
the inconsistency: retaining the extra factor kills roots 11 and 12.
The theorem asserts only this consequence of the explicitly stated
relations; construction and identification of the centralizer are separate.
-/

namespace ReeTwo

private theorem swap_of_rightComm {G : Type*} [Group G] {a b c : G}
    (h : rightComm a b = c) : b * a = a * b * c⁻¹ := by
  rw [← h]
  simp [rightComm, mul_assoc]

private theorem inverse_of_square {G : Type*} [Group G] {a s : G}
    (h : a * a = s) (hs : s * s = 1) : a⁻¹ = a * s := by
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, h, hs]

private theorem replace_word {G : Type*} [Group G] (x : CoreRoot → G)
    (p s : List CoreRoot) {u v : List CoreRoot}
    (h : rootWord x u = rootWord x v) :
    rootWord x (p ++ u ++ s) = rootWord x (p ++ v ++ s) := by
  simp only [rootWord_append, h]

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
private theorem collected_action_square {G : Type*} [Group G]
    (x : CoreRoot → G) (h : CoreRelations x) :
    rootWord x [1, 9, 8, 7, 6, 4, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] = rootWord x [2, 3, 4, 5, 6] := by
  have inv8 : (x 5)⁻¹ = x 5 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [coreSquare] using h.square 5
  have inv9 : (x 6)⁻¹ = x 6 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [coreSquare] using h.square 6
  have inv10 : (x 7)⁻¹ = x 7 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [coreSquare] using h.square 7
  have inv11 : (x 8)⁻¹ = x 8 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [coreSquare] using h.square 8
  have inv12 : (x 9)⁻¹ = x 9 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [coreSquare] using h.square 9
  have r4_4 : rootWord x [1, 1] = rootWord x [5] := by
    simpa [rootWord, coreSquare] using h.square 1
  have r5_5 : rootWord x [2, 2] = rootWord x [9] := by
    simpa [rootWord, coreSquare] using h.square 2
  have r6_4 : rootWord x [3, 1] = rootWord x [1, 3] := by
    have hc := swap_of_rightComm (h.commutator 1 3 (by decide))
    change x 3 * x 1 = x 1 * x 3 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r6_5 : rootWord x [3, 2] = rootWord x [2, 3, 7] := by
    have hc := swap_of_rightComm (h.commutator 2 3 (by decide))
    change x 3 * x 2 = x 2 * x 3 * (rootWord x [7])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r7_5 : rootWord x [4, 2] = rootWord x [2, 4, 8] := by
    have hc := swap_of_rightComm (h.commutator 2 4 (by decide))
    change x 4 * x 2 = x 2 * x 4 * (rootWord x [8])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r7_6 : rootWord x [4, 3] = rootWord x [3, 4] := by
    have hc := swap_of_rightComm (h.commutator 3 4 (by decide))
    change x 4 * x 3 = x 3 * x 4 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r7_7 : rootWord x [4, 4] = rootWord x [] := by
    simpa [rootWord, coreSquare] using h.square 4
  have r8_5 : rootWord x [5, 2] = rootWord x [2, 5] := by
    have hc := swap_of_rightComm (h.commutator 2 5 (by decide))
    change x 5 * x 2 = x 2 * x 5 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r8_6 : rootWord x [5, 3] = rootWord x [3, 5] := by
    have hc := swap_of_rightComm (h.commutator 3 5 (by decide))
    change x 5 * x 3 = x 3 * x 5 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r8_7 : rootWord x [5, 4] = rootWord x [4, 5, 9] := by
    have hc := swap_of_rightComm (h.commutator 4 5 (by decide))
    change x 5 * x 4 = x 4 * x 5 * (rootWord x [9])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r9_4 : rootWord x [6, 1] = rootWord x [1, 6] := by
    have hc := swap_of_rightComm (h.commutator 1 6 (by decide))
    change x 6 * x 1 = x 1 * x 6 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r9_5 : rootWord x [6, 2] = rootWord x [2, 6] := by
    have hc := swap_of_rightComm (h.commutator 2 6 (by decide))
    change x 6 * x 2 = x 2 * x 6 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r9_6 : rootWord x [6, 3] = rootWord x [3, 6, 9] := by
    have hc := swap_of_rightComm (h.commutator 3 6 (by decide))
    change x 6 * x 3 = x 3 * x 6 * (rootWord x [9])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r9_7 : rootWord x [6, 4] = rootWord x [4, 6] := by
    have hc := swap_of_rightComm (h.commutator 4 6 (by decide))
    change x 6 * x 4 = x 4 * x 6 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r10_4 : rootWord x [7, 1] = rootWord x [1, 7, 9] := by
    have hc := swap_of_rightComm (h.commutator 1 7 (by decide))
    change x 7 * x 1 = x 1 * x 7 * (rootWord x [9])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r10_5 : rootWord x [7, 2] = rootWord x [2, 7] := by
    have hc := swap_of_rightComm (h.commutator 2 7 (by decide))
    change x 7 * x 2 = x 2 * x 7 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r10_6 : rootWord x [7, 3] = rootWord x [3, 7] := by
    have hc := swap_of_rightComm (h.commutator 3 7 (by decide))
    change x 7 * x 3 = x 3 * x 7 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r10_7 : rootWord x [7, 4] = rootWord x [4, 7] := by
    have hc := swap_of_rightComm (h.commutator 4 7 (by decide))
    change x 7 * x 4 = x 4 * x 7 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r10_8 : rootWord x [7, 5] = rootWord x [5, 7] := by
    have hc := swap_of_rightComm (h.commutator 5 7 (by decide))
    change x 7 * x 5 = x 5 * x 7 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r10_9 : rootWord x [7, 6] = rootWord x [6, 7] := by
    have hc := swap_of_rightComm (h.commutator 6 7 (by decide))
    change x 7 * x 6 = x 6 * x 7 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r10_10 : rootWord x [7, 7] = rootWord x [] := by
    simpa [rootWord, coreSquare] using h.square 7
  have r11_4 : rootWord x [8, 1] = rootWord x [1, 8] := by
    have hc := swap_of_rightComm (h.commutator 1 8 (by decide))
    change x 8 * x 1 = x 1 * x 8 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r11_5 : rootWord x [8, 2] = rootWord x [2, 8] := by
    have hc := swap_of_rightComm (h.commutator 2 8 (by decide))
    change x 8 * x 2 = x 2 * x 8 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r11_6 : rootWord x [8, 3] = rootWord x [3, 8] := by
    have hc := swap_of_rightComm (h.commutator 3 8 (by decide))
    change x 8 * x 3 = x 3 * x 8 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r11_7 : rootWord x [8, 4] = rootWord x [4, 8] := by
    have hc := swap_of_rightComm (h.commutator 4 8 (by decide))
    change x 8 * x 4 = x 4 * x 8 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r11_9 : rootWord x [8, 6] = rootWord x [6, 8] := by
    have hc := swap_of_rightComm (h.commutator 6 8 (by decide))
    change x 8 * x 6 = x 6 * x 8 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r11_10 : rootWord x [8, 7] = rootWord x [7, 8] := by
    have hc := swap_of_rightComm (h.commutator 7 8 (by decide))
    change x 8 * x 7 = x 7 * x 8 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r11_11 : rootWord x [8, 8] = rootWord x [] := by
    simpa [rootWord, coreSquare] using h.square 8
  have r12_4 : rootWord x [9, 1] = rootWord x [1, 9] := by
    have hc := swap_of_rightComm (h.commutator 1 9 (by decide))
    change x 9 * x 1 = x 1 * x 9 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r12_5 : rootWord x [9, 2] = rootWord x [2, 9] := by
    have hc := swap_of_rightComm (h.commutator 2 9 (by decide))
    change x 9 * x 2 = x 2 * x 9 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r12_6 : rootWord x [9, 3] = rootWord x [3, 9] := by
    have hc := swap_of_rightComm (h.commutator 3 9 (by decide))
    change x 9 * x 3 = x 3 * x 9 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r12_7 : rootWord x [9, 4] = rootWord x [4, 9] := by
    have hc := swap_of_rightComm (h.commutator 4 9 (by decide))
    change x 9 * x 4 = x 4 * x 9 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r12_9 : rootWord x [9, 6] = rootWord x [6, 9] := by
    have hc := swap_of_rightComm (h.commutator 6 9 (by decide))
    change x 9 * x 6 = x 6 * x 9 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r12_10 : rootWord x [9, 7] = rootWord x [7, 9] := by
    have hc := swap_of_rightComm (h.commutator 7 9 (by decide))
    change x 9 * x 7 = x 7 * x 9 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r12_11 : rootWord x [9, 8] = rootWord x [8, 9] := by
    have hc := swap_of_rightComm (h.commutator 8 9 (by decide))
    change x 9 * x 8 = x 8 * x 9 * (rootWord x [])⁻¹ at hc
    simpa only [rootWord_cons, rootWord_nil, mul_one,
      mul_inv_rev, inv8, inv9, inv10, inv11, inv12, inv_one, mul_assoc] using hc
  have r12_12 : rootWord x [9, 9] = rootWord x [] := by
    simpa [rootWord, coreSquare] using h.square 9
  calc
    rootWord x [1, 9, 8, 7, 6, 4, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] = rootWord x [1, 8, 9, 7, 6, 4, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1] [7, 6, 4, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r12_11
    _ = rootWord x [1, 8, 7, 9, 6, 4, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 8] [6, 4, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r12_10
    _ = rootWord x [1, 7, 8, 9, 6, 4, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1] [9, 6, 4, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r11_10
    _ = rootWord x [1, 7, 8, 6, 9, 4, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 7, 8] [4, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r12_9
    _ = rootWord x [1, 7, 6, 8, 9, 4, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 7] [9, 4, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r11_9
    _ = rootWord x [1, 6, 7, 8, 9, 4, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1] [8, 9, 4, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r10_9
    _ = rootWord x [1, 6, 7, 8, 4, 9, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 6, 7, 8] [3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r12_7
    _ = rootWord x [1, 6, 7, 4, 8, 9, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 6, 7] [9, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r11_7
    _ = rootWord x [1, 6, 4, 7, 8, 9, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 6] [8, 9, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r10_7
    _ = rootWord x [1, 4, 6, 7, 8, 9, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1] [7, 8, 9, 3, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r9_7
    _ = rootWord x [1, 4, 6, 7, 8, 3, 9, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 4, 6, 7, 8] [8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r12_6
    _ = rootWord x [1, 4, 6, 7, 3, 8, 9, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 4, 6, 7] [9, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r11_6
    _ = rootWord x [1, 4, 6, 3, 7, 8, 9, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 4, 6] [8, 9, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r10_6
    _ = rootWord x [1, 4, 3, 6, 9, 7, 8, 9, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 4] [7, 8, 9, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r9_6
    _ = rootWord x [1, 3, 4, 6, 9, 7, 8, 9, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1] [6, 9, 7, 8, 9, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r7_6
    _ = rootWord x [1, 3, 4, 6, 7, 9, 8, 9, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 4, 6] [8, 9, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r12_10
    _ = rootWord x [1, 3, 4, 6, 7, 8, 9, 9, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 4, 6, 7] [9, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r12_11
    _ = rootWord x [1, 3, 4, 6, 7, 8, 8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 4, 6, 7, 8] [8, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r12_12
    _ = rootWord x [1, 3, 4, 6, 7, 2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 4, 6, 7] [2, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r11_11
    _ = rootWord x [1, 3, 4, 6, 2, 7, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 4, 6] [9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r10_5
    _ = rootWord x [1, 3, 4, 2, 6, 7, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 4] [7, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r9_5
    _ = rootWord x [1, 3, 2, 4, 8, 6, 7, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3] [6, 7, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r7_5
    _ = rootWord x [1, 2, 3, 7, 4, 8, 6, 7, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1] [4, 8, 6, 7, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r6_5
    _ = rootWord x [1, 2, 3, 4, 7, 8, 6, 7, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 2, 3] [8, 6, 7, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r10_7
    _ = rootWord x [1, 2, 3, 4, 7, 6, 8, 7, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 2, 3, 4, 7] [7, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r11_9
    _ = rootWord x [1, 2, 3, 4, 6, 7, 8, 7, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 2, 3, 4] [8, 7, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r10_9
    _ = rootWord x [1, 2, 3, 4, 6, 7, 7, 8, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 2, 3, 4, 6, 7] [9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r11_10
    _ = rootWord x [1, 2, 3, 4, 6, 8, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 2, 3, 4, 6] [8, 9, 2, 4, 8, 9, 1, 2, 4, 8, 9] r10_10
    _ = rootWord x [1, 2, 3, 4, 6, 8, 2, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 2, 3, 4, 6, 8] [4, 8, 9, 1, 2, 4, 8, 9] r12_5
    _ = rootWord x [1, 2, 3, 4, 6, 2, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 2, 3, 4, 6] [9, 4, 8, 9, 1, 2, 4, 8, 9] r11_5
    _ = rootWord x [1, 2, 3, 4, 2, 6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 2, 3, 4] [8, 9, 4, 8, 9, 1, 2, 4, 8, 9] r9_5
    _ = rootWord x [1, 2, 3, 2, 4, 8, 6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 2, 3] [6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] r7_5
    _ = rootWord x [1, 2, 2, 3, 7, 4, 8, 6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 2] [4, 8, 6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] r6_5
    _ = rootWord x [1, 9, 3, 7, 4, 8, 6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1] [3, 7, 4, 8, 6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] r5_5
    _ = rootWord x [1, 3, 9, 7, 4, 8, 6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1] [7, 4, 8, 6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] r12_6
    _ = rootWord x [1, 3, 7, 9, 4, 8, 6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3] [4, 8, 6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] r12_10
    _ = rootWord x [1, 3, 7, 4, 9, 8, 6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 7] [8, 6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] r12_7
    _ = rootWord x [1, 3, 4, 7, 9, 8, 6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3] [9, 8, 6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] r10_7
    _ = rootWord x [1, 3, 4, 7, 8, 9, 6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 4, 7] [6, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] r12_11
    _ = rootWord x [1, 3, 4, 7, 8, 6, 9, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 4, 7, 8] [8, 9, 4, 8, 9, 1, 2, 4, 8, 9] r12_9
    _ = rootWord x [1, 3, 4, 7, 6, 8, 9, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 4, 7] [9, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] r11_9
    _ = rootWord x [1, 3, 4, 6, 7, 8, 9, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 4] [8, 9, 8, 9, 4, 8, 9, 1, 2, 4, 8, 9] r10_9
    _ = rootWord x [1, 3, 4, 6, 7, 8, 8, 9, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 4, 6, 7, 8] [9, 4, 8, 9, 1, 2, 4, 8, 9] r12_11
    _ = rootWord x [1, 3, 4, 6, 7, 9, 9, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 4, 6, 7] [9, 9, 4, 8, 9, 1, 2, 4, 8, 9] r11_11
    _ = rootWord x [1, 3, 4, 6, 7, 4, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 4, 6, 7] [4, 8, 9, 1, 2, 4, 8, 9] r12_12
    _ = rootWord x [1, 3, 4, 6, 4, 7, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 4, 6] [8, 9, 1, 2, 4, 8, 9] r10_7
    _ = rootWord x [1, 3, 4, 4, 6, 7, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3, 4] [7, 8, 9, 1, 2, 4, 8, 9] r9_7
    _ = rootWord x [1, 3, 6, 7, 8, 9, 1, 2, 4, 8, 9] :=
      replace_word x [1, 3] [6, 7, 8, 9, 1, 2, 4, 8, 9] r7_7
    _ = rootWord x [1, 3, 6, 7, 8, 1, 9, 2, 4, 8, 9] :=
      replace_word x [1, 3, 6, 7, 8] [2, 4, 8, 9] r12_4
    _ = rootWord x [1, 3, 6, 7, 1, 8, 9, 2, 4, 8, 9] :=
      replace_word x [1, 3, 6, 7] [9, 2, 4, 8, 9] r11_4
    _ = rootWord x [1, 3, 6, 1, 7, 9, 8, 9, 2, 4, 8, 9] :=
      replace_word x [1, 3, 6] [8, 9, 2, 4, 8, 9] r10_4
    _ = rootWord x [1, 3, 1, 6, 7, 9, 8, 9, 2, 4, 8, 9] :=
      replace_word x [1, 3] [7, 9, 8, 9, 2, 4, 8, 9] r9_4
    _ = rootWord x [1, 1, 3, 6, 7, 9, 8, 9, 2, 4, 8, 9] :=
      replace_word x [1] [6, 7, 9, 8, 9, 2, 4, 8, 9] r6_4
    _ = rootWord x [5, 3, 6, 7, 9, 8, 9, 2, 4, 8, 9] :=
      replace_word x [] [3, 6, 7, 9, 8, 9, 2, 4, 8, 9] r4_4
    _ = rootWord x [3, 5, 6, 7, 9, 8, 9, 2, 4, 8, 9] :=
      replace_word x [] [6, 7, 9, 8, 9, 2, 4, 8, 9] r8_6
    _ = rootWord x [3, 5, 6, 7, 8, 9, 9, 2, 4, 8, 9] :=
      replace_word x [3, 5, 6, 7] [9, 2, 4, 8, 9] r12_11
    _ = rootWord x [3, 5, 6, 7, 8, 2, 4, 8, 9] :=
      replace_word x [3, 5, 6, 7, 8] [2, 4, 8, 9] r12_12
    _ = rootWord x [3, 5, 6, 7, 2, 8, 4, 8, 9] :=
      replace_word x [3, 5, 6, 7] [4, 8, 9] r11_5
    _ = rootWord x [3, 5, 6, 2, 7, 8, 4, 8, 9] :=
      replace_word x [3, 5, 6] [8, 4, 8, 9] r10_5
    _ = rootWord x [3, 5, 2, 6, 7, 8, 4, 8, 9] :=
      replace_word x [3, 5] [7, 8, 4, 8, 9] r9_5
    _ = rootWord x [3, 2, 5, 6, 7, 8, 4, 8, 9] :=
      replace_word x [3] [6, 7, 8, 4, 8, 9] r8_5
    _ = rootWord x [2, 3, 7, 5, 6, 7, 8, 4, 8, 9] :=
      replace_word x [] [5, 6, 7, 8, 4, 8, 9] r6_5
    _ = rootWord x [2, 3, 5, 7, 6, 7, 8, 4, 8, 9] :=
      replace_word x [2, 3] [6, 7, 8, 4, 8, 9] r10_8
    _ = rootWord x [2, 3, 5, 6, 7, 7, 8, 4, 8, 9] :=
      replace_word x [2, 3, 5] [7, 8, 4, 8, 9] r10_9
    _ = rootWord x [2, 3, 5, 6, 8, 4, 8, 9] :=
      replace_word x [2, 3, 5, 6] [8, 4, 8, 9] r10_10
    _ = rootWord x [2, 3, 5, 6, 4, 8, 8, 9] :=
      replace_word x [2, 3, 5, 6] [8, 9] r11_7
    _ = rootWord x [2, 3, 5, 4, 6, 8, 8, 9] :=
      replace_word x [2, 3, 5] [8, 8, 9] r9_7
    _ = rootWord x [2, 3, 4, 5, 9, 6, 8, 8, 9] :=
      replace_word x [2, 3] [6, 8, 8, 9] r8_7
    _ = rootWord x [2, 3, 4, 5, 6, 9, 8, 8, 9] :=
      replace_word x [2, 3, 4, 5] [8, 8, 9] r12_9
    _ = rootWord x [2, 3, 4, 5, 6, 8, 9, 8, 9] :=
      replace_word x [2, 3, 4, 5, 6] [8, 9] r12_11
    _ = rootWord x [2, 3, 4, 5, 6, 8, 8, 9, 9] :=
      replace_word x [2, 3, 4, 5, 6, 8] [9] r12_11
    _ = rootWord x [2, 3, 4, 5, 6, 9, 9] :=
      replace_word x [2, 3, 4, 5, 6] [9, 9] r11_11
    _ = rootWord x [2, 3, 4, 5, 6] :=
      replace_word x [2, 3, 4, 5, 6] [] r12_12

/-- The remaining printed relations force the root-2/root-3 commutator.
The arguments are root 1 and roots 3 through 12, with root 2 defined as
root 1 squared by the printed root multiplication law. -/
public theorem forced_rootTwoThree {G : Type*} [Group G]
    (a : G) (x : CoreRoot → G) (h : CoreRelations x) (ha : RootOneRelations a x) :
    rightComm (a ^ 2) (x 0) = rootWord x [2, 3, 4, 5, 6] := by
  have inv12 : (x 9)⁻¹ = x 9 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [coreSquare] using h.square 9
  have inv11 : (x 8)⁻¹ = x 8 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [coreSquare] using h.square 8
  have inv10 : (x 7)⁻¹ = x 7 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [coreSquare] using h.square 7
  have inv9 : (x 6)⁻¹ = x 6 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [coreSquare] using h.square 6
  have inv7 : (x 4)⁻¹ = x 4 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [coreSquare] using h.square 4
  have inv6 : (x 3)⁻¹ = x 3 * x 8 := by
    apply inverse_of_square
    · simpa only [mul_one] using (show x 3 * x 3 = x 8 * 1 from h.square 3)
    · simpa [coreSquare] using h.square 8
  have inv5 : (x 2)⁻¹ = x 2 * x 9 := by
    apply inverse_of_square
    · simpa [coreSquare] using h.square 2
    · simpa [coreSquare] using h.square 9
  have ha4 : MulAut.conj a⁻¹ (x 1) =
      x 1 * (rootWord x [2, 3, 4, 6, 7, 8, 9])⁻¹ :=
    rightConj_of_rightComm (ha 1)
  have ha5 : MulAut.conj a⁻¹ (x 2) = x 2 := by
    simpa [actionCorrection] using rightConj_of_rightComm (ha 2)
  have ha7 : MulAut.conj a⁻¹ (x 4) = x 4 := by
    simpa [actionCorrection] using rightConj_of_rightComm (ha 4)
  have ha11 : MulAut.conj a⁻¹ (x 8) = x 8 := by
    simpa [actionCorrection] using rightConj_of_rightComm (ha 8)
  have ha12 : MulAut.conj a⁻¹ (x 9) = x 9 := by
    simpa [actionCorrection] using rightConj_of_rightComm (ha 9)
  rw [rightComm_square, ha 0]
  change MulAut.conj a⁻¹ (rootWord x [1, 2, 4, 8, 9]) *
    rootWord x [1, 2, 4, 8, 9] = _
  simp only [rootWord_cons, rootWord_nil, mul_one, map_mul,
    ha4, ha5, ha7, ha11, ha12, mul_inv_rev, inv12, inv11, inv10, inv9, inv7, inv6, inv5]
  simpa only [rootWord_cons, rootWord_nil, mul_one, mul_assoc] using
    collected_action_square x h

/-- The extra final root-11 factor printed in (2.3) is incompatible with
nontrivial last roots, in the presence of the other relations. -/
public theorem printed_rootTwoThree_forces_last_roots_trivial
    {G : Type*} [Group G] (a : G) (x : CoreRoot → G)
    (h : CoreRelations x) (ha : RootOneRelations a x)
    (hprinted : rightComm (a ^ 2) (x 0) = rootWord x [2, 3, 4, 5, 6, 8]) :
    x 8 = 1 ∧ x 9 = 1 := by
  have he := (forced_rootTwoThree a x h ha).symm.trans hprinted
  have he' : rootWord x [2, 3, 4, 5, 6] =
      rootWord x [2, 3, 4, 5, 6] * x 8 := by
    simpa only [rootWord_cons, rootWord_nil, mul_one, mul_assoc] using he
  have h11 : x 8 = 1 := (mul_eq_left.mp he'.symm)
  refine ⟨h11, ?_⟩
  have hc := h.commutator 0 8 (by decide)
  change rightComm (x 0) (x 8) = x 9 * 1 at hc
  simpa [rightComm, h11] using hc.symm

end ReeTwo
