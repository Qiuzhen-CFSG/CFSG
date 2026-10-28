module

public import Theory.Representation.BinaryQuarticMathieu.Basic
public import Theory.Mathieu.M22.WittDesign

/-!
# Complete coverage of the marked zero-sum hexads

The six-element subsets of the marked binary point configuration with zero
vector sum are exactly the repository's literal Witt-design blocks.

We identify vector addition with XOR of the ten-bit point words. A Boolean
fold over `univ.powersetCard 6` then checks every six-subset for membership in
the actual `m22Blocks`. Its soundness gives exhaustive coverage, while a
separate check proves that every listed block has zero sum. The ten-bit bound
is needed to recover an integer word from its decoded vector.

The point configuration and marking come from `Basic.lean`, documented by
`Scratch/J4FleetGuidance/SeedCentralizer/design-marking.json` in the source
repository. Here `point` already uses the repository's labels. The enumeration
compares directly with `WittDesign.lean`, without another point permutation or
an auxiliary list of claimed hexads. All finite checks use kernel reduction.
-/

namespace BinaryQuarticMathieu

open Sporadic.Mathieu

private def packedSum (B : Finset (Fin 22)) : Nat :=
  B.fold (· ^^^ ·) 0 (fun i => pointWord (pointMarking.symm i))

private theorem vector_xor (a b : Nat) : vector (a ^^^ b) = vector a + vector b := by
  funext i
  simp only [vector, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i.val <;> cases b.testBit i.val <;> simp [CharTwo.add_self_eq_zero]

private theorem vector_zero : vector 0 = 0 := by
  funext i
  simp [vector]

private theorem packedSum_vector (B : Finset (Fin 22)) :
    vector (packedSum B) = ∑ i ∈ B, point i := by
  induction B using Finset.induction_on with
  | empty => simp [packedSum, vector_zero]
  | @insert i B hi ih =>
    rw [packedSum, Finset.fold_insert hi, vector_xor]
    change point i + vector (packedSum B) = _
    rw [ih, Finset.sum_insert hi]

private theorem pointWord_lt : ∀ i : Fin 22, pointWord i < 2 ^ 10 := by
  decide +kernel

private theorem packedSum_lt (B : Finset (Fin 22)) : packedSum B < 2 ^ 10 := by
  induction B using Finset.induction_on with
  | empty => decide +kernel
  | @insert i B hi ih =>
    rw [packedSum, Finset.fold_insert hi]
    exact Nat.xor_lt_two_pow (pointWord_lt _) ih

private theorem sum_eq_zero_iff_packedSum (B : Finset (Fin 22)) :
    (∑ i ∈ B, point i) = 0 ↔ packedSum B = 0 := by
  rw [← packedSum_vector]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.zero_testBit]
    by_cases hk : k < 10
    · have hc := congrFun h (⟨k, hk⟩ : Fin 10)
      cases hb : (packedSum B).testBit k
      · rfl
      · simp [vector, hb] at hc
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (packedSum_lt B)
        (Nat.pow_le_pow_right (by decide) (by omega)))
  · rintro h
    rw [h, vector_zero]

/-- The domain is all six-subsets, not just the supplied block list. -/
private noncomputable def allCheck : Bool :=
  ((Finset.univ : Finset (Fin 22)).powersetCard 6).fold (· && ·) true
    (fun B => decide (packedSum B ≠ 0 ∨ B ∈ m22Blocks))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 800000 in
private theorem allCheck_true : allCheck = true := by
  decide +kernel

private theorem allCheck_sound (B : Finset (Fin 22)) (hB : B.card = 6) :
    packedSum B ≠ 0 ∨ B ∈ m22Blocks := by
  have h := (Finset.fold_op_rel_iff_and
    (op := (· && ·)) (r := fun (_ : Bool) y => y = true) (c := true)
    (fun {_ _ _} => by simp only [Bool.and_eq_true])).mp allCheck_true
  exact of_decide_eq_true (h.2 B (Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ B, hB⟩))

private theorem block_sum_zero : ∀ i : Fin 77, packedSum (m22BlockAt i) = 0 := by
  decide +kernel

/-- The literal Witt blocks are precisely all zero-sum six-subsets of the marked points. -/
public theorem mem_m22Blocks_iff_isHexad (B : Finset (Fin 22)) :
    B ∈ m22Blocks ↔ IsHexad B := by
  constructor
  · intro hB
    refine ⟨m22Block_card B hB, ?_⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
    exact (sum_eq_zero_iff_packedSum _).mpr (block_sum_zero i)
  · rintro ⟨hcard, hsum⟩
    exact (allCheck_sound B hcard).resolve_left
      (not_not.mpr ((sum_eq_zero_iff_packedSum B).mp hsum))

end BinaryQuarticMathieu
