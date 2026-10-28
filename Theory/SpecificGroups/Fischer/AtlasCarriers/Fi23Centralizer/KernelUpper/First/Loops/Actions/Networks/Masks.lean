module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Actions.Certificates

/-!
# Meaning of the fifteen literal Fi23 coordinate masks

The masks are obtained by repeated doubling. The lower coordinate planes
repeat in the upper half; the new highest plane selects that upper half.
This proves the meaning of all padded coordinates without point enumeration.

The recursive construction and induction proof are adapted from the saved
CFSG `Exhaustion.Edges.FastActions.Masks` work of task
`qt-fischer-fi23-exhaustion-edge-bit-actions`, workspace `ac8ef25e88e2452da418131e73264eb7`.
The literal masks here are independently compared with that construction.
Original CFSG code, Apache 2.0. Source: ATLAS F23G1-p31671B0, GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Actions

private def recursivePlane : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k => if k = n then (2 ^ (2 ^ n) - 1) <<< (2 ^ n)
    else let v := recursivePlane n k; v ||| (v <<< (2 ^ n))

private theorem recursivePlane_spec (n k : Nat) (hk : k < n) (i : Nat) :
    (recursivePlane n k).testBit i = (decide (i < 2 ^ n) && i.testBit k) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [recursivePlane]
    by_cases hkn : k = n
    · subst k
      rw [if_pos rfl, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      by_cases hlow : i < 2 ^ n
      · have hb := Nat.testBit_lt_two_pow hlow
        simp [show ¬2 ^ n ≤ i by omega, hb]
      · have hle : 2 ^ n ≤ i := by omega
        by_cases hhigh : i < 2 ^ (n + 1)
        · have hb := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hle hhigh
          have hs : i - 2 ^ n < 2 ^ n := by rw [Nat.pow_succ] at hhigh; omega
          simp [hle, hs, hhigh, hb]
        · have hs : ¬i - 2 ^ n < 2 ^ n := by rw [Nat.pow_succ] at hhigh; omega
          simp [hs, hhigh]
    · have hlt : k < n := by omega
      rw [if_neg hkn, Nat.testBit_or, Nat.testBit_shiftLeft, ih hlt, ih hlt]
      by_cases hlow : i < 2 ^ n
      · have hhigh : i < 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
        simp [hlow, show ¬2 ^ n ≤ i by omega, hhigh]
      · have hle : 2 ^ n ≤ i := by omega
        have he : (i - 2 ^ n).testBit k = i.testBit k := by
          have hh := Nat.testBit_two_pow_add_gt hlt (i - 2 ^ n)
          simpa only [Nat.add_sub_of_le hle] using hh.symm
        have hs : i - 2 ^ n < 2 ^ n ↔ i < 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
        simp [hlow, hle, hs, he]


theorem coordinate_mask_sound : CoordinateMaskSound := by
  intro k j hj
  have he : coordinateMasks k = recursivePlane 15 k.val := by
    fin_cases k <;> decide +kernel
  rw [he, recursivePlane_spec 15 k.val k.isLt]
  simp only [show j < 2^15 from hj, decide_true, Bool.true_and]

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Actions
