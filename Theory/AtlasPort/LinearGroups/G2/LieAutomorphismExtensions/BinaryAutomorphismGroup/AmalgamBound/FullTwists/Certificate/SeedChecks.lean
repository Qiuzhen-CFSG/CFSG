module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.FullTwists.Certificate.Basic

/-!
# Endpoint generator certificates

Multiplication, inverse maps, and literal overlap squares for five left
extensions and one right extension. Every other extension is a composition
of these generators; no endpoint coverage theorem is assumed.

All finite certificates are checked by the Lean kernel. The original table
numbering and ATLAS root conventions are retained; attribution and the
ATLAS Research and Attribution License 1.0 are recorded in `Data`.
Source application: Aschbacher--Smith F.1.12(I)(3), q = 2, pp.262--263.
-/

-- The full 192 by 192 prototype used 4 GB. Small, sequential kernel checks
-- keep peak memory near the import baseline (2 GB) with default threading.
set_option Elab.async false

public section
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists.Certificate

theorem left_inverse : ∀ k, ∀ i : Fin 192, leftSeedInverse k (leftSeed k i) = i := by decide +kernel

theorem left_inverse_rev : ∀ k, ∀ i : Fin 192, leftSeed k (leftSeedInverse k i) = i := by decide +kernel

theorem middle_inverse : ∀ k, ∀ i : Fin 64, middleSeedInverse k (middleSeed k i) = i := by decide +kernel

theorem middle_inverse_rev : ∀ k, ∀ i : Fin 64, middleSeed k (middleSeedInverse k i) = i := by decide +kernel

theorem right_inverse : ∀ i : Fin 192, rightSeedInverse (rightSeed i) = i := by decide +kernel

theorem right_inverse_rev : ∀ i : Fin 192, rightSeed (rightSeedInverse i) = i := by decide +kernel

theorem rightMiddle_inverse : ∀ i : Fin 64, rightMiddleSeedInverse (rightMiddleSeed i) = i := by decide +kernel

theorem rightMiddle_inverse_rev : ∀ i : Fin 64, rightMiddleSeed (rightMiddleSeedInverse i) = i := by decide +kernel

theorem left_square : ∀ k i, leftSeed k (leftOverlap i) = leftOverlap (middleSeed k i) := by decide +kernel

theorem right_square : ∀ i, rightSeed (rightOverlap i) = rightOverlap (rightMiddleSeed i) := by decide +kernel

private theorem left0_mul00 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 0 (leftMul (row 0 i) j) = leftMul (leftSeed 0 (row 0 i)) (leftSeed 0 j) := by decide +kernel

private theorem left0_mul01 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 0 (leftMul (row 1 i) j) = leftMul (leftSeed 0 (row 1 i)) (leftSeed 0 j) := by decide +kernel

private theorem left0_mul02 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 0 (leftMul (row 2 i) j) = leftMul (leftSeed 0 (row 2 i)) (leftSeed 0 j) := by decide +kernel

private theorem left0_mul03 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 0 (leftMul (row 3 i) j) = leftMul (leftSeed 0 (row 3 i)) (leftSeed 0 j) := by decide +kernel

private theorem left0_mul04 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 0 (leftMul (row 4 i) j) = leftMul (leftSeed 0 (row 4 i)) (leftSeed 0 j) := by decide +kernel

private theorem left0_mul05 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 0 (leftMul (row 5 i) j) = leftMul (leftSeed 0 (row 5 i)) (leftSeed 0 j) := by decide +kernel

private theorem left0_mul06 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 0 (leftMul (row 6 i) j) = leftMul (leftSeed 0 (row 6 i)) (leftSeed 0 j) := by decide +kernel

private theorem left0_mul07 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 0 (leftMul (row 7 i) j) = leftMul (leftSeed 0 (row 7 i)) (leftSeed 0 j) := by decide +kernel

private theorem left0_mul08 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 0 (leftMul (row 8 i) j) = leftMul (leftSeed 0 (row 8 i)) (leftSeed 0 j) := by decide +kernel

private theorem left0_mul09 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 0 (leftMul (row 9 i) j) = leftMul (leftSeed 0 (row 9 i)) (leftSeed 0 j) := by decide +kernel

private theorem left0_mul10 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 0 (leftMul (row 10 i) j) = leftMul (leftSeed 0 (row 10 i)) (leftSeed 0 j) := by decide +kernel

private theorem left0_mul11 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 0 (leftMul (row 11 i) j) = leftMul (leftSeed 0 (row 11 i)) (leftSeed 0 j) := by decide +kernel

theorem left0_mul : ∀ i j, leftSeed 0 (leftMul i j) = leftMul (leftSeed 0 i) (leftSeed 0 j) := by
  apply forall_rows
  intro b
  fin_cases b
  · exact left0_mul00
  · exact left0_mul01
  · exact left0_mul02
  · exact left0_mul03
  · exact left0_mul04
  · exact left0_mul05
  · exact left0_mul06
  · exact left0_mul07
  · exact left0_mul08
  · exact left0_mul09
  · exact left0_mul10
  · exact left0_mul11

private theorem left1_mul00 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 1 (leftMul (row 0 i) j) = leftMul (leftSeed 1 (row 0 i)) (leftSeed 1 j) := by decide +kernel

private theorem left1_mul01 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 1 (leftMul (row 1 i) j) = leftMul (leftSeed 1 (row 1 i)) (leftSeed 1 j) := by decide +kernel

private theorem left1_mul02 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 1 (leftMul (row 2 i) j) = leftMul (leftSeed 1 (row 2 i)) (leftSeed 1 j) := by decide +kernel

private theorem left1_mul03 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 1 (leftMul (row 3 i) j) = leftMul (leftSeed 1 (row 3 i)) (leftSeed 1 j) := by decide +kernel

private theorem left1_mul04 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 1 (leftMul (row 4 i) j) = leftMul (leftSeed 1 (row 4 i)) (leftSeed 1 j) := by decide +kernel

private theorem left1_mul05 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 1 (leftMul (row 5 i) j) = leftMul (leftSeed 1 (row 5 i)) (leftSeed 1 j) := by decide +kernel

private theorem left1_mul06 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 1 (leftMul (row 6 i) j) = leftMul (leftSeed 1 (row 6 i)) (leftSeed 1 j) := by decide +kernel

private theorem left1_mul07 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 1 (leftMul (row 7 i) j) = leftMul (leftSeed 1 (row 7 i)) (leftSeed 1 j) := by decide +kernel

private theorem left1_mul08 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 1 (leftMul (row 8 i) j) = leftMul (leftSeed 1 (row 8 i)) (leftSeed 1 j) := by decide +kernel

private theorem left1_mul09 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 1 (leftMul (row 9 i) j) = leftMul (leftSeed 1 (row 9 i)) (leftSeed 1 j) := by decide +kernel

private theorem left1_mul10 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 1 (leftMul (row 10 i) j) = leftMul (leftSeed 1 (row 10 i)) (leftSeed 1 j) := by decide +kernel

private theorem left1_mul11 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 1 (leftMul (row 11 i) j) = leftMul (leftSeed 1 (row 11 i)) (leftSeed 1 j) := by decide +kernel

theorem left1_mul : ∀ i j, leftSeed 1 (leftMul i j) = leftMul (leftSeed 1 i) (leftSeed 1 j) := by
  apply forall_rows
  intro b
  fin_cases b
  · exact left1_mul00
  · exact left1_mul01
  · exact left1_mul02
  · exact left1_mul03
  · exact left1_mul04
  · exact left1_mul05
  · exact left1_mul06
  · exact left1_mul07
  · exact left1_mul08
  · exact left1_mul09
  · exact left1_mul10
  · exact left1_mul11

private theorem left2_mul00 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 2 (leftMul (row 0 i) j) = leftMul (leftSeed 2 (row 0 i)) (leftSeed 2 j) := by decide +kernel

private theorem left2_mul01 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 2 (leftMul (row 1 i) j) = leftMul (leftSeed 2 (row 1 i)) (leftSeed 2 j) := by decide +kernel

private theorem left2_mul02 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 2 (leftMul (row 2 i) j) = leftMul (leftSeed 2 (row 2 i)) (leftSeed 2 j) := by decide +kernel

private theorem left2_mul03 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 2 (leftMul (row 3 i) j) = leftMul (leftSeed 2 (row 3 i)) (leftSeed 2 j) := by decide +kernel

private theorem left2_mul04 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 2 (leftMul (row 4 i) j) = leftMul (leftSeed 2 (row 4 i)) (leftSeed 2 j) := by decide +kernel

private theorem left2_mul05 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 2 (leftMul (row 5 i) j) = leftMul (leftSeed 2 (row 5 i)) (leftSeed 2 j) := by decide +kernel

private theorem left2_mul06 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 2 (leftMul (row 6 i) j) = leftMul (leftSeed 2 (row 6 i)) (leftSeed 2 j) := by decide +kernel

private theorem left2_mul07 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 2 (leftMul (row 7 i) j) = leftMul (leftSeed 2 (row 7 i)) (leftSeed 2 j) := by decide +kernel

private theorem left2_mul08 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 2 (leftMul (row 8 i) j) = leftMul (leftSeed 2 (row 8 i)) (leftSeed 2 j) := by decide +kernel

private theorem left2_mul09 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 2 (leftMul (row 9 i) j) = leftMul (leftSeed 2 (row 9 i)) (leftSeed 2 j) := by decide +kernel

private theorem left2_mul10 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 2 (leftMul (row 10 i) j) = leftMul (leftSeed 2 (row 10 i)) (leftSeed 2 j) := by decide +kernel

private theorem left2_mul11 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 2 (leftMul (row 11 i) j) = leftMul (leftSeed 2 (row 11 i)) (leftSeed 2 j) := by decide +kernel

theorem left2_mul : ∀ i j, leftSeed 2 (leftMul i j) = leftMul (leftSeed 2 i) (leftSeed 2 j) := by
  apply forall_rows
  intro b
  fin_cases b
  · exact left2_mul00
  · exact left2_mul01
  · exact left2_mul02
  · exact left2_mul03
  · exact left2_mul04
  · exact left2_mul05
  · exact left2_mul06
  · exact left2_mul07
  · exact left2_mul08
  · exact left2_mul09
  · exact left2_mul10
  · exact left2_mul11

private theorem left3_mul00 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 3 (leftMul (row 0 i) j) = leftMul (leftSeed 3 (row 0 i)) (leftSeed 3 j) := by decide +kernel

private theorem left3_mul01 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 3 (leftMul (row 1 i) j) = leftMul (leftSeed 3 (row 1 i)) (leftSeed 3 j) := by decide +kernel

private theorem left3_mul02 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 3 (leftMul (row 2 i) j) = leftMul (leftSeed 3 (row 2 i)) (leftSeed 3 j) := by decide +kernel

private theorem left3_mul03 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 3 (leftMul (row 3 i) j) = leftMul (leftSeed 3 (row 3 i)) (leftSeed 3 j) := by decide +kernel

private theorem left3_mul04 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 3 (leftMul (row 4 i) j) = leftMul (leftSeed 3 (row 4 i)) (leftSeed 3 j) := by decide +kernel

private theorem left3_mul05 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 3 (leftMul (row 5 i) j) = leftMul (leftSeed 3 (row 5 i)) (leftSeed 3 j) := by decide +kernel

private theorem left3_mul06 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 3 (leftMul (row 6 i) j) = leftMul (leftSeed 3 (row 6 i)) (leftSeed 3 j) := by decide +kernel

private theorem left3_mul07 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 3 (leftMul (row 7 i) j) = leftMul (leftSeed 3 (row 7 i)) (leftSeed 3 j) := by decide +kernel

private theorem left3_mul08 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 3 (leftMul (row 8 i) j) = leftMul (leftSeed 3 (row 8 i)) (leftSeed 3 j) := by decide +kernel

private theorem left3_mul09 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 3 (leftMul (row 9 i) j) = leftMul (leftSeed 3 (row 9 i)) (leftSeed 3 j) := by decide +kernel

private theorem left3_mul10 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 3 (leftMul (row 10 i) j) = leftMul (leftSeed 3 (row 10 i)) (leftSeed 3 j) := by decide +kernel

private theorem left3_mul11 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 3 (leftMul (row 11 i) j) = leftMul (leftSeed 3 (row 11 i)) (leftSeed 3 j) := by decide +kernel

theorem left3_mul : ∀ i j, leftSeed 3 (leftMul i j) = leftMul (leftSeed 3 i) (leftSeed 3 j) := by
  apply forall_rows
  intro b
  fin_cases b
  · exact left3_mul00
  · exact left3_mul01
  · exact left3_mul02
  · exact left3_mul03
  · exact left3_mul04
  · exact left3_mul05
  · exact left3_mul06
  · exact left3_mul07
  · exact left3_mul08
  · exact left3_mul09
  · exact left3_mul10
  · exact left3_mul11

private theorem left4_mul00 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 4 (leftMul (row 0 i) j) = leftMul (leftSeed 4 (row 0 i)) (leftSeed 4 j) := by decide +kernel

private theorem left4_mul01 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 4 (leftMul (row 1 i) j) = leftMul (leftSeed 4 (row 1 i)) (leftSeed 4 j) := by decide +kernel

private theorem left4_mul02 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 4 (leftMul (row 2 i) j) = leftMul (leftSeed 4 (row 2 i)) (leftSeed 4 j) := by decide +kernel

private theorem left4_mul03 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 4 (leftMul (row 3 i) j) = leftMul (leftSeed 4 (row 3 i)) (leftSeed 4 j) := by decide +kernel

private theorem left4_mul04 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 4 (leftMul (row 4 i) j) = leftMul (leftSeed 4 (row 4 i)) (leftSeed 4 j) := by decide +kernel

private theorem left4_mul05 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 4 (leftMul (row 5 i) j) = leftMul (leftSeed 4 (row 5 i)) (leftSeed 4 j) := by decide +kernel

private theorem left4_mul06 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 4 (leftMul (row 6 i) j) = leftMul (leftSeed 4 (row 6 i)) (leftSeed 4 j) := by decide +kernel

private theorem left4_mul07 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 4 (leftMul (row 7 i) j) = leftMul (leftSeed 4 (row 7 i)) (leftSeed 4 j) := by decide +kernel

private theorem left4_mul08 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 4 (leftMul (row 8 i) j) = leftMul (leftSeed 4 (row 8 i)) (leftSeed 4 j) := by decide +kernel

private theorem left4_mul09 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 4 (leftMul (row 9 i) j) = leftMul (leftSeed 4 (row 9 i)) (leftSeed 4 j) := by decide +kernel

private theorem left4_mul10 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 4 (leftMul (row 10 i) j) = leftMul (leftSeed 4 (row 10 i)) (leftSeed 4 j) := by decide +kernel

private theorem left4_mul11 : ∀ i : Fin 16, ∀ j : Fin 192,
    leftSeed 4 (leftMul (row 11 i) j) = leftMul (leftSeed 4 (row 11 i)) (leftSeed 4 j) := by decide +kernel

theorem left4_mul : ∀ i j, leftSeed 4 (leftMul i j) = leftMul (leftSeed 4 i) (leftSeed 4 j) := by
  apply forall_rows
  intro b
  fin_cases b
  · exact left4_mul00
  · exact left4_mul01
  · exact left4_mul02
  · exact left4_mul03
  · exact left4_mul04
  · exact left4_mul05
  · exact left4_mul06
  · exact left4_mul07
  · exact left4_mul08
  · exact left4_mul09
  · exact left4_mul10
  · exact left4_mul11

private theorem right_mul00 : ∀ i : Fin 16, ∀ j : Fin 192,
    rightSeed (rightMul (row 0 i) j) = rightMul (rightSeed (row 0 i)) (rightSeed j) := by decide +kernel

private theorem right_mul01 : ∀ i : Fin 16, ∀ j : Fin 192,
    rightSeed (rightMul (row 1 i) j) = rightMul (rightSeed (row 1 i)) (rightSeed j) := by decide +kernel

private theorem right_mul02 : ∀ i : Fin 16, ∀ j : Fin 192,
    rightSeed (rightMul (row 2 i) j) = rightMul (rightSeed (row 2 i)) (rightSeed j) := by decide +kernel

private theorem right_mul03 : ∀ i : Fin 16, ∀ j : Fin 192,
    rightSeed (rightMul (row 3 i) j) = rightMul (rightSeed (row 3 i)) (rightSeed j) := by decide +kernel

private theorem right_mul04 : ∀ i : Fin 16, ∀ j : Fin 192,
    rightSeed (rightMul (row 4 i) j) = rightMul (rightSeed (row 4 i)) (rightSeed j) := by decide +kernel

private theorem right_mul05 : ∀ i : Fin 16, ∀ j : Fin 192,
    rightSeed (rightMul (row 5 i) j) = rightMul (rightSeed (row 5 i)) (rightSeed j) := by decide +kernel

private theorem right_mul06 : ∀ i : Fin 16, ∀ j : Fin 192,
    rightSeed (rightMul (row 6 i) j) = rightMul (rightSeed (row 6 i)) (rightSeed j) := by decide +kernel

private theorem right_mul07 : ∀ i : Fin 16, ∀ j : Fin 192,
    rightSeed (rightMul (row 7 i) j) = rightMul (rightSeed (row 7 i)) (rightSeed j) := by decide +kernel

private theorem right_mul08 : ∀ i : Fin 16, ∀ j : Fin 192,
    rightSeed (rightMul (row 8 i) j) = rightMul (rightSeed (row 8 i)) (rightSeed j) := by decide +kernel

private theorem right_mul09 : ∀ i : Fin 16, ∀ j : Fin 192,
    rightSeed (rightMul (row 9 i) j) = rightMul (rightSeed (row 9 i)) (rightSeed j) := by decide +kernel

private theorem right_mul10 : ∀ i : Fin 16, ∀ j : Fin 192,
    rightSeed (rightMul (row 10 i) j) = rightMul (rightSeed (row 10 i)) (rightSeed j) := by decide +kernel

private theorem right_mul11 : ∀ i : Fin 16, ∀ j : Fin 192,
    rightSeed (rightMul (row 11 i) j) = rightMul (rightSeed (row 11 i)) (rightSeed j) := by decide +kernel

theorem right_mul : ∀ i j, rightSeed (rightMul i j) = rightMul (rightSeed i) (rightSeed j) := by
  apply forall_rows
  intro b
  fin_cases b
  · exact right_mul00
  · exact right_mul01
  · exact right_mul02
  · exact right_mul03
  · exact right_mul04
  · exact right_mul05
  · exact right_mul06
  · exact right_mul07
  · exact right_mul08
  · exact right_mul09
  · exact right_mul10
  · exact right_mul11

theorem left_mul : ∀ k i j, leftSeed k (leftMul i j) = leftMul (leftSeed k i) (leftSeed k j) := by
  intro k
  fin_cases k
  · exact left0_mul
  · exact left1_mul
  · exact left2_mul
  · exact left3_mul
  · exact left4_mul

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists.Certificate
