module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceNativeSimilarity
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRectangleOrbits
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRectangleOrbits
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceOvergroup
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSylowCensus
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix

/-!
# The two involution classes and their fusion in the generated subgroup

The 192 square-one elements of the marked Sylow have explicit change-of-basis
certificates. Packed binary multiplication checks both the inverse and the
intertwining equation; its soundness theorem converts them to actual SL₅(2)
conjugations. Sylow conjugacy then gives the two native involution classes.

Recognition inside the normalizer-generated subgroup supplies its two classes.
The original fusion counts distinguish the marked representatives, so this
argument does not require a marking-preserving recognition isomorphism.
The common ambient Sylow gives the two ambient classes as well, and hence
fusion control in the literal generated subgroup.

These are the class and fusion assertions of Aschbacher, *Sporadic Groups*
(1994), 40.6 and the generation argument in 41.1, printed pp.219–220.
The full ambient centralizer of the second involution remains to be controlled.
The internal imports deliberately reuse the existing Sylow encoding and
marked coordinate implementations without changing their public boundaries.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
open scoped Matrix Pointwise
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open SylowCoordinates Thompson.BinaryMatrix

private def packedUpper (a : BitVec 10) : Array ℕ := #[
  (BitVec.cons a[3]! (BitVec.cons a[2]! (BitVec.cons a[1]! (BitVec.cons a[0]! (BitVec.cons true (0 : BitVec 0)))))).toNat,
  (BitVec.cons a[6]! (BitVec.cons a[5]! (BitVec.cons a[4]! (BitVec.cons true (BitVec.cons false (0 : BitVec 0)))))).toNat,
  (BitVec.cons a[8]! (BitVec.cons a[7]! (BitVec.cons true (BitVec.cons false (BitVec.cons false (0 : BitVec 0)))))).toNat,
  (BitVec.cons a[9]! (BitVec.cons true (BitVec.cons false (BitVec.cons false (BitVec.cons false (0 : BitVec 0)))))).toNat,
  16]

private theorem packed_bit (a b c d e : Bool) (i : Fin 5) :
    Thompson.BinaryMatrix.bit
      (BitVec.cons e (BitVec.cons d (BitVec.cons c (BitVec.cons b
        (BitVec.cons a (0 : BitVec 0)))))).toNat i.val =
      (if ![a,b,c,d,e] i then (1 : ZMod 2) else 0) := by decide +revert

set_option linter.unusedSimpArgs false in
private theorem upper_matrix (g : upper) : (g : SL).val = decode 5 (packedUpper (encode g)) := by
  let x := encode g
  ext i j
  fin_cases i
  · change _ = Thompson.BinaryMatrix.bit (BitVec.cons x[3]! (BitVec.cons x[2]! (BitVec.cons x[1]! (BitVec.cons x[0]! (BitVec.cons true (0 : BitVec 0)))))).toNat j.val
    rw [packed_bit]
    fin_cases j
    all_goals simp [x, encode, BitVec.getElem_cons, SylowCoordinates.bit, upper_entry]
    all_goals exact (by decide : ∀ a : ZMod 2, a = if a = 1 then 1 else 0) _
  · change _ = Thompson.BinaryMatrix.bit (BitVec.cons x[6]! (BitVec.cons x[5]! (BitVec.cons x[4]! (BitVec.cons true (BitVec.cons false (0 : BitVec 0)))))).toNat j.val
    rw [packed_bit]
    fin_cases j
    all_goals simp [x, encode, BitVec.getElem_cons, SylowCoordinates.bit, upper_entry]
    all_goals exact (by decide : ∀ a : ZMod 2, a = if a = 1 then 1 else 0) _
  · change _ = Thompson.BinaryMatrix.bit (BitVec.cons x[8]! (BitVec.cons x[7]! (BitVec.cons true (BitVec.cons false (BitVec.cons false (0 : BitVec 0)))))).toNat j.val
    rw [packed_bit]
    fin_cases j
    all_goals simp [x, encode, BitVec.getElem_cons, SylowCoordinates.bit, upper_entry]
    all_goals exact (by decide : ∀ a : ZMod 2, a = if a = 1 then 1 else 0) _
  · change _ = Thompson.BinaryMatrix.bit (BitVec.cons x[9]! (BitVec.cons true (BitVec.cons false (BitVec.cons false (BitVec.cons false (0 : BitVec 0)))))).toNat j.val
    rw [packed_bit]
    fin_cases j
    all_goals simp [x, encode, BitVec.getElem_cons, SylowCoordinates.bit, upper_entry]
    all_goals exact (by decide : ∀ a : ZMod 2, a = if a = 1 then 1 else 0) _
  · change _ = Thompson.BinaryMatrix.bit (BitVec.cons true (BitVec.cons false (BitVec.cons false (BitVec.cons false (BitVec.cons false (0 : BitVec 0)))))).toNat j.val
    rw [packed_bit]
    fin_cases j
    all_goals simp [x, encode, BitVec.getElem_cons, SylowCoordinates.bit, upper_entry]

private def certificate : ℕ → ℕ × Array ℕ × Array ℕ
  | 0 => (0, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 1 => (1, #[1, 16, 2, 4, 8], #[1, 4, 8, 16, 2])
  | 2 => (1, #[1, 2, 16, 4, 8], #[1, 2, 8, 16, 4])
  | 3 => (1, #[1, 18, 2, 4, 8], #[1, 4, 8, 16, 6])
  | 4 => (1, #[1, 2, 4, 16, 8], #[1, 2, 4, 16, 8])
  | 5 => (1, #[1, 20, 2, 4, 8], #[1, 4, 8, 16, 10])
  | 6 => (1, #[1, 2, 20, 4, 8], #[1, 2, 8, 16, 12])
  | 7 => (1, #[1, 22, 2, 4, 8], #[1, 4, 8, 16, 14])
  | 8 => (1, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 9 => (1, #[1, 24, 2, 4, 8], #[1, 4, 8, 16, 18])
  | 10 => (1, #[1, 2, 24, 4, 8], #[1, 2, 8, 16, 20])
  | 11 => (1, #[1, 26, 2, 4, 8], #[1, 4, 8, 16, 22])
  | 12 => (1, #[1, 2, 4, 24, 8], #[1, 2, 4, 16, 24])
  | 13 => (1, #[1, 28, 2, 4, 8], #[1, 4, 8, 16, 26])
  | 14 => (1, #[1, 2, 28, 4, 8], #[1, 2, 8, 16, 28])
  | 15 => (1, #[1, 30, 2, 4, 8], #[1, 4, 8, 16, 30])
  | 16 => (1, #[2, 1, 16, 4, 8], #[2, 1, 8, 16, 4])
  | 18 => (1, #[3, 1, 16, 4, 8], #[2, 3, 8, 16, 4])
  | 20 => (2, #[2, 1, 8, 16, 4], #[2, 1, 16, 4, 8])
  | 22 => (2, #[3, 1, 8, 16, 4], #[2, 3, 16, 4, 8])
  | 24 => (2, #[2, 1, 8, 4, 16], #[2, 1, 8, 4, 16])
  | 26 => (2, #[3, 1, 8, 4, 16], #[2, 3, 8, 4, 16])
  | 28 => (2, #[2, 1, 8, 20, 4], #[2, 1, 16, 4, 24])
  | 30 => (2, #[3, 1, 8, 20, 4], #[2, 3, 16, 4, 24])
  | 32 => (1, #[2, 1, 4, 16, 8], #[2, 1, 4, 16, 8])
  | 34 => (2, #[1, 2, 8, 16, 4], #[1, 2, 16, 4, 8])
  | 36 => (1, #[3, 1, 4, 16, 8], #[2, 3, 4, 16, 8])
  | 38 => (2, #[3, 2, 8, 16, 4], #[3, 2, 16, 4, 8])
  | 40 => (2, #[2, 1, 4, 8, 16], #[2, 1, 4, 8, 16])
  | 42 => (2, #[1, 2, 12, 16, 4], #[1, 2, 16, 20, 8])
  | 44 => (2, #[3, 1, 4, 8, 16], #[2, 3, 4, 8, 16])
  | 46 => (2, #[3, 2, 12, 16, 4], #[3, 2, 16, 20, 8])
  | 48 => (1, #[2, 1, 20, 4, 8], #[2, 1, 8, 16, 12])
  | 50 => (2, #[1, 3, 8, 16, 4], #[1, 3, 16, 4, 8])
  | 52 => (2, #[2, 3, 8, 16, 4], #[3, 1, 16, 4, 8])
  | 54 => (1, #[3, 1, 20, 4, 8], #[2, 3, 8, 16, 12])
  | 56 => (2, #[2, 1, 12, 4, 16], #[2, 1, 8, 12, 16])
  | 58 => (2, #[1, 3, 12, 20, 4], #[1, 3, 16, 20, 24])
  | 60 => (2, #[2, 3, 12, 20, 4], #[3, 1, 16, 20, 24])
  | 62 => (2, #[3, 1, 12, 4, 16], #[2, 3, 8, 12, 16])
  | 64 => (1, #[2, 1, 4, 8, 16], #[2, 1, 4, 8, 16])
  | 66 => (2, #[1, 2, 8, 4, 16], #[1, 2, 8, 4, 16])
  | 68 => (2, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 70 => (2, #[1, 2, 12, 4, 16], #[1, 2, 8, 12, 16])
  | 72 => (1, #[3, 1, 4, 8, 16], #[2, 3, 4, 8, 16])
  | 74 => (2, #[3, 2, 8, 4, 16], #[3, 2, 8, 4, 16])
  | 76 => (2, #[3, 2, 4, 8, 16], #[3, 2, 4, 8, 16])
  | 78 => (2, #[3, 2, 12, 4, 16], #[3, 2, 8, 12, 16])
  | 80 => (1, #[2, 1, 24, 4, 8], #[2, 1, 8, 16, 20])
  | 82 => (2, #[1, 3, 8, 4, 16], #[1, 3, 8, 4, 16])
  | 84 => (2, #[2, 1, 12, 16, 4], #[2, 1, 16, 20, 8])
  | 86 => (2, #[3, 1, 12, 20, 4], #[2, 3, 16, 20, 24])
  | 88 => (2, #[2, 3, 8, 4, 16], #[3, 1, 8, 4, 16])
  | 90 => (1, #[3, 1, 24, 4, 8], #[2, 3, 8, 16, 20])
  | 92 => (2, #[2, 1, 12, 20, 4], #[2, 1, 16, 20, 24])
  | 94 => (2, #[3, 1, 12, 16, 4], #[2, 3, 16, 20, 8])
  | 96 => (1, #[2, 1, 4, 24, 8], #[2, 1, 4, 16, 24])
  | 98 => (2, #[1, 2, 8, 20, 4], #[1, 2, 16, 4, 24])
  | 100 => (2, #[1, 3, 4, 8, 16], #[1, 3, 4, 8, 16])
  | 102 => (2, #[3, 2, 12, 20, 4], #[3, 2, 16, 20, 24])
  | 104 => (2, #[2, 3, 4, 8, 16], #[3, 1, 4, 8, 16])
  | 106 => (2, #[1, 2, 12, 20, 4], #[1, 2, 16, 20, 24])
  | 108 => (1, #[3, 1, 4, 24, 8], #[2, 3, 4, 16, 24])
  | 110 => (2, #[3, 2, 8, 20, 4], #[3, 2, 16, 4, 24])
  | 112 => (1, #[2, 1, 28, 4, 8], #[2, 1, 8, 16, 28])
  | 114 => (2, #[1, 3, 8, 20, 4], #[1, 3, 16, 4, 24])
  | 116 => (2, #[2, 3, 12, 16, 4], #[3, 1, 16, 20, 8])
  | 118 => (2, #[1, 3, 12, 4, 16], #[1, 3, 8, 12, 16])
  | 120 => (2, #[2, 3, 12, 4, 16], #[3, 1, 8, 12, 16])
  | 122 => (2, #[1, 3, 12, 16, 4], #[1, 3, 16, 20, 8])
  | 124 => (2, #[2, 3, 8, 20, 4], #[3, 1, 16, 4, 24])
  | 126 => (1, #[3, 1, 28, 4, 8], #[2, 3, 8, 16, 28])
  | 128 => (1, #[2, 4, 1, 16, 8], #[4, 1, 2, 16, 8])
  | 129 => (2, #[1, 8, 2, 16, 4], #[1, 4, 16, 2, 8])
  | 132 => (1, #[3, 4, 1, 16, 8], #[4, 5, 2, 16, 8])
  | 133 => (2, #[3, 8, 2, 16, 4], #[5, 4, 16, 2, 8])
  | 136 => (2, #[2, 4, 1, 8, 16], #[4, 1, 2, 8, 16])
  | 137 => (2, #[1, 12, 2, 16, 4], #[1, 4, 16, 18, 8])
  | 140 => (2, #[3, 4, 1, 8, 16], #[4, 5, 2, 8, 16])
  | 141 => (2, #[3, 12, 2, 16, 4], #[5, 4, 16, 18, 8])
  | 160 => (1, #[2, 5, 1, 16, 8], #[4, 1, 6, 16, 8])
  | 163 => (2, #[1, 10, 2, 16, 4], #[1, 4, 16, 6, 8])
  | 164 => (1, #[3, 5, 1, 16, 8], #[4, 5, 6, 16, 8])
  | 167 => (2, #[3, 10, 2, 16, 4], #[5, 4, 16, 6, 8])
  | 168 => (2, #[2, 5, 1, 8, 16], #[4, 1, 6, 8, 16])
  | 171 => (2, #[1, 14, 2, 16, 4], #[1, 4, 16, 22, 8])
  | 172 => (2, #[3, 5, 1, 8, 16], #[4, 5, 6, 8, 16])
  | 175 => (2, #[3, 14, 2, 16, 4], #[5, 4, 16, 22, 8])
  | 192 => (2, #[4, 2, 1, 8, 16], #[4, 2, 1, 8, 16])
  | 196 => (2, #[5, 2, 1, 8, 16], #[4, 2, 5, 8, 16])
  | 200 => (2, #[6, 2, 1, 8, 16], #[4, 2, 3, 8, 16])
  | 204 => (2, #[7, 2, 1, 8, 16], #[4, 2, 7, 8, 16])
  | 224 => (2, #[4, 3, 1, 8, 16], #[4, 6, 1, 8, 16])
  | 228 => (2, #[5, 3, 1, 8, 16], #[4, 6, 5, 8, 16])
  | 232 => (2, #[6, 3, 1, 8, 16], #[4, 6, 7, 8, 16])
  | 236 => (2, #[7, 3, 1, 8, 16], #[4, 6, 3, 8, 16])
  | 256 => (1, #[2, 4, 1, 8, 16], #[4, 1, 2, 8, 16])
  | 257 => (2, #[1, 8, 2, 4, 16], #[1, 4, 8, 2, 16])
  | 260 => (2, #[1, 4, 2, 8, 16], #[1, 4, 2, 8, 16])
  | 261 => (2, #[1, 12, 2, 4, 16], #[1, 4, 8, 10, 16])
  | 264 => (1, #[3, 4, 1, 8, 16], #[4, 5, 2, 8, 16])
  | 265 => (2, #[3, 8, 2, 4, 16], #[5, 4, 8, 2, 16])
  | 268 => (2, #[3, 4, 2, 8, 16], #[5, 4, 2, 8, 16])
  | 269 => (2, #[3, 12, 2, 4, 16], #[5, 4, 8, 10, 16])
  | 288 => (2, #[4, 1, 2, 8, 16], #[2, 4, 1, 8, 16])
  | 292 => (2, #[5, 1, 2, 8, 16], #[2, 4, 3, 8, 16])
  | 296 => (2, #[6, 1, 2, 8, 16], #[2, 4, 5, 8, 16])
  | 300 => (2, #[7, 1, 2, 8, 16], #[2, 4, 7, 8, 16])
  | 320 => (1, #[2, 5, 1, 8, 16], #[4, 1, 6, 8, 16])
  | 323 => (2, #[1, 10, 2, 4, 16], #[1, 4, 8, 6, 16])
  | 324 => (2, #[1, 6, 2, 8, 16], #[1, 4, 6, 8, 16])
  | 327 => (2, #[1, 14, 2, 4, 16], #[1, 4, 8, 14, 16])
  | 328 => (1, #[3, 5, 1, 8, 16], #[4, 5, 6, 8, 16])
  | 331 => (2, #[3, 10, 2, 4, 16], #[5, 4, 8, 6, 16])
  | 332 => (2, #[3, 6, 2, 8, 16], #[5, 4, 6, 8, 16])
  | 335 => (2, #[3, 14, 2, 4, 16], #[5, 4, 8, 14, 16])
  | 352 => (2, #[4, 3, 2, 8, 16], #[6, 4, 1, 8, 16])
  | 356 => (2, #[5, 3, 2, 8, 16], #[6, 4, 7, 8, 16])
  | 360 => (2, #[6, 3, 2, 8, 16], #[6, 4, 5, 8, 16])
  | 364 => (2, #[7, 3, 2, 8, 16], #[6, 4, 3, 8, 16])
  | 384 => (1, #[2, 4, 1, 24, 8], #[4, 1, 2, 16, 24])
  | 385 => (2, #[1, 8, 2, 20, 4], #[1, 4, 16, 2, 24])
  | 388 => (2, #[1, 4, 3, 8, 16], #[1, 5, 2, 8, 16])
  | 389 => (2, #[3, 12, 2, 20, 4], #[5, 4, 16, 18, 24])
  | 392 => (2, #[2, 4, 3, 8, 16], #[5, 1, 2, 8, 16])
  | 393 => (2, #[1, 12, 2, 20, 4], #[1, 4, 16, 18, 24])
  | 396 => (1, #[3, 4, 1, 24, 8], #[4, 5, 2, 16, 24])
  | 397 => (2, #[3, 8, 2, 20, 4], #[5, 4, 16, 2, 24])
  | 416 => (2, #[4, 1, 3, 8, 16], #[2, 6, 1, 8, 16])
  | 420 => (2, #[5, 1, 3, 8, 16], #[2, 6, 3, 8, 16])
  | 424 => (2, #[6, 1, 3, 8, 16], #[2, 6, 7, 8, 16])
  | 428 => (2, #[7, 1, 3, 8, 16], #[2, 6, 5, 8, 16])
  | 448 => (2, #[4, 2, 3, 8, 16], #[6, 2, 1, 8, 16])
  | 452 => (2, #[5, 2, 3, 8, 16], #[6, 2, 7, 8, 16])
  | 456 => (2, #[6, 2, 3, 8, 16], #[6, 2, 3, 8, 16])
  | 460 => (2, #[7, 2, 3, 8, 16], #[6, 2, 5, 8, 16])
  | 480 => (1, #[2, 5, 1, 24, 8], #[4, 1, 6, 16, 24])
  | 483 => (2, #[1, 10, 2, 20, 4], #[1, 4, 16, 6, 24])
  | 484 => (2, #[1, 7, 3, 8, 16], #[1, 5, 6, 8, 16])
  | 487 => (2, #[3, 14, 2, 20, 4], #[5, 4, 16, 22, 24])
  | 488 => (2, #[2, 7, 3, 8, 16], #[5, 1, 6, 8, 16])
  | 491 => (2, #[1, 14, 2, 20, 4], #[1, 4, 16, 22, 24])
  | 492 => (1, #[3, 5, 1, 24, 8], #[4, 5, 6, 16, 24])
  | 495 => (2, #[3, 10, 2, 20, 4], #[5, 4, 16, 6, 24])
  | 512 => (1, #[2, 4, 8, 1, 16], #[8, 1, 2, 4, 16])
  | 513 => (2, #[1, 8, 4, 2, 16], #[1, 8, 4, 2, 16])
  | 514 => (2, #[1, 4, 8, 2, 16], #[1, 8, 2, 4, 16])
  | 515 => (2, #[1, 12, 4, 2, 16], #[1, 8, 4, 6, 16])
  | 520 => (1, #[3, 4, 8, 1, 16], #[8, 9, 2, 4, 16])
  | 521 => (2, #[3, 8, 4, 2, 16], #[9, 8, 4, 2, 16])
  | 522 => (2, #[3, 4, 8, 2, 16], #[9, 8, 2, 4, 16])
  | 523 => (2, #[3, 12, 4, 2, 16], #[9, 8, 4, 6, 16])
  | 528 => (2, #[4, 1, 8, 2, 16], #[2, 8, 1, 4, 16])
  | 530 => (2, #[5, 1, 8, 2, 16], #[2, 8, 3, 4, 16])
  | 536 => (2, #[6, 1, 8, 2, 16], #[2, 8, 9, 4, 16])
  | 538 => (2, #[7, 1, 8, 2, 16], #[2, 8, 11, 4, 16])
  | 576 => (1, #[2, 5, 8, 1, 16], #[8, 1, 10, 4, 16])
  | 578 => (2, #[1, 6, 8, 2, 16], #[1, 8, 10, 4, 16])
  | 581 => (2, #[1, 10, 4, 2, 16], #[1, 8, 4, 10, 16])
  | 583 => (2, #[1, 14, 4, 2, 16], #[1, 8, 4, 14, 16])
  | 584 => (1, #[3, 5, 8, 1, 16], #[8, 9, 10, 4, 16])
  | 586 => (2, #[3, 6, 8, 2, 16], #[9, 8, 10, 4, 16])
  | 589 => (2, #[3, 10, 4, 2, 16], #[9, 8, 4, 10, 16])
  | 591 => (2, #[3, 14, 4, 2, 16], #[9, 8, 4, 14, 16])
  | 592 => (2, #[4, 3, 8, 2, 16], #[10, 8, 1, 4, 16])
  | 594 => (2, #[5, 3, 8, 2, 16], #[10, 8, 11, 4, 16])
  | 600 => (2, #[6, 3, 8, 2, 16], #[10, 8, 9, 4, 16])
  | 602 => (2, #[7, 3, 8, 2, 16], #[10, 8, 3, 4, 16])
  | 768 => (1, #[2, 4, 9, 1, 16], #[8, 1, 2, 12, 16])
  | 769 => (2, #[1, 8, 6, 2, 16], #[1, 8, 12, 2, 16])
  | 774 => (2, #[1, 4, 10, 2, 16], #[1, 8, 2, 12, 16])
  | 775 => (2, #[1, 12, 6, 2, 16], #[1, 8, 12, 14, 16])
  | 776 => (1, #[3, 4, 9, 1, 16], #[8, 9, 2, 12, 16])
  | 777 => (2, #[3, 8, 6, 2, 16], #[9, 8, 12, 2, 16])
  | 782 => (2, #[3, 4, 10, 2, 16], #[9, 8, 2, 12, 16])
  | 783 => (2, #[3, 12, 6, 2, 16], #[9, 8, 12, 14, 16])
  | 816 => (2, #[4, 1, 10, 2, 16], #[2, 8, 1, 12, 16])
  | 822 => (2, #[5, 1, 10, 2, 16], #[2, 8, 3, 12, 16])
  | 824 => (2, #[6, 1, 10, 2, 16], #[2, 8, 9, 12, 16])
  | 830 => (2, #[7, 1, 10, 2, 16], #[2, 8, 11, 12, 16])
  | 832 => (1, #[2, 5, 9, 1, 16], #[8, 1, 10, 12, 16])
  | 835 => (2, #[1, 14, 6, 2, 16], #[1, 8, 12, 6, 16])
  | 837 => (2, #[1, 10, 6, 2, 16], #[1, 8, 12, 10, 16])
  | 838 => (2, #[1, 6, 10, 2, 16], #[1, 8, 10, 12, 16])
  | 840 => (1, #[3, 5, 9, 1, 16], #[8, 9, 10, 12, 16])
  | 843 => (2, #[3, 14, 6, 2, 16], #[9, 8, 12, 6, 16])
  | 845 => (2, #[3, 10, 6, 2, 16], #[9, 8, 12, 10, 16])
  | 846 => (2, #[3, 6, 10, 2, 16], #[9, 8, 10, 12, 16])
  | 880 => (2, #[4, 3, 10, 2, 16], #[10, 8, 1, 12, 16])
  | 886 => (2, #[5, 3, 10, 2, 16], #[10, 8, 11, 12, 16])
  | 888 => (2, #[6, 3, 10, 2, 16], #[10, 8, 9, 12, 16])
  | 894 => (2, #[7, 3, 10, 2, 16], #[10, 8, 3, 12, 16])
  | _ => (0, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])


private def representativeRows : ℕ → Array ℕ
  | 0 => #[1, 2, 4, 8, 16]
  | 1 => #[17, 2, 4, 8, 16]
  | _ => #[9, 18, 4, 8, 16]

private def checkCertificate (a : BitVec 10) : Bool :=
  let (r, q, qi) := certificate a.toNat
  decide (r ≤ 2) && (List.range 5).all (fun i =>
    decide (rowProduct q[i]! qi 5 = 2 ^ i) &&
    decide (rowProduct (packedUpper a)[i]! q 5 = rowProduct q[i]! (representativeRows r) 5))

set_option maxRecDepth 4096 in
private theorem certificates_checked : involutionList.all checkCertificate = true := by
  decide +kernel

private theorem certificate_spec (a : BitVec 10) (ha : square a = true) :
    (certificate a.toNat).1 ≤ 2 ∧
    decode 5 (certificate a.toNat).2.1 * decode 5 (certificate a.toNat).2.2 = 1 ∧
    decode 5 (packedUpper a) * decode 5 (certificate a.toNat).2.1 =
      decode 5 (certificate a.toNat).2.1 * decode 5 (representativeRows (certificate a.toNat).1) := by
  have hh := List.all_eq_true.mp certificates_checked a (square_mem a ha)
  simp only [checkCertificate, Bool.and_eq_true, decide_eq_true_eq] at hh
  refine ⟨hh.1, decode_mul_one _ _ _ ?_, ?_⟩
  · intro i
    have hi := List.all_eq_true.mp hh.2 i.val (List.mem_range.mpr i.isLt)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    exact hi.1
  · ext i j
    have hi := List.all_eq_true.mp hh.2 i.val (List.mem_range.mpr i.isLt)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    change (∑ k : Fin 5, Thompson.BinaryMatrix.bit (packedUpper a)[i.val]! k.val *
      Thompson.BinaryMatrix.bit (certificate a.toNat).2.1[k.val]! j.val) =
      (∑ k : Fin 5, Thompson.BinaryMatrix.bit (certificate a.toNat).2.1[i.val]! k.val *
      Thompson.BinaryMatrix.bit (representativeRows (certificate a.toNat).1)[k.val]! j.val)
    rw [Fin.sum_univ_eq_sum_range (fun k => Thompson.BinaryMatrix.bit (packedUpper a)[i.val]! k *
      Thompson.BinaryMatrix.bit (certificate a.toNat).2.1[k]! j.val),
      Fin.sum_univ_eq_sum_range (fun k => Thompson.BinaryMatrix.bit (certificate a.toNat).2.1[i.val]! k *
      Thompson.BinaryMatrix.bit (representativeRows (certificate a.toNat).1)[k]! j.val),
      ← bit_rowProduct, ← bit_rowProduct, hi.2]

private theorem det_one_of_right_inverse (A B : Matrix (Fin 5) (Fin 5) (ZMod 2))
    (h : A * B = 1) : A.det = 1 := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at hd
  have hn : A.det ≠ 0 := by intro he; simp [he] at hd
  exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hn

private def second : SL := root (show (0 : Fin 5) < 3 by decide) *
  root (show (1 : Fin 5) < 4 by decide)

private def representative : ℕ → SL
  | 0 => 1
  | 1 => transvection
  | _ => second

private theorem representative_matrix (r : ℕ) :
    (representative r).val = decode 5 (representativeRows r) := by
  rcases r with _ | _ | r
  · decide
  · decide
  · change second.val = decode 5 #[9, 18, 4, 8, 16]
    decide

private theorem upper_two_classes (g : upper) (hg : (g : SL) ^ 2 = 1) :
    (g : SL) = 1 ∨ IsConj transvection (g : SL) ∨ IsConj second (g : SL) := by
  have hs := certificate_spec (encode g) (square_encode g (by simpa [pow_two] using hg))
  let q : SL := ⟨decode 5 (certificate (encode g).toNat).2.1,
    det_one_of_right_inverse _ _ hs.2.1⟩
  have he : (g : SL) * q = q * representative (certificate (encode g).toNat).1 := by
    apply Subtype.ext
    change (g : SL).val * q.val = q.val * (representative _).val
    rw [upper_matrix, representative_matrix]
    exact hs.2.2
  have hc : IsConj (representative (certificate (encode g).toNat).1) (g : SL) :=
    isConj_iff.mpr ⟨q, mul_inv_eq_iff_eq_mul.mpr he.symm⟩
  have hr := hs.1
  have hr' : (certificate (encode g).toNat).1 = 0 ∨
      (certificate (encode g).toNat).1 = 1 ∨ (certificate (encode g).toNat).1 = 2 := by omega
  rcases hr' with h | h | h <;> rw [h] at hc
  · exact Or.inl (isConj_one_right.mp hc)
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr hc)

open scoped Pointwise

private theorem involution_into_sylow {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (x : G) (hx : orderOf x = 2) :
    ∃ y : S, IsConj x (y : G) := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx]; rfl)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  have hm : (MulAut.conj g) x ∈ (S : Subgroup G) := by
    rw [← hg]
    change (MulAut.conj g) • x ∈ (MulAut.conj g) • (P : Set G)
    exact Set.smul_mem_smul_set (hP (mem_zpowers x))
  exact ⟨⟨(MulAut.conj g) x, hm⟩, isConj_iff.mpr ⟨g, rfl⟩⟩

private theorem native_two_classes (x : SL) (hx : orderOf x = 2) :
    IsConj transvection x ∨ IsConj second x := by
  obtain ⟨y, hy⟩ := involution_into_sylow (sourceSylow nativeMarking) x hx
  have hyu : (y : SL) ∈ upper := by
    have hm : (y : SL) ∈ (sourceSylow nativeMarking : Subgroup SL) := y.property
    rw [coe_sourceSylow, nativeMarking_pullback _
      ((model_upper_eq_unipotent ▸ upper_le_centralizer) :
        Theory.SpecificGroups.LinearSylowNormalizers.unipotent 5 (ZMod 2) ≤ centralizer),
      ← model_upper_eq_unipotent] at hm
    exact hm
  have hyo : orderOf (y : SL) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hy
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  rcases upper_two_classes ⟨y, hyu⟩ (by simpa only [hyo] using pow_orderOf_eq_one (y : SL)) with he | hz | ht
  · change (y : SL) = 1 at he
    rw [he, orderOf_one] at hyo
    omega
  · exact Or.inl (hz.trans hy.symm)
  · exact Or.inr (ht.trans hy.symm)

private theorem conj_order {G : Type*} [Group G] {x y : G}
    (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).symm

private theorem two_classes_of_equiv {G : Type*} [Group G] (e : G ≃* SL)
    {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : ¬ IsConj a b)
    (x : G) (hx : orderOf x = 2) : IsConj a x ∨ IsConj b x := by
  have back {u v : G} (h : IsConj (e u) (e v)) : IsConj u v := by
    simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using e.symm.toMonoidHom.map_isConj h
  have ha' := native_two_classes (e a) ((e.orderOf_eq a).trans ha)
  have hb' := native_two_classes (e b) ((e.orderOf_eq b).trans hb)
  have hx' := native_two_classes (e x) ((e.orderOf_eq x).trans hx)
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
  · exact (hab (back (ha'.symm.trans hb'))).elim
  · exact hx'.imp (fun h => back (ha'.symm.trans h)) (fun h => back (hb'.symm.trans h))
  · exact hx'.symm.imp (fun h => back (ha'.symm.trans h)) (fun h => back (hb'.symm.trans h))
  · exact (hab (back (ha'.symm.trans hb'))).elim

variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

omit [Finite G] in
/-- Literal restriction preserves every rectangle coordinate, including the
second involution chosen in the intersection of the two rectangles. -/
theorem normalizerSpan_element_val (a : PlaneCensus.Code) :
    (PlaneTensor.element (G := normalizerSpan F) (normalizerSpanMarking F) a : G) = PlaneTensor.element F a := by
  have he := PlaneTensor.element_model (normalizerSpanMarking F) a
  have hc : (PlaneTensor.element (G := normalizerSpan F) (normalizerSpanMarking F) a : G) ∈
      Subgroup.centralizer ({z} : Set G) :=
    by
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp
          ((normalizerSpanMarking F).pullback_le _ (PlaneTensor.element_mem _ a))))
  have he' : (F.equiv ⟨_, hc⟩ : SL) =
      (F.equiv ⟨PlaneTensor.element F a, F.pullback_le _ (PlaneTensor.element_mem F a)⟩ : SL) := by
    rw [PlaneTensor.element_model]
    exact he
  exact congrArg Subtype.val (F.equiv.injective (Subtype.ext he'))

omit [Finite G] in
/-- The chosen rank-two representative is unchanged by literal inclusion. -/
theorem normalizerSpan_secondPoint_val :
    ((planeSecondPoint (normalizerSpanMarking F) : normalizerSpan F) : G) = planeSecondPoint F :=
  normalizerSpan_element_val F 34

/-- The normalizer-generated subgroup has the two original marked involution
classes. No compatibility of a chosen recognition isomorphism with the marking
is needed: the fusion count separates the two marked representatives. -/
theorem normalizerSpan_two_involution_classes (hlinear : F.LinearFusion)
    (x : normalizerSpan F) (hx : orderOf x = 2) :
    IsConj (overgroupPoint (normalizerSpan F) (point_centralizer_le_normalizerSpan F)) x ∨
      IsConj (planeSecondPoint (normalizerSpanMarking F)) x := by
  obtain ⟨e⟩ := normalizerSpan_nonempty_equiv F hlinear
  exact two_classes_of_equiv e (normalizerSpanMarking F).point_orderOf
    (planeSecondPoint_order _) (planeSecondPoint_not_conjugate _
      (normalizerSpan_linearFusion F hlinear)) x hx

/-- All ambient involutions are fused into the actual generated subgroup,
using its common Sylow with the ambient group. -/
theorem involution_conjugate_into_normalizerSpan (x : G) (hx : orderOf x = 2) :
    ∃ y : normalizerSpan F, IsConj x (y : G) := by
  obtain ⟨y, hy⟩ := involution_into_sylow (sourceSylow F) x hx
  exact ⟨⟨y, point_centralizer_le_normalizerSpan F
    (sourceSylow_le_point_centralizer F y.property)⟩, hy⟩

/-- Source 40.6 in the linear branch: the ambient group has precisely the
classes represented by the marked point and the rank-two rectangle element. -/
theorem linear_two_involution_classes (hlinear : F.LinearFusion)
    (x : G) (hx : orderOf x = 2) : IsConj z x ∨ IsConj (planeSecondPoint F) x := by
  obtain ⟨y, hy⟩ := involution_conjugate_into_normalizerSpan F x hx
  have hyo : orderOf y = 2 := (Subgroup.orderOf_coe y).symm.trans ((conj_order hy).symm.trans hx)
  have hm := normalizerSpan_two_involution_classes F hlinear y hyo
  rcases hm with hz | ht
  · exact Or.inl (((normalizerSpan F).subtype.map_isConj hz).trans hy.symm)
  · have hh := (normalizerSpan F).subtype.map_isConj ht
    change IsConj (PlaneTensor.element (G := normalizerSpan F) (normalizerSpanMarking F) 34 : G) (y : G) at hh
    rw [normalizerSpan_element_val] at hh
    exact Or.inr (hh.trans hy.symm)

/-- The actual generated subgroup controls fusion of every involution it
contains. This establishes both class-intersection equalities used in 41.1. -/
theorem normalizerSpan_involution_fusion (hlinear : F.LinearFusion)
    (a b : normalizerSpan F) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : IsConj (a : G) (b : G)) : IsConj a b := by
  have hz := planeSecondPoint_not_conjugate F hlinear
  have cast_point : ((normalizerSpan F).subtype
      (overgroupPoint (normalizerSpan F) (point_centralizer_le_normalizerSpan F))) = z := rfl
  have cast_second : ((normalizerSpan F).subtype
      (planeSecondPoint (normalizerSpanMarking F))) = planeSecondPoint F :=
    normalizerSpan_element_val F 34
  rcases normalizerSpan_two_involution_classes F hlinear a ha with hza | hta <;>
    rcases normalizerSpan_two_involution_classes F hlinear b hb with hzb | htb
  · exact hza.symm.trans hzb
  · have hh := ((normalizerSpan F).subtype.map_isConj hza).trans
      (hab.trans ((normalizerSpan F).subtype.map_isConj htb).symm)
    rw [cast_point, cast_second] at hh
    exact (hz hh).elim
  · have hh := ((normalizerSpan F).subtype.map_isConj hzb).trans
      (hab.symm.trans ((normalizerSpan F).subtype.map_isConj hta).symm)
    rw [cast_point, cast_second] at hh
    exact (hz hh).elim
  · exact hta.symm.trans htb

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
