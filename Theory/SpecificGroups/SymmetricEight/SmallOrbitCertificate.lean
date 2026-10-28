module
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel
public import Theory.Representation.BinaryPermutation.EightCoreLine
/-!
# Small-orbit displacement certificates in the eight-point Sylow

The 128 binary-tree words contain only 44 involutions. For 32 of them,
commuting involutions have orbits of size at most four on two specified
pair words, whose displacements have total weight two or eight. The twelve
remaining words reduce, using subgroup closure, to the even pair group.
The last two pair words give weight eight there.

These bounded certificates support the augmentation-core calculation in
Aschbacher--Smith, combined manuscript of 1 March 2004, 12.6.22, p.829.
They enumerate words and their centralizers, not permutations or subgroups.
-/

@[expose] public section
open Subgroup BinaryPermutation
open BinaryPermutation.EightNonsingular
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace BinaryPermutation.EightSmallOrbits
abbrev S := Equiv.Perm (Fin 8)
abbrev C := core (Fin 8)
def bad : Finset (Fin 128) := {0,3,5,6,9,10,12,15,16,19,32,44}
def actors : Fin 32 → Fin 128 := ![1,2,4,7,8,11,13,14,20,23,24,27,28,31,33,34,35,45,46,47,48,51,60,63,64,69,74,79,112,118,121,127]
def first : Fin 32 → C := ![pair 0 2,
pair 0 2,
pair 4 6,
pair 4 6,
pair 4 6,
pair 4 6,
pair 0 2,
pair 0 2,
pair 4 6,
pair 4 6,
pair 4 6,
pair 4 6,
pair 0 1,
pair 0 1,
pair 0 2,
pair 0 2,
pair 0 2,
pair 0 2,
pair 0 2,
pair 0 2,
pair 0 1,
pair 0 1,
pair 0 1,
pair 0 1,
pair 0 1,
pair 0 1,
pair 0 1,
pair 0 1,
pair 0 1,
pair 0 1,
pair 0 1,
pair 0 1]
def second : Fin 32 → C := ![pair 0 0,
pair 0 0,
pair 0 0,
pair 0 0,
pair 0 0,
pair 0 0,
pair 0 0,
pair 0 0,
pair 0 0,
pair 0 0,
pair 0 0,
pair 0 0,
pair 4 6,
pair 4 6,
pair 0 0,
pair 0 0,
pair 4 5,
pair 0 0,
pair 0 0,
pair 4 5,
pair 4 5,
pair 4 5,
pair 4 5,
pair 4 5,
pair 2 3,
pair 2 3,
pair 2 3,
pair 2 3,
pair 2 3,
pair 2 3,
pair 2 3,
pair 2 3]
def firstCover : Fin 32 → Fin 4 → C := ![![pair 0 2, pair 1 2, pair 0 3, pair 1 3],
![pair 0 2, pair 1 2, pair 0 3, pair 1 3],
![pair 4 6, pair 5 6, pair 4 7, pair 5 7],
![pair 4 6, pair 5 6, pair 4 7, pair 5 7],
![pair 4 6, pair 5 6, pair 4 7, pair 5 7],
![pair 4 6, pair 5 6, pair 4 7, pair 5 7],
![pair 0 2, pair 1 2, pair 0 3, pair 1 3],
![pair 0 2, pair 1 2, pair 0 3, pair 1 3],
![pair 4 6, pair 5 6, pair 4 7, pair 5 7],
![pair 4 6, pair 5 6, pair 4 7, pair 5 7],
![pair 4 6, pair 5 6, pair 4 7, pair 5 7],
![pair 4 6, pair 5 6, pair 4 7, pair 5 7],
![pair 0 1, pair 2 3, pair 0 1, pair 0 1],
![pair 0 1, pair 2 3, pair 0 1, pair 0 1],
![pair 0 2, pair 1 2, pair 0 3, pair 1 3],
![pair 0 2, pair 1 2, pair 0 3, pair 1 3],
![pair 0 2, pair 1 2, pair 0 3, pair 1 3],
![pair 0 2, pair 1 2, pair 0 3, pair 1 3],
![pair 0 2, pair 1 2, pair 0 3, pair 1 3],
![pair 0 2, pair 1 2, pair 0 3, pair 1 3],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7]]
def secondCover : Fin 32 → Fin 4 → C := ![![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 4 6, pair 5 6, pair 4 7, pair 5 7],
![pair 4 6, pair 5 6, pair 4 7, pair 5 7],
![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 4 5, pair 6 7, pair 4 5, pair 4 5],
![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 0 0, pair 0 0, pair 0 0, pair 0 0],
![pair 4 5, pair 6 7, pair 4 5, pair 4 5],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7],
![pair 0 1, pair 2 3, pair 4 5, pair 6 7]]
def row (i : Fin 32) : Prop :=
  (∀ j : Fin 128, (treeWord j)^2 = 1 →
    treeWord j * treeWord (actors i) = treeWord (actors i) * treeWord j →
    (∃ k : Fin 4, coreRepresentation (Fin 8) (treeWord j) (first i) = firstCover i k) ∧
    (∃ k : Fin 4, coreRepresentation (Fin 8) (treeWord j) (second i) = secondCover i k)) ∧
  (let d := coreRepresentation (Fin 8) (treeWord (actors i)) (first i) + first i +
    (coreRepresentation (Fin 8) (treeWord (actors i)) (second i) + second i)
   hammingNorm d.val = 2 ∨ hammingNorm d.val = 8)
instance (i : Fin 32) : Decidable (row i) := by unfold row; infer_instance
set_option maxRecDepth 2048 in
theorem row_0 : row 0 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_1 : row 1 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_2 : row 2 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_3 : row 3 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_4 : row 4 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_5 : row 5 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_6 : row 6 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_7 : row 7 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_8 : row 8 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_9 : row 9 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_10 : row 10 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_11 : row 11 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_12 : row 12 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_13 : row 13 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_14 : row 14 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_15 : row 15 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_16 : row 16 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_17 : row 17 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_18 : row 18 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_19 : row 19 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_20 : row 20 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_21 : row 21 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_22 : row 22 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_23 : row 23 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_24 : row 24 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_25 : row 25 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_26 : row 26 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_27 : row 27 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_28 : row 28 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_29 : row 29 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_30 : row 30 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_31 : row 31 := by decide +kernel
theorem rows (i : Fin 32) : row i := by
  fin_cases i
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4
  · exact row_5
  · exact row_6
  · exact row_7
  · exact row_8
  · exact row_9
  · exact row_10
  · exact row_11
  · exact row_12
  · exact row_13
  · exact row_14
  · exact row_15
  · exact row_16
  · exact row_17
  · exact row_18
  · exact row_19
  · exact row_20
  · exact row_21
  · exact row_22
  · exact row_23
  · exact row_24
  · exact row_25
  · exact row_26
  · exact row_27
  · exact row_28
  · exact row_29
  · exact row_30
  · exact row_31
theorem involution_cover : ∀ i : Fin 128, (treeWord i)^2 = 1 →
    i ∈ bad ∨ ∃ j, actors j = i := by decide +kernel

def exceptional : Finset (Fin 128) := {16,19,32,44}
def base : Finset (Fin 128) := {0,3,5,6,9,10,12,15}
def exceptionalCover : Fin 4 → Fin 4 → Fin 128 :=
  ![![0,3,16,19], ![0,3,16,19], ![0,12,32,44], ![0,12,32,44]]
def exceptionalActor : Fin 4 → Fin 128 := ![16,19,32,44]
theorem bad_split : ∀ i ∈ bad, i ∈ base ∨ i ∈ exceptional := by decide +kernel

def badIndex : Fin 12 → Fin 128 := ![0,3,5,6,9,10,12,15,16,19,32,44]
theorem bad_index : ∀ j ∈ bad, ∃ k, badIndex k = j := by decide +kernel
set_option maxRecDepth 2048 in
theorem exceptional_small : ∀ i : Fin 4, ∀ j : Fin 12,
    treeWord (badIndex j) * treeWord (exceptionalActor i) =
      treeWord (exceptionalActor i) * treeWord (badIndex j) →
    (∃ k : Fin 12, treeWord (badIndex j) * treeWord (exceptionalActor i) = treeWord (badIndex k)) →
    ∃ k, badIndex j = exceptionalCover i k := by decide +kernel

theorem exceptional_exhaustive : ∀ i ∈ exceptional, ∃ j, exceptionalActor j = i := by decide

def finalFirst : C := pair 0 2
def finalSecond : C := pair 4 6
def finalFirstCover : Fin 4 → C := ![pair 0 2,pair 0 3,pair 1 2,pair 1 3]
def finalSecondCover : Fin 4 → C := ![pair 4 6,pair 4 7,pair 5 6,pair 5 7]
theorem final_covers : ∀ j ∈ base,
    (∃ k, coreRepresentation (Fin 8) (treeWord j) finalFirst = finalFirstCover k) ∧
    (∃ k, coreRepresentation (Fin 8) (treeWord j) finalSecond = finalSecondCover k) := by decide +kernel

theorem final_weight : hammingNorm
    (coreRepresentation (Fin 8) (treeWord 15) finalFirst + finalFirst +
    (coreRepresentation (Fin 8) (treeWord 15) finalSecond + finalSecond)).val = 8 := by decide +kernel
end BinaryPermutation.EightSmallOrbits
