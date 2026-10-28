module
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel
public import Theory.Representation.BinaryPermutation.EightNonsingularStabilizer
/-!
# Small moved orbits in the binary eight-point natural module

For every tree involution except the central pair reversal, the commuting
involutions move a specified pair word among at most four pair words. Its
own displacement is neither zero nor the constant word, so survives the
natural quotient. The remaining elementary actor has at most two elements.
These small certificates concern 128 tree words, without enumerating S8.

Source: Aschbacher--Smith, 12.6.28(1), printed p.834. They give a direct
small-orbit proof of the intrinsic corank-three fixed-space exclusion.
-/

@[expose] public section
open BinaryPermutation BinaryPermutation.EightNonsingular
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace BinaryPermutation.EightRigidityCertificate
abbrev C := core (Fin 8)
def actors : Fin 42 → Fin 128 := ![1,2,3,4,5,6,7,8,9,10,11,12,13,14,16,19,20,23,24,27,28,31,32,33,34,35,44,45,46,47,48,51,60,63,64,69,74,79,112,118,121,127]
def vector : Fin 42 → C := ![pair 0 2,pair 0 2,pair 0 2,pair 4 6,pair 0 4,pair 2 4,pair 0 2,pair 4 6,pair 0 6,pair 2 6,pair 0 2,pair 4 6,pair 0 2,pair 0 2,pair 0 1,pair 0 1,pair 0 1,pair 0 1,pair 0 1,pair 0 1,pair 0 1,pair 0 1,pair 4 5,pair 4 5,pair 4 5,pair 4 5,pair 4 5,pair 4 5,pair 4 5,pair 4 5,pair 0 1,pair 0 1,pair 0 1,pair 0 1,pair 0 1,pair 0 1,pair 0 1,pair 0 1,pair 0 1,pair 0 1,pair 0 1,pair 0 1]
def cover : Fin 42 → Fin 4 → C := ![![pair 0 2,pair 0 3,pair 1 2,pair 1 3],![pair 0 2,pair 0 3,pair 1 2,pair 1 3],![pair 0 2,pair 0 3,pair 1 2,pair 1 3],![pair 4 6,pair 4 7,pair 5 6,pair 5 7],![pair 0 4,pair 0 5,pair 1 4,pair 1 5],![pair 2 4,pair 2 5,pair 3 4,pair 3 5],![pair 0 2,pair 0 3,pair 1 2,pair 1 3],![pair 4 6,pair 4 7,pair 5 6,pair 5 7],![pair 0 6,pair 0 7,pair 1 6,pair 1 7],![pair 2 6,pair 2 7,pair 3 6,pair 3 7],![pair 0 2,pair 0 3,pair 1 2,pair 1 3],![pair 4 6,pair 4 7,pair 5 6,pair 5 7],![pair 0 2,pair 0 3,pair 1 2,pair 1 3],![pair 0 2,pair 0 3,pair 1 2,pair 1 3],![pair 0 1,pair 2 3,pair 0 1,pair 0 1],![pair 0 1,pair 2 3,pair 0 1,pair 0 1],![pair 0 1,pair 2 3,pair 0 1,pair 0 1],![pair 0 1,pair 2 3,pair 0 1,pair 0 1],![pair 0 1,pair 2 3,pair 0 1,pair 0 1],![pair 0 1,pair 2 3,pair 0 1,pair 0 1],![pair 0 1,pair 2 3,pair 0 1,pair 0 1],![pair 0 1,pair 2 3,pair 0 1,pair 0 1],![pair 4 5,pair 6 7,pair 4 5,pair 4 5],![pair 4 5,pair 6 7,pair 4 5,pair 4 5],![pair 4 5,pair 6 7,pair 4 5,pair 4 5],![pair 4 5,pair 6 7,pair 4 5,pair 4 5],![pair 4 5,pair 6 7,pair 4 5,pair 4 5],![pair 4 5,pair 6 7,pair 4 5,pair 4 5],![pair 4 5,pair 6 7,pair 4 5,pair 4 5],![pair 4 5,pair 6 7,pair 4 5,pair 4 5],![pair 0 1,pair 2 3,pair 4 5,pair 6 7],![pair 0 1,pair 2 3,pair 4 5,pair 6 7],![pair 0 1,pair 2 3,pair 4 5,pair 6 7],![pair 0 1,pair 2 3,pair 4 5,pair 6 7],![pair 0 1,pair 2 3,pair 4 5,pair 6 7],![pair 0 1,pair 2 3,pair 4 5,pair 6 7],![pair 0 1,pair 2 3,pair 4 5,pair 6 7],![pair 0 1,pair 2 3,pair 4 5,pair 6 7],![pair 0 1,pair 2 3,pair 4 5,pair 6 7],![pair 0 1,pair 2 3,pair 4 5,pair 6 7],![pair 0 1,pair 2 3,pair 4 5,pair 6 7],![pair 0 1,pair 2 3,pair 4 5,pair 6 7]]
def row (i : Fin 42) : Prop :=
  (∀ j : Fin 128, (treeWord j)^2 = 1 →
    treeWord j * treeWord (actors i) = treeWord (actors i) * treeWord j →
    ∃ k : Fin 4, coreRepresentation (Fin 8) (treeWord j) (vector i) = cover i k) ∧
  (coreRepresentation (Fin 8) (treeWord (actors i)) (vector i) - vector i).val ≠ 0 ∧
  (coreRepresentation (Fin 8) (treeWord (actors i)) (vector i) - vector i).val ≠ allOne (Fin 8)
instance (i : Fin 42) : Decidable (row i) := by unfold row; infer_instance
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
set_option maxRecDepth 2048 in
theorem row_32 : row 32 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_33 : row 33 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_34 : row 34 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_35 : row 35 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_36 : row 36 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_37 : row 37 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_38 : row 38 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_39 : row 39 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_40 : row 40 := by decide +kernel
set_option maxRecDepth 2048 in
theorem row_41 : row 41 := by decide +kernel
theorem rows (i : Fin 42) : row i := by
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
  · exact row_32
  · exact row_33
  · exact row_34
  · exact row_35
  · exact row_36
  · exact row_37
  · exact row_38
  · exact row_39
  · exact row_40
  · exact row_41
theorem involution_cover : ∀ i : Fin 128, (treeWord i)^2 = 1 →
    i = 0 ∨ i = 15 ∨ ∃ j, actors j = i := by decide +kernel

theorem central_cover : ∀ i : Fin 128, i = 0 ∨ i = 15 →
    ∃ k : Fin 4, coreRepresentation (Fin 8) (treeWord i) (pair 0 2) =
      (![pair 0 2, pair 1 3, pair 0 2, pair 1 3] : Fin 4 → C) k := by decide +kernel

theorem central_moved :
    (coreRepresentation (Fin 8) (treeWord 15) (pair 0 2) - pair 0 2).val ≠ 0 ∧
    (coreRepresentation (Fin 8) (treeWord 15) (pair 0 2) - pair 0 2).val ≠ allOne (Fin 8) := by
  decide +kernel
end BinaryPermutation.EightRigidityCertificate
