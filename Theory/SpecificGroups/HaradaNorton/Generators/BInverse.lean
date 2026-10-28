module

public import Theory.SpecificGroups.HaradaNorton.Generators.SparseRows
import Mathlib.Tactic.FinCases

/-!
# Harada–Norton BInverse certificate

Each row support and each restricted product is checked by kernel reduction.
The row equalities assemble to the full matrix identity. These checks use the
original ATLAS entries, with no assumption about invertibility.
Source and attribution: `../MatrixSources.md`.
-/

namespace HaradaNorton

set_option maxRecDepth 10000

private instance rowDecidable (A B : Matrix133) (i : Fin 133) :
    Decidable (∀ j, A i j = B i j) :=
  @Nat.decidableForallFin 133 _ (fun j => ZMod.decidableEq 5 (A i j) (B i j))

set_option maxHeartbeats 0 in
private theorem row_0 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 0 j = (1 : Matrix133) 0 j := by
  have hs : ∀ k : Fin 133, k ∉ ({1} : Finset (Fin 133)) →
      bMatrix 0 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({1} : Finset (Fin 133)), bMatrix 0 k * bInvMatrix k j) =
        (1 : Matrix133) 0 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 0 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_1 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 1 j = (1 : Matrix133) 1 j := by
  have hs : ∀ k : Fin 133, k ∉ ({3} : Finset (Fin 133)) →
      bMatrix 1 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({3} : Finset (Fin 133)), bMatrix 1 k * bInvMatrix k j) =
        (1 : Matrix133) 1 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 1 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_2 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 2 j = (1 : Matrix133) 2 j := by
  have hs : ∀ k : Fin 133, k ∉ ({4} : Finset (Fin 133)) →
      bMatrix 2 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({4} : Finset (Fin 133)), bMatrix 2 k * bInvMatrix k j) =
        (1 : Matrix133) 2 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 2 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_3 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 3 j = (1 : Matrix133) 3 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0} : Finset (Fin 133)) →
      bMatrix 3 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0} : Finset (Fin 133)), bMatrix 3 k * bInvMatrix k j) =
        (1 : Matrix133) 3 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 3 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_4 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 4 j = (1 : Matrix133) 4 j := by
  have hs : ∀ k : Fin 133, k ∉ ({7} : Finset (Fin 133)) →
      bMatrix 4 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({7} : Finset (Fin 133)), bMatrix 4 k * bInvMatrix k j) =
        (1 : Matrix133) 4 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 4 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_5 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 5 j = (1 : Matrix133) 5 j := by
  have hs : ∀ k : Fin 133, k ∉ ({8} : Finset (Fin 133)) →
      bMatrix 5 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({8} : Finset (Fin 133)), bMatrix 5 k * bInvMatrix k j) =
        (1 : Matrix133) 5 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 5 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_6 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 6 j = (1 : Matrix133) 6 j := by
  have hs : ∀ k : Fin 133, k ∉ ({9} : Finset (Fin 133)) →
      bMatrix 6 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({9} : Finset (Fin 133)), bMatrix 6 k * bInvMatrix k j) =
        (1 : Matrix133) 6 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 6 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_7 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 7 j = (1 : Matrix133) 7 j := by
  have hs : ∀ k : Fin 133, k ∉ ({2} : Finset (Fin 133)) →
      bMatrix 7 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({2} : Finset (Fin 133)), bMatrix 7 k * bInvMatrix k j) =
        (1 : Matrix133) 7 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 7 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_8 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 8 j = (1 : Matrix133) 8 j := by
  have hs : ∀ k : Fin 133, k ∉ ({12} : Finset (Fin 133)) →
      bMatrix 8 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({12} : Finset (Fin 133)), bMatrix 8 k * bInvMatrix k j) =
        (1 : Matrix133) 8 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 8 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_9 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 9 j = (1 : Matrix133) 9 j := by
  have hs : ∀ k : Fin 133, k ∉ ({14} : Finset (Fin 133)) →
      bMatrix 9 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({14} : Finset (Fin 133)), bMatrix 9 k * bInvMatrix k j) =
        (1 : Matrix133) 9 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 9 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_10 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 10 j = (1 : Matrix133) 10 j := by
  have hs : ∀ k : Fin 133, k ∉ ({15} : Finset (Fin 133)) →
      bMatrix 10 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({15} : Finset (Fin 133)), bMatrix 10 k * bInvMatrix k j) =
        (1 : Matrix133) 10 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 10 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_11 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 11 j = (1 : Matrix133) 11 j := by
  have hs : ∀ k : Fin 133, k ∉ ({16} : Finset (Fin 133)) →
      bMatrix 11 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({16} : Finset (Fin 133)), bMatrix 11 k * bInvMatrix k j) =
        (1 : Matrix133) 11 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 11 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_12 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 12 j = (1 : Matrix133) 12 j := by
  have hs : ∀ k : Fin 133, k ∉ ({5} : Finset (Fin 133)) →
      bMatrix 12 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({5} : Finset (Fin 133)), bMatrix 12 k * bInvMatrix k j) =
        (1 : Matrix133) 12 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 12 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_13 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 13 j = (1 : Matrix133) 13 j := by
  have hs : ∀ k : Fin 133, k ∉ ({18} : Finset (Fin 133)) →
      bMatrix 13 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({18} : Finset (Fin 133)), bMatrix 13 k * bInvMatrix k j) =
        (1 : Matrix133) 13 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 13 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_14 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 14 j = (1 : Matrix133) 14 j := by
  have hs : ∀ k : Fin 133, k ∉ ({6} : Finset (Fin 133)) →
      bMatrix 14 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({6} : Finset (Fin 133)), bMatrix 14 k * bInvMatrix k j) =
        (1 : Matrix133) 14 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 14 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_15 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 15 j = (1 : Matrix133) 15 j := by
  have hs : ∀ k : Fin 133, k ∉ ({21} : Finset (Fin 133)) →
      bMatrix 15 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({21} : Finset (Fin 133)), bMatrix 15 k * bInvMatrix k j) =
        (1 : Matrix133) 15 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 15 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_16 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 16 j = (1 : Matrix133) 16 j := by
  have hs : ∀ k : Fin 133, k ∉ ({23} : Finset (Fin 133)) →
      bMatrix 16 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({23} : Finset (Fin 133)), bMatrix 16 k * bInvMatrix k j) =
        (1 : Matrix133) 16 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 16 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_17 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 17 j = (1 : Matrix133) 17 j := by
  have hs : ∀ k : Fin 133, k ∉ ({24} : Finset (Fin 133)) →
      bMatrix 17 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({24} : Finset (Fin 133)), bMatrix 17 k * bInvMatrix k j) =
        (1 : Matrix133) 17 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 17 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_18 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 18 j = (1 : Matrix133) 18 j := by
  have hs : ∀ k : Fin 133, k ∉ ({26} : Finset (Fin 133)) →
      bMatrix 18 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({26} : Finset (Fin 133)), bMatrix 18 k * bInvMatrix k j) =
        (1 : Matrix133) 18 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 18 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_19 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 19 j = (1 : Matrix133) 19 j := by
  have hs : ∀ k : Fin 133, k ∉ ({27} : Finset (Fin 133)) →
      bMatrix 19 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({27} : Finset (Fin 133)), bMatrix 19 k * bInvMatrix k j) =
        (1 : Matrix133) 19 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 19 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_20 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 20 j = (1 : Matrix133) 20 j := by
  have hs : ∀ k : Fin 133, k ∉ ({28} : Finset (Fin 133)) →
      bMatrix 20 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({28} : Finset (Fin 133)), bMatrix 20 k * bInvMatrix k j) =
        (1 : Matrix133) 20 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 20 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_21 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 21 j = (1 : Matrix133) 21 j := by
  have hs : ∀ k : Fin 133, k ∉ ({10} : Finset (Fin 133)) →
      bMatrix 21 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({10} : Finset (Fin 133)), bMatrix 21 k * bInvMatrix k j) =
        (1 : Matrix133) 21 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 21 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_22 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 22 j = (1 : Matrix133) 22 j := by
  have hs : ∀ k : Fin 133, k ∉ ({30} : Finset (Fin 133)) →
      bMatrix 22 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({30} : Finset (Fin 133)), bMatrix 22 k * bInvMatrix k j) =
        (1 : Matrix133) 22 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 22 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_23 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 23 j = (1 : Matrix133) 23 j := by
  have hs : ∀ k : Fin 133, k ∉ ({11} : Finset (Fin 133)) →
      bMatrix 23 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({11} : Finset (Fin 133)), bMatrix 23 k * bInvMatrix k j) =
        (1 : Matrix133) 23 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 23 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_24 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 24 j = (1 : Matrix133) 24 j := by
  have hs : ∀ k : Fin 133, k ∉ ({33} : Finset (Fin 133)) →
      bMatrix 24 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({33} : Finset (Fin 133)), bMatrix 24 k * bInvMatrix k j) =
        (1 : Matrix133) 24 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 24 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_25 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 25 j = (1 : Matrix133) 25 j := by
  have hs : ∀ k : Fin 133, k ∉ ({34} : Finset (Fin 133)) →
      bMatrix 25 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({34} : Finset (Fin 133)), bMatrix 25 k * bInvMatrix k j) =
        (1 : Matrix133) 25 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 25 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_26 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 26 j = (1 : Matrix133) 26 j := by
  have hs : ∀ k : Fin 133, k ∉ ({13} : Finset (Fin 133)) →
      bMatrix 26 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({13} : Finset (Fin 133)), bMatrix 26 k * bInvMatrix k j) =
        (1 : Matrix133) 26 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 26 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_27 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 27 j = (1 : Matrix133) 27 j := by
  have hs : ∀ k : Fin 133, k ∉ ({37} : Finset (Fin 133)) →
      bMatrix 27 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({37} : Finset (Fin 133)), bMatrix 27 k * bInvMatrix k j) =
        (1 : Matrix133) 27 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 27 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_28 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 28 j = (1 : Matrix133) 28 j := by
  have hs : ∀ k : Fin 133, k ∉ ({39} : Finset (Fin 133)) →
      bMatrix 28 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({39} : Finset (Fin 133)), bMatrix 28 k * bInvMatrix k j) =
        (1 : Matrix133) 28 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 28 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_29 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 29 j = (1 : Matrix133) 29 j := by
  have hs : ∀ k : Fin 133, k ∉ ({29} : Finset (Fin 133)) →
      bMatrix 29 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({29} : Finset (Fin 133)), bMatrix 29 k * bInvMatrix k j) =
        (1 : Matrix133) 29 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 29 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_30 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 30 j = (1 : Matrix133) 30 j := by
  have hs : ∀ k : Fin 133, k ∉ ({41} : Finset (Fin 133)) →
      bMatrix 30 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({41} : Finset (Fin 133)), bMatrix 30 k * bInvMatrix k j) =
        (1 : Matrix133) 30 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 30 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_31 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 31 j = (1 : Matrix133) 31 j := by
  have hs : ∀ k : Fin 133, k ∉ ({42} : Finset (Fin 133)) →
      bMatrix 31 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({42} : Finset (Fin 133)), bMatrix 31 k * bInvMatrix k j) =
        (1 : Matrix133) 31 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 31 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_32 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 32 j = (1 : Matrix133) 32 j := by
  have hs : ∀ k : Fin 133, k ∉ ({43} : Finset (Fin 133)) →
      bMatrix 32 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({43} : Finset (Fin 133)), bMatrix 32 k * bInvMatrix k j) =
        (1 : Matrix133) 32 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 32 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_33 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 33 j = (1 : Matrix133) 33 j := by
  have hs : ∀ k : Fin 133, k ∉ ({17} : Finset (Fin 133)) →
      bMatrix 33 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({17} : Finset (Fin 133)), bMatrix 33 k * bInvMatrix k j) =
        (1 : Matrix133) 33 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 33 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_34 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 34 j = (1 : Matrix133) 34 j := by
  have hs : ∀ k : Fin 133, k ∉ ({46} : Finset (Fin 133)) →
      bMatrix 34 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({46} : Finset (Fin 133)), bMatrix 34 k * bInvMatrix k j) =
        (1 : Matrix133) 34 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 34 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_35 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 35 j = (1 : Matrix133) 35 j := by
  have hs : ∀ k : Fin 133, k ∉ ({47} : Finset (Fin 133)) →
      bMatrix 35 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({47} : Finset (Fin 133)), bMatrix 35 k * bInvMatrix k j) =
        (1 : Matrix133) 35 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 35 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_36 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 36 j = (1 : Matrix133) 36 j := by
  have hs : ∀ k : Fin 133, k ∉ ({48} : Finset (Fin 133)) →
      bMatrix 36 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({48} : Finset (Fin 133)), bMatrix 36 k * bInvMatrix k j) =
        (1 : Matrix133) 36 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 36 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_37 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 37 j = (1 : Matrix133) 37 j := by
  have hs : ∀ k : Fin 133, k ∉ ({19} : Finset (Fin 133)) →
      bMatrix 37 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({19} : Finset (Fin 133)), bMatrix 37 k * bInvMatrix k j) =
        (1 : Matrix133) 37 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 37 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_38 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 38 j = (1 : Matrix133) 38 j := by
  have hs : ∀ k : Fin 133, k ∉ ({50} : Finset (Fin 133)) →
      bMatrix 38 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({50} : Finset (Fin 133)), bMatrix 38 k * bInvMatrix k j) =
        (1 : Matrix133) 38 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 38 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_39 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 39 j = (1 : Matrix133) 39 j := by
  have hs : ∀ k : Fin 133, k ∉ ({20} : Finset (Fin 133)) →
      bMatrix 39 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({20} : Finset (Fin 133)), bMatrix 39 k * bInvMatrix k j) =
        (1 : Matrix133) 39 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 39 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_40 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 40 j = (1 : Matrix133) 40 j := by
  have hs : ∀ k : Fin 133, k ∉ ({52} : Finset (Fin 133)) →
      bMatrix 40 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({52} : Finset (Fin 133)), bMatrix 40 k * bInvMatrix k j) =
        (1 : Matrix133) 40 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 40 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_41 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 41 j = (1 : Matrix133) 41 j := by
  have hs : ∀ k : Fin 133, k ∉ ({22} : Finset (Fin 133)) →
      bMatrix 41 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({22} : Finset (Fin 133)), bMatrix 41 k * bInvMatrix k j) =
        (1 : Matrix133) 41 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 41 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_42 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 42 j = (1 : Matrix133) 42 j := by
  have hs : ∀ k : Fin 133, k ∉ ({55} : Finset (Fin 133)) →
      bMatrix 42 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({55} : Finset (Fin 133)), bMatrix 42 k * bInvMatrix k j) =
        (1 : Matrix133) 42 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 42 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_43 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 43 j = (1 : Matrix133) 43 j := by
  have hs : ∀ k : Fin 133, k ∉ ({57} : Finset (Fin 133)) →
      bMatrix 43 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({57} : Finset (Fin 133)), bMatrix 43 k * bInvMatrix k j) =
        (1 : Matrix133) 43 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 43 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_44 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 44 j = (1 : Matrix133) 44 j := by
  have hs : ∀ k : Fin 133, k ∉ ({58} : Finset (Fin 133)) →
      bMatrix 44 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({58} : Finset (Fin 133)), bMatrix 44 k * bInvMatrix k j) =
        (1 : Matrix133) 44 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 44 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_45 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 45 j = (1 : Matrix133) 45 j := by
  have hs : ∀ k : Fin 133, k ∉ ({59} : Finset (Fin 133)) →
      bMatrix 45 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({59} : Finset (Fin 133)), bMatrix 45 k * bInvMatrix k j) =
        (1 : Matrix133) 45 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 45 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_46 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 46 j = (1 : Matrix133) 46 j := by
  have hs : ∀ k : Fin 133, k ∉ ({25} : Finset (Fin 133)) →
      bMatrix 46 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({25} : Finset (Fin 133)), bMatrix 46 k * bInvMatrix k j) =
        (1 : Matrix133) 46 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 46 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_47 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 47 j = (1 : Matrix133) 47 j := by
  have hs : ∀ k : Fin 133, k ∉ ({62} : Finset (Fin 133)) →
      bMatrix 47 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({62} : Finset (Fin 133)), bMatrix 47 k * bInvMatrix k j) =
        (1 : Matrix133) 47 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 47 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_48 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 48 j = (1 : Matrix133) 48 j := by
  have hs : ∀ k : Fin 133, k ∉ ({64} : Finset (Fin 133)) →
      bMatrix 48 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({64} : Finset (Fin 133)), bMatrix 48 k * bInvMatrix k j) =
        (1 : Matrix133) 48 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 48 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_49 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 49 j = (1 : Matrix133) 49 j := by
  have hs : ∀ k : Fin 133, k ∉ ({65} : Finset (Fin 133)) →
      bMatrix 49 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({65} : Finset (Fin 133)), bMatrix 49 k * bInvMatrix k j) =
        (1 : Matrix133) 49 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 49 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_50 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 50 j = (1 : Matrix133) 50 j := by
  have hs : ∀ k : Fin 133, k ∉ ({67} : Finset (Fin 133)) →
      bMatrix 50 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({67} : Finset (Fin 133)), bMatrix 50 k * bInvMatrix k j) =
        (1 : Matrix133) 50 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 50 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_51 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 51 j = (1 : Matrix133) 51 j := by
  have hs : ∀ k : Fin 133, k ∉ ({68} : Finset (Fin 133)) →
      bMatrix 51 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({68} : Finset (Fin 133)), bMatrix 51 k * bInvMatrix k j) =
        (1 : Matrix133) 51 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 51 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_52 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 52 j = (1 : Matrix133) 52 j := by
  have hs : ∀ k : Fin 133, k ∉ ({70} : Finset (Fin 133)) →
      bMatrix 52 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({70} : Finset (Fin 133)), bMatrix 52 k * bInvMatrix k j) =
        (1 : Matrix133) 52 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 52 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_53 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 53 j = (1 : Matrix133) 53 j := by
  have hs : ∀ k : Fin 133, k ∉ ({71} : Finset (Fin 133)) →
      bMatrix 53 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({71} : Finset (Fin 133)), bMatrix 53 k * bInvMatrix k j) =
        (1 : Matrix133) 53 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 53 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_54 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 54 j = (1 : Matrix133) 54 j := by
  have hs : ∀ k : Fin 133, k ∉ ({72} : Finset (Fin 133)) →
      bMatrix 54 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({72} : Finset (Fin 133)), bMatrix 54 k * bInvMatrix k j) =
        (1 : Matrix133) 54 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 54 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_55 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 55 j = (1 : Matrix133) 55 j := by
  have hs : ∀ k : Fin 133, k ∉ ({31} : Finset (Fin 133)) →
      bMatrix 55 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({31} : Finset (Fin 133)), bMatrix 55 k * bInvMatrix k j) =
        (1 : Matrix133) 55 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 55 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_56 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 56 j = (1 : Matrix133) 56 j := by
  have hs : ∀ k : Fin 133, k ∉ ({74} : Finset (Fin 133)) →
      bMatrix 56 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({74} : Finset (Fin 133)), bMatrix 56 k * bInvMatrix k j) =
        (1 : Matrix133) 56 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 56 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_57 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 57 j = (1 : Matrix133) 57 j := by
  have hs : ∀ k : Fin 133, k ∉ ({32} : Finset (Fin 133)) →
      bMatrix 57 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({32} : Finset (Fin 133)), bMatrix 57 k * bInvMatrix k j) =
        (1 : Matrix133) 57 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 57 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_58 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 58 j = (1 : Matrix133) 58 j := by
  have hs : ∀ k : Fin 133, k ∉ ({77} : Finset (Fin 133)) →
      bMatrix 58 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({77} : Finset (Fin 133)), bMatrix 58 k * bInvMatrix k j) =
        (1 : Matrix133) 58 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 58 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_59 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 59 j = (1 : Matrix133) 59 j := by
  have hs : ∀ k : Fin 133, k ∉ ({79} : Finset (Fin 133)) →
      bMatrix 59 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({79} : Finset (Fin 133)), bMatrix 59 k * bInvMatrix k j) =
        (1 : Matrix133) 59 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 59 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_60 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 60 j = (1 : Matrix133) 60 j := by
  have hs : ∀ k : Fin 133, k ∉ ({80} : Finset (Fin 133)) →
      bMatrix 60 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({80} : Finset (Fin 133)), bMatrix 60 k * bInvMatrix k j) =
        (1 : Matrix133) 60 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 60 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_61 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 61 j = (1 : Matrix133) 61 j := by
  have hs : ∀ k : Fin 133, k ∉ ({81} : Finset (Fin 133)) →
      bMatrix 61 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({81} : Finset (Fin 133)), bMatrix 61 k * bInvMatrix k j) =
        (1 : Matrix133) 61 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 61 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_62 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 62 j = (1 : Matrix133) 62 j := by
  have hs : ∀ k : Fin 133, k ∉ ({35} : Finset (Fin 133)) →
      bMatrix 62 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({35} : Finset (Fin 133)), bMatrix 62 k * bInvMatrix k j) =
        (1 : Matrix133) 62 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 62 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_63 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 63 j = (1 : Matrix133) 63 j := by
  have hs : ∀ k : Fin 133, k ∉ ({82} : Finset (Fin 133)) →
      bMatrix 63 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({82} : Finset (Fin 133)), bMatrix 63 k * bInvMatrix k j) =
        (1 : Matrix133) 63 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 63 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_64 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 64 j = (1 : Matrix133) 64 j := by
  have hs : ∀ k : Fin 133, k ∉ ({36} : Finset (Fin 133)) →
      bMatrix 64 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({36} : Finset (Fin 133)), bMatrix 64 k * bInvMatrix k j) =
        (1 : Matrix133) 64 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 64 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_65 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 65 j = (1 : Matrix133) 65 j := by
  have hs : ∀ k : Fin 133, k ∉ ({85} : Finset (Fin 133)) →
      bMatrix 65 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({85} : Finset (Fin 133)), bMatrix 65 k * bInvMatrix k j) =
        (1 : Matrix133) 65 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 65 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_66 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 66 j = (1 : Matrix133) 66 j := by
  have hs : ∀ k : Fin 133, k ∉ ({86} : Finset (Fin 133)) →
      bMatrix 66 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({86} : Finset (Fin 133)), bMatrix 66 k * bInvMatrix k j) =
        (1 : Matrix133) 66 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 66 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_67 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 67 j = (1 : Matrix133) 67 j := by
  have hs : ∀ k : Fin 133, k ∉ ({38} : Finset (Fin 133)) →
      bMatrix 67 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({38} : Finset (Fin 133)), bMatrix 67 k * bInvMatrix k j) =
        (1 : Matrix133) 67 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 67 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_68 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 68 j = (1 : Matrix133) 68 j := by
  have hs : ∀ k : Fin 133, k ∉ ({69} : Finset (Fin 133)) →
      bMatrix 68 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({69} : Finset (Fin 133)), bMatrix 68 k * bInvMatrix k j) =
        (1 : Matrix133) 68 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 68 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_69 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 69 j = (1 : Matrix133) 69 j := by
  have hs : ∀ k : Fin 133, k ∉ ({51} : Finset (Fin 133)) →
      bMatrix 69 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({51} : Finset (Fin 133)), bMatrix 69 k * bInvMatrix k j) =
        (1 : Matrix133) 69 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 69 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_70 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 70 j = (1 : Matrix133) 70 j := by
  have hs : ∀ k : Fin 133, k ∉ ({40} : Finset (Fin 133)) →
      bMatrix 70 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({40} : Finset (Fin 133)), bMatrix 70 k * bInvMatrix k j) =
        (1 : Matrix133) 70 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 70 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_71 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 71 j = (1 : Matrix133) 71 j := by
  have hs : ∀ k : Fin 133, k ∉ ({90} : Finset (Fin 133)) →
      bMatrix 71 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({90} : Finset (Fin 133)), bMatrix 71 k * bInvMatrix k j) =
        (1 : Matrix133) 71 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 71 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_72 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 72 j = (1 : Matrix133) 72 j := by
  have hs : ∀ k : Fin 133, k ∉ ({92} : Finset (Fin 133)) →
      bMatrix 72 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({92} : Finset (Fin 133)), bMatrix 72 k * bInvMatrix k j) =
        (1 : Matrix133) 72 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 72 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_73 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 73 j = (1 : Matrix133) 73 j := by
  have hs : ∀ k : Fin 133, k ∉ ({93} : Finset (Fin 133)) →
      bMatrix 73 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({93} : Finset (Fin 133)), bMatrix 73 k * bInvMatrix k j) =
        (1 : Matrix133) 73 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 73 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_74 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 74 j = (1 : Matrix133) 74 j := by
  have hs : ∀ k : Fin 133, k ∉ ({95} : Finset (Fin 133)) →
      bMatrix 74 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({95} : Finset (Fin 133)), bMatrix 74 k * bInvMatrix k j) =
        (1 : Matrix133) 74 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 74 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_75 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 75 j = (1 : Matrix133) 75 j := by
  have hs : ∀ k : Fin 133, k ∉ ({96} : Finset (Fin 133)) →
      bMatrix 75 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({96} : Finset (Fin 133)), bMatrix 75 k * bInvMatrix k j) =
        (1 : Matrix133) 75 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 75 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_76 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 76 j = (1 : Matrix133) 76 j := by
  have hs : ∀ k : Fin 133, k ∉ ({97} : Finset (Fin 133)) →
      bMatrix 76 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({97} : Finset (Fin 133)), bMatrix 76 k * bInvMatrix k j) =
        (1 : Matrix133) 76 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 76 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_77 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 77 j = (1 : Matrix133) 77 j := by
  have hs : ∀ k : Fin 133, k ∉ ({44} : Finset (Fin 133)) →
      bMatrix 77 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({44} : Finset (Fin 133)), bMatrix 77 k * bInvMatrix k j) =
        (1 : Matrix133) 77 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 77 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_78 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 78 j = (1 : Matrix133) 78 j := by
  have hs : ∀ k : Fin 133, k ∉ ({99} : Finset (Fin 133)) →
      bMatrix 78 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({99} : Finset (Fin 133)), bMatrix 78 k * bInvMatrix k j) =
        (1 : Matrix133) 78 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 78 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_79 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 79 j = (1 : Matrix133) 79 j := by
  have hs : ∀ k : Fin 133, k ∉ ({45} : Finset (Fin 133)) →
      bMatrix 79 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({45} : Finset (Fin 133)), bMatrix 79 k * bInvMatrix k j) =
        (1 : Matrix133) 79 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 79 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_80 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 80 j = (1 : Matrix133) 80 j := by
  have hs : ∀ k : Fin 133, k ∉ ({102} : Finset (Fin 133)) →
      bMatrix 80 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({102} : Finset (Fin 133)), bMatrix 80 k * bInvMatrix k j) =
        (1 : Matrix133) 80 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 80 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_81 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 81 j = (1 : Matrix133) 81 j := by
  have hs : ∀ k : Fin 133, k ∉ ({87} : Finset (Fin 133)) →
      bMatrix 81 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({87} : Finset (Fin 133)), bMatrix 81 k * bInvMatrix k j) =
        (1 : Matrix133) 81 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 81 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_82 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 82 j = (1 : Matrix133) 82 j := by
  have hs : ∀ k : Fin 133, k ∉ ({105} : Finset (Fin 133)) →
      bMatrix 82 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({105} : Finset (Fin 133)), bMatrix 82 k * bInvMatrix k j) =
        (1 : Matrix133) 82 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 82 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_83 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 83 j = (1 : Matrix133) 83 j := by
  have hs : ∀ k : Fin 133, k ∉ ({106} : Finset (Fin 133)) →
      bMatrix 83 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({106} : Finset (Fin 133)), bMatrix 83 k * bInvMatrix k j) =
        (1 : Matrix133) 83 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 83 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_84 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 84 j = (1 : Matrix133) 84 j := by
  have hs : ∀ k : Fin 133, k ∉ ({107} : Finset (Fin 133)) →
      bMatrix 84 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({107} : Finset (Fin 133)), bMatrix 84 k * bInvMatrix k j) =
        (1 : Matrix133) 84 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 84 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_85 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 85 j = (1 : Matrix133) 85 j := by
  have hs : ∀ k : Fin 133, k ∉ ({49} : Finset (Fin 133)) →
      bMatrix 85 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({49} : Finset (Fin 133)), bMatrix 85 k * bInvMatrix k j) =
        (1 : Matrix133) 85 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 85 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_86 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 86 j = (1 : Matrix133) 86 j := by
  have hs : ∀ k : Fin 133, k ∉ ({110} : Finset (Fin 133)) →
      bMatrix 86 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({110} : Finset (Fin 133)), bMatrix 86 k * bInvMatrix k j) =
        (1 : Matrix133) 86 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 86 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_87 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 87 j = (1 : Matrix133) 87 j := by
  have hs : ∀ k : Fin 133, k ∉ ({61} : Finset (Fin 133)) →
      bMatrix 87 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({61} : Finset (Fin 133)), bMatrix 87 k * bInvMatrix k j) =
        (1 : Matrix133) 87 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 87 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_88 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 88 j = (1 : Matrix133) 88 j := by
  have hs : ∀ k : Fin 133, k ∉ ({111} : Finset (Fin 133)) →
      bMatrix 88 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({111} : Finset (Fin 133)), bMatrix 88 k * bInvMatrix k j) =
        (1 : Matrix133) 88 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 88 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_89 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 89 j = (1 : Matrix133) 89 j := by
  have hs : ∀ k : Fin 133, k ∉ ({112} : Finset (Fin 133)) →
      bMatrix 89 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({112} : Finset (Fin 133)), bMatrix 89 k * bInvMatrix k j) =
        (1 : Matrix133) 89 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 89 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_90 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 90 j = (1 : Matrix133) 90 j := by
  have hs : ∀ k : Fin 133, k ∉ ({53} : Finset (Fin 133)) →
      bMatrix 90 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({53} : Finset (Fin 133)), bMatrix 90 k * bInvMatrix k j) =
        (1 : Matrix133) 90 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 90 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_91 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 91 j = (1 : Matrix133) 91 j := by
  have hs : ∀ k : Fin 133, k ∉ ({114} : Finset (Fin 133)) →
      bMatrix 91 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({114} : Finset (Fin 133)), bMatrix 91 k * bInvMatrix k j) =
        (1 : Matrix133) 91 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 91 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_92 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 92 j = (1 : Matrix133) 92 j := by
  have hs : ∀ k : Fin 133, k ∉ ({54} : Finset (Fin 133)) →
      bMatrix 92 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({54} : Finset (Fin 133)), bMatrix 92 k * bInvMatrix k j) =
        (1 : Matrix133) 92 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 92 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_93 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 93 j = (1 : Matrix133) 93 j := by
  have hs : ∀ k : Fin 133, k ∉ ({116} : Finset (Fin 133)) →
      bMatrix 93 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({116} : Finset (Fin 133)), bMatrix 93 k * bInvMatrix k j) =
        (1 : Matrix133) 93 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 93 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_94 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 94 j = (1 : Matrix133) 94 j := by
  have hs : ∀ k : Fin 133, k ∉ ({117} : Finset (Fin 133)) →
      bMatrix 94 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({117} : Finset (Fin 133)), bMatrix 94 k * bInvMatrix k j) =
        (1 : Matrix133) 94 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 94 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_95 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 95 j = (1 : Matrix133) 95 j := by
  have hs : ∀ k : Fin 133, k ∉ ({56} : Finset (Fin 133)) →
      bMatrix 95 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({56} : Finset (Fin 133)), bMatrix 95 k * bInvMatrix k j) =
        (1 : Matrix133) 95 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 95 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_96 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 96 j = (1 : Matrix133) 96 j := by
  have hs : ∀ k : Fin 133, k ∉ ({119} : Finset (Fin 133)) →
      bMatrix 96 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({119} : Finset (Fin 133)), bMatrix 96 k * bInvMatrix k j) =
        (1 : Matrix133) 96 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 96 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_97 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 97 j = (1 : Matrix133) 97 j := by
  have hs : ∀ k : Fin 133, k ∉ ({121} : Finset (Fin 133)) →
      bMatrix 97 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({121} : Finset (Fin 133)), bMatrix 97 k * bInvMatrix k j) =
        (1 : Matrix133) 97 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 97 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_98 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 98 j = (1 : Matrix133) 98 j := by
  have hs : ∀ k : Fin 133, k ∉ ({122} : Finset (Fin 133)) →
      bMatrix 98 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({122} : Finset (Fin 133)), bMatrix 98 k * bInvMatrix k j) =
        (1 : Matrix133) 98 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 98 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_99 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 99 j = (1 : Matrix133) 99 j := by
  have hs : ∀ k : Fin 133, k ∉ ({124} : Finset (Fin 133)) →
      bMatrix 99 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({124} : Finset (Fin 133)), bMatrix 99 k * bInvMatrix k j) =
        (1 : Matrix133) 99 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 99 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_100 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 100 j = (1 : Matrix133) 100 j := by
  have hs : ∀ k : Fin 133, k ∉ ({125} : Finset (Fin 133)) →
      bMatrix 100 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({125} : Finset (Fin 133)), bMatrix 100 k * bInvMatrix k j) =
        (1 : Matrix133) 100 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 100 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_101 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 101 j = (1 : Matrix133) 101 j := by
  have hs : ∀ k : Fin 133, k ∉ ({126} : Finset (Fin 133)) →
      bMatrix 101 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({126} : Finset (Fin 133)), bMatrix 101 k * bInvMatrix k j) =
        (1 : Matrix133) 101 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 101 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_102 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 102 j = (1 : Matrix133) 102 j := by
  have hs : ∀ k : Fin 133, k ∉ ({60} : Finset (Fin 133)) →
      bMatrix 102 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({60} : Finset (Fin 133)), bMatrix 102 k * bInvMatrix k j) =
        (1 : Matrix133) 102 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 102 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_103 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 103 j = (1 : Matrix133) 103 j := by
  have hs : ∀ k : Fin 133, k ∉ ({128} : Finset (Fin 133)) →
      bMatrix 103 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({128} : Finset (Fin 133)), bMatrix 103 k * bInvMatrix k j) =
        (1 : Matrix133) 103 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 103 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_104 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 104 j = (1 : Matrix133) 104 j := by
  have hs : ∀ k : Fin 133, k ∉ ({129} : Finset (Fin 133)) →
      bMatrix 104 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({129} : Finset (Fin 133)), bMatrix 104 k * bInvMatrix k j) =
        (1 : Matrix133) 104 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 104 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_105 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 105 j = (1 : Matrix133) 105 j := by
  have hs : ∀ k : Fin 133, k ∉ ({63} : Finset (Fin 133)) →
      bMatrix 105 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({63} : Finset (Fin 133)), bMatrix 105 k * bInvMatrix k j) =
        (1 : Matrix133) 105 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 105 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_106 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 106 j = (1 : Matrix133) 106 j := by
  have hs : ∀ k : Fin 133, k ∉ ({130} : Finset (Fin 133)) →
      bMatrix 106 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({130} : Finset (Fin 133)), bMatrix 106 k * bInvMatrix k j) =
        (1 : Matrix133) 106 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 106 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_107 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 107 j = (1 : Matrix133) 107 j := by
  have hs : ∀ k : Fin 133, k ∉ ({132} : Finset (Fin 133)) →
      bMatrix 107 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({132} : Finset (Fin 133)), bMatrix 107 k * bInvMatrix k j) =
        (1 : Matrix133) 107 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 107 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_108 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 108 j = (1 : Matrix133) 108 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 63, 64, 65, 66, 68, 69, 71, 72, 73, 74, 75, 76, 77, 79, 80, 81, 82, 84, 86, 87, 88, 91, 94, 95, 96, 97, 98, 100, 101, 102, 104, 105, 106, 107, 108, 109, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131} : Finset (Fin 133)) →
      bMatrix 108 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 63, 64, 65, 66, 68, 69, 71, 72, 73, 74, 75, 76, 77, 79, 80, 81, 82, 84, 86, 87, 88, 91, 94, 95, 96, 97, 98, 100, 101, 102, 104, 105, 106, 107, 108, 109, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131} : Finset (Fin 133)), bMatrix 108 k * bInvMatrix k j) =
        (1 : Matrix133) 108 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 108 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_109 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 109 j = (1 : Matrix133) 109 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 4, 5, 6, 8, 9, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 54, 56, 57, 58, 60, 61, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 74, 75, 77, 81, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 94, 95, 96, 97, 98, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 115, 116, 118, 119, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132} : Finset (Fin 133)) →
      bMatrix 109 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 4, 5, 6, 8, 9, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 54, 56, 57, 58, 60, 61, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 74, 75, 77, 81, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 94, 95, 96, 97, 98, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 115, 116, 118, 119, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132} : Finset (Fin 133)), bMatrix 109 k * bInvMatrix k j) =
        (1 : Matrix133) 109 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 109 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_110 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 110 j = (1 : Matrix133) 110 j := by
  have hs : ∀ k : Fin 133, k ∉ ({66} : Finset (Fin 133)) →
      bMatrix 110 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({66} : Finset (Fin 133)), bMatrix 110 k * bInvMatrix k j) =
        (1 : Matrix133) 110 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 110 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_111 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 111 j = (1 : Matrix133) 111 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 5, 6, 7, 8, 10, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 36, 37, 38, 40, 41, 42, 44, 45, 46, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 84, 85, 86, 87, 88, 89, 91, 92, 94, 95, 96, 100, 102, 104, 105, 107, 108, 110, 111, 112, 113, 114, 115, 116, 117, 119, 120, 122, 123, 124, 126, 127, 128, 131, 132} : Finset (Fin 133)) →
      bMatrix 111 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 5, 6, 7, 8, 10, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 36, 37, 38, 40, 41, 42, 44, 45, 46, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 84, 85, 86, 87, 88, 89, 91, 92, 94, 95, 96, 100, 102, 104, 105, 107, 108, 110, 111, 112, 113, 114, 115, 116, 117, 119, 120, 122, 123, 124, 126, 127, 128, 131, 132} : Finset (Fin 133)), bMatrix 111 k * bInvMatrix k j) =
        (1 : Matrix133) 111 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 111 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_112 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 112 j = (1 : Matrix133) 112 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 22, 23, 24, 25, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 61, 62, 63, 64, 65, 67, 69, 70, 71, 72, 74, 75, 77, 78, 79, 80, 81, 82, 83, 84, 86, 87, 88, 90, 92, 93, 94, 95, 96, 97, 99, 100, 101, 103, 104, 106, 107, 108, 109, 111, 112, 113, 114, 115, 116, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 131} : Finset (Fin 133)) →
      bMatrix 112 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 22, 23, 24, 25, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 61, 62, 63, 64, 65, 67, 69, 70, 71, 72, 74, 75, 77, 78, 79, 80, 81, 82, 83, 84, 86, 87, 88, 90, 92, 93, 94, 95, 96, 97, 99, 100, 101, 103, 104, 106, 107, 108, 109, 111, 112, 113, 114, 115, 116, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 131} : Finset (Fin 133)), bMatrix 112 k * bInvMatrix k j) =
        (1 : Matrix133) 112 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 112 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_113 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 113 j = (1 : Matrix133) 113 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22, 23, 25, 26, 28, 29, 30, 31, 32, 33, 34, 35, 37, 38, 40, 43, 44, 45, 46, 47, 48, 50, 51, 52, 54, 56, 57, 58, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 76, 77, 78, 79, 80, 82, 83, 85, 87, 88, 89, 90, 93, 94, 95, 96, 97, 98, 100, 101, 102, 103, 104, 106, 107, 108, 110, 112, 113, 114, 115, 116, 119, 120, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132} : Finset (Fin 133)) →
      bMatrix 113 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22, 23, 25, 26, 28, 29, 30, 31, 32, 33, 34, 35, 37, 38, 40, 43, 44, 45, 46, 47, 48, 50, 51, 52, 54, 56, 57, 58, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 76, 77, 78, 79, 80, 82, 83, 85, 87, 88, 89, 90, 93, 94, 95, 96, 97, 98, 100, 101, 102, 103, 104, 106, 107, 108, 110, 112, 113, 114, 115, 116, 119, 120, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132} : Finset (Fin 133)), bMatrix 113 k * bInvMatrix k j) =
        (1 : Matrix133) 113 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 113 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_114 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 114 j = (1 : Matrix133) 114 j := by
  have hs : ∀ k : Fin 133, k ∉ ({1, 2, 3, 4, 5, 6, 9, 10, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 35, 36, 37, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 52, 53, 54, 55, 57, 58, 60, 61, 62, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 75, 76, 78, 83, 84, 86, 87, 88, 89, 91, 92, 93, 94, 96, 97, 99, 100, 101, 102, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 118, 119, 123, 125, 126, 127, 128, 130} : Finset (Fin 133)) →
      bMatrix 114 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({1, 2, 3, 4, 5, 6, 9, 10, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 35, 36, 37, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 52, 53, 54, 55, 57, 58, 60, 61, 62, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 75, 76, 78, 83, 84, 86, 87, 88, 89, 91, 92, 93, 94, 96, 97, 99, 100, 101, 102, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 118, 119, 123, 125, 126, 127, 128, 130} : Finset (Fin 133)), bMatrix 114 k * bInvMatrix k j) =
        (1 : Matrix133) 114 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 114 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_115 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 115 j = (1 : Matrix133) 115 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 3, 5, 6, 7, 8, 10, 13, 14, 15, 16, 18, 19, 21, 22, 23, 24, 25, 26, 28, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 44, 47, 48, 49, 50, 53, 54, 55, 57, 58, 60, 61, 62, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 80, 82, 83, 84, 85, 86, 87, 88, 90, 91, 92, 93, 94, 95, 96, 97, 102, 103, 104, 105, 106, 107, 110, 111, 113, 114, 115, 116, 117, 118, 119, 120, 121, 123, 124, 125, 126, 127, 132} : Finset (Fin 133)) →
      bMatrix 115 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 3, 5, 6, 7, 8, 10, 13, 14, 15, 16, 18, 19, 21, 22, 23, 24, 25, 26, 28, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 44, 47, 48, 49, 50, 53, 54, 55, 57, 58, 60, 61, 62, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 80, 82, 83, 84, 85, 86, 87, 88, 90, 91, 92, 93, 94, 95, 96, 97, 102, 103, 104, 105, 106, 107, 110, 111, 113, 114, 115, 116, 117, 118, 119, 120, 121, 123, 124, 125, 126, 127, 132} : Finset (Fin 133)), bMatrix 115 k * bInvMatrix k j) =
        (1 : Matrix133) 115 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 115 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_116 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 116 j = (1 : Matrix133) 116 j := by
  have hs : ∀ k : Fin 133, k ∉ ({73} : Finset (Fin 133)) →
      bMatrix 116 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({73} : Finset (Fin 133)), bMatrix 116 k * bInvMatrix k j) =
        (1 : Matrix133) 116 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 116 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_117 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 117 j = (1 : Matrix133) 117 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 23, 25, 26, 28, 31, 32, 33, 34, 35, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 52, 53, 54, 55, 56, 58, 59, 60, 61, 62, 63, 64, 67, 68, 69, 71, 72, 73, 74, 75, 77, 78, 79, 80, 82, 83, 84, 85, 88, 90, 91, 92, 93, 94, 95, 96, 98, 99, 100, 101, 103, 105, 106, 108, 110, 112, 113, 115, 116, 117, 119, 120, 122, 123, 124, 125, 126, 127, 130, 131, 132} : Finset (Fin 133)) →
      bMatrix 117 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 23, 25, 26, 28, 31, 32, 33, 34, 35, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 52, 53, 54, 55, 56, 58, 59, 60, 61, 62, 63, 64, 67, 68, 69, 71, 72, 73, 74, 75, 77, 78, 79, 80, 82, 83, 84, 85, 88, 90, 91, 92, 93, 94, 95, 96, 98, 99, 100, 101, 103, 105, 106, 108, 110, 112, 113, 115, 116, 117, 119, 120, 122, 123, 124, 125, 126, 127, 130, 131, 132} : Finset (Fin 133)), bMatrix 117 k * bInvMatrix k j) =
        (1 : Matrix133) 117 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 117 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_118 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 118 j = (1 : Matrix133) 118 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 51, 52, 53, 54, 56, 58, 59, 60, 62, 63, 65, 66, 67, 68, 69, 71, 73, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 97, 98, 99, 100, 101, 103, 105, 107, 108, 111, 112, 113, 114, 115, 116, 117, 118, 119, 122, 123, 124, 125, 126, 127, 128, 130, 131} : Finset (Fin 133)) →
      bMatrix 118 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 51, 52, 53, 54, 56, 58, 59, 60, 62, 63, 65, 66, 67, 68, 69, 71, 73, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 97, 98, 99, 100, 101, 103, 105, 107, 108, 111, 112, 113, 114, 115, 116, 117, 118, 119, 122, 123, 124, 125, 126, 127, 128, 130, 131} : Finset (Fin 133)), bMatrix 118 k * bInvMatrix k j) =
        (1 : Matrix133) 118 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 118 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_119 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 119 j = (1 : Matrix133) 119 j := by
  have hs : ∀ k : Fin 133, k ∉ ({75} : Finset (Fin 133)) →
      bMatrix 119 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({75} : Finset (Fin 133)), bMatrix 119 k * bInvMatrix k j) =
        (1 : Matrix133) 119 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 119 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_120 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 120 j = (1 : Matrix133) 120 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 19, 21, 23, 24, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 37, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 58, 59, 60, 63, 64, 65, 66, 67, 68, 69, 72, 73, 74, 75, 77, 79, 81, 82, 83, 84, 85, 86, 87, 89, 90, 91, 92, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 108, 109, 110, 111, 112, 113, 114, 115, 116, 118, 119, 120, 122, 123, 124, 127, 129, 130, 131} : Finset (Fin 133)) →
      bMatrix 120 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 19, 21, 23, 24, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 37, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 58, 59, 60, 63, 64, 65, 66, 67, 68, 69, 72, 73, 74, 75, 77, 79, 81, 82, 83, 84, 85, 86, 87, 89, 90, 91, 92, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 108, 109, 110, 111, 112, 113, 114, 115, 116, 118, 119, 120, 122, 123, 124, 127, 129, 130, 131} : Finset (Fin 133)), bMatrix 120 k * bInvMatrix k j) =
        (1 : Matrix133) 120 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 120 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_121 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 121 j = (1 : Matrix133) 121 j := by
  have hs : ∀ k : Fin 133, k ∉ ({76} : Finset (Fin 133)) →
      bMatrix 121 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({76} : Finset (Fin 133)), bMatrix 121 k * bInvMatrix k j) =
        (1 : Matrix133) 121 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 121 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_122 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 122 j = (1 : Matrix133) 122 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 4, 5, 6, 7, 10, 12, 14, 15, 16, 18, 19, 22, 23, 24, 25, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 44, 46, 47, 49, 50, 51, 52, 53, 54, 56, 58, 59, 60, 62, 65, 66, 67, 68, 72, 73, 75, 76, 77, 79, 80, 82, 83, 85, 88, 89, 90, 91, 93, 94, 95, 96, 97, 98, 99, 100, 101, 105, 107, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 124, 126, 127, 128, 129, 130, 131, 132} : Finset (Fin 133)) →
      bMatrix 122 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 4, 5, 6, 7, 10, 12, 14, 15, 16, 18, 19, 22, 23, 24, 25, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 44, 46, 47, 49, 50, 51, 52, 53, 54, 56, 58, 59, 60, 62, 65, 66, 67, 68, 72, 73, 75, 76, 77, 79, 80, 82, 83, 85, 88, 89, 90, 91, 93, 94, 95, 96, 97, 98, 99, 100, 101, 105, 107, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 124, 126, 127, 128, 129, 130, 131, 132} : Finset (Fin 133)), bMatrix 122 k * bInvMatrix k j) =
        (1 : Matrix133) 122 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 122 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_123 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 123 j = (1 : Matrix133) 123 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 61, 63, 64, 65, 66, 68, 69, 70, 71, 73, 74, 75, 78, 80, 81, 82, 83, 84, 86, 87, 89, 90, 91, 93, 94, 96, 98, 99, 100, 102, 105, 106, 107, 108, 109, 110, 111, 112, 115, 117, 118, 119, 120, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132} : Finset (Fin 133)) →
      bMatrix 123 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 61, 63, 64, 65, 66, 68, 69, 70, 71, 73, 74, 75, 78, 80, 81, 82, 83, 84, 86, 87, 89, 90, 91, 93, 94, 96, 98, 99, 100, 102, 105, 106, 107, 108, 109, 110, 111, 112, 115, 117, 118, 119, 120, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132} : Finset (Fin 133)), bMatrix 123 k * bInvMatrix k j) =
        (1 : Matrix133) 123 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 123 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_124 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 124 j = (1 : Matrix133) 124 j := by
  have hs : ∀ k : Fin 133, k ∉ ({78} : Finset (Fin 133)) →
      bMatrix 124 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({78} : Finset (Fin 133)), bMatrix 124 k * bInvMatrix k j) =
        (1 : Matrix133) 124 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 124 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_125 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 125 j = (1 : Matrix133) 125 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 29, 31, 33, 36, 38, 39, 40, 43, 44, 45, 46, 47, 48, 49, 51, 52, 53, 56, 57, 58, 59, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 75, 76, 77, 79, 80, 81, 83, 85, 86, 87, 88, 90, 91, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 116, 117, 118, 119, 121, 122, 124, 125, 126, 127, 128, 129, 130, 132} : Finset (Fin 133)) →
      bMatrix 125 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 29, 31, 33, 36, 38, 39, 40, 43, 44, 45, 46, 47, 48, 49, 51, 52, 53, 56, 57, 58, 59, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 75, 76, 77, 79, 80, 81, 83, 85, 86, 87, 88, 90, 91, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 116, 117, 118, 119, 121, 122, 124, 125, 126, 127, 128, 129, 130, 132} : Finset (Fin 133)), bMatrix 125 k * bInvMatrix k j) =
        (1 : Matrix133) 125 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 125 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_126 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 126 j = (1 : Matrix133) 126 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 21, 22, 24, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 51, 53, 55, 56, 57, 59, 60, 61, 62, 64, 67, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 80, 83, 84, 85, 89, 92, 94, 95, 96, 97, 98, 99, 100, 102, 103, 104, 105, 106, 107, 108, 109, 112, 113, 114, 115, 116, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132} : Finset (Fin 133)) →
      bMatrix 126 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 21, 22, 24, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 51, 53, 55, 56, 57, 59, 60, 61, 62, 64, 67, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 80, 83, 84, 85, 89, 92, 94, 95, 96, 97, 98, 99, 100, 102, 103, 104, 105, 106, 107, 108, 109, 112, 113, 114, 115, 116, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132} : Finset (Fin 133)), bMatrix 126 k * bInvMatrix k j) =
        (1 : Matrix133) 126 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 126 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_127 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 127 j = (1 : Matrix133) 127 j := by
  have hs : ∀ k : Fin 133, k ∉ ({2, 3, 6, 7, 8, 9, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 52, 53, 54, 55, 56, 58, 59, 60, 61, 62, 64, 65, 67, 68, 69, 70, 71, 72, 73, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 87, 88, 91, 93, 95, 96, 97, 98, 99, 102, 103, 104, 106, 107, 108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 122, 123, 125, 126, 127, 128, 130, 132} : Finset (Fin 133)) →
      bMatrix 127 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({2, 3, 6, 7, 8, 9, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 52, 53, 54, 55, 56, 58, 59, 60, 61, 62, 64, 65, 67, 68, 69, 70, 71, 72, 73, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 87, 88, 91, 93, 95, 96, 97, 98, 99, 102, 103, 104, 106, 107, 108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 122, 123, 125, 126, 127, 128, 130, 132} : Finset (Fin 133)), bMatrix 127 k * bInvMatrix k j) =
        (1 : Matrix133) 127 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 127 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_128 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 128 j = (1 : Matrix133) 128 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 52, 54, 55, 56, 58, 59, 60, 61, 62, 64, 65, 67, 68, 69, 70, 71, 72, 73, 74, 76, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 94, 95, 96, 97, 98, 99, 100, 101, 102, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131} : Finset (Fin 133)) →
      bMatrix 128 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 52, 54, 55, 56, 58, 59, 60, 61, 62, 64, 65, 67, 68, 69, 70, 71, 72, 73, 74, 76, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 94, 95, 96, 97, 98, 99, 100, 101, 102, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131} : Finset (Fin 133)), bMatrix 128 k * bInvMatrix k j) =
        (1 : Matrix133) 128 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 128 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_129 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 129 j = (1 : Matrix133) 129 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 2, 3, 4, 5, 7, 8, 9, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 31, 32, 33, 35, 36, 37, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 53, 55, 56, 57, 58, 59, 60, 62, 64, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 85, 86, 88, 89, 90, 92, 93, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 113, 115, 116, 117, 118, 119, 120, 122, 123, 124, 125, 128, 131, 132} : Finset (Fin 133)) →
      bMatrix 129 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 2, 3, 4, 5, 7, 8, 9, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 31, 32, 33, 35, 36, 37, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 53, 55, 56, 57, 58, 59, 60, 62, 64, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 85, 86, 88, 89, 90, 92, 93, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 113, 115, 116, 117, 118, 119, 120, 122, 123, 124, 125, 128, 131, 132} : Finset (Fin 133)), bMatrix 129 k * bInvMatrix k j) =
        (1 : Matrix133) 129 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 129 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_130 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 130 j = (1 : Matrix133) 130 j := by
  have hs : ∀ k : Fin 133, k ∉ ({83} : Finset (Fin 133)) →
      bMatrix 130 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({83} : Finset (Fin 133)), bMatrix 130 k * bInvMatrix k j) =
        (1 : Matrix133) 130 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 130 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_131 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 131 j = (1 : Matrix133) 131 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 28, 29, 30, 31, 32, 33, 35, 36, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 58, 60, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 76, 78, 79, 80, 81, 82, 83, 86, 87, 88, 89, 92, 94, 95, 96, 97, 98, 102, 103, 104, 106, 107, 108, 109, 113, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 127, 128, 129} : Finset (Fin 133)) →
      bMatrix 131 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 28, 29, 30, 31, 32, 33, 35, 36, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 58, 60, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 76, 78, 79, 80, 81, 82, 83, 86, 87, 88, 89, 92, 94, 95, 96, 97, 98, 102, 103, 104, 106, 107, 108, 109, 113, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 127, 128, 129} : Finset (Fin 133)), bMatrix 131 k * bInvMatrix k j) =
        (1 : Matrix133) 131 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 131 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_132 : ∀ j : Fin 133,
    (bMatrix * bInvMatrix) 132 j = (1 : Matrix133) 132 j := by
  have hs : ∀ k : Fin 133, k ∉ ({84} : Finset (Fin 133)) →
      bMatrix 132 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({84} : Finset (Fin 133)), bMatrix 132 k * bInvMatrix k j) =
        (1 : Matrix133) 132 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bInvMatrix 132 _ hs j).trans (hv j)

/-- The kernel-certified BInverse identity for the ATLAS matrices. -/
public theorem bMatrix_mul_inv : bMatrix * bInvMatrix = (1 : Matrix133) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact row_0 j
  · exact row_1 j
  · exact row_2 j
  · exact row_3 j
  · exact row_4 j
  · exact row_5 j
  · exact row_6 j
  · exact row_7 j
  · exact row_8 j
  · exact row_9 j
  · exact row_10 j
  · exact row_11 j
  · exact row_12 j
  · exact row_13 j
  · exact row_14 j
  · exact row_15 j
  · exact row_16 j
  · exact row_17 j
  · exact row_18 j
  · exact row_19 j
  · exact row_20 j
  · exact row_21 j
  · exact row_22 j
  · exact row_23 j
  · exact row_24 j
  · exact row_25 j
  · exact row_26 j
  · exact row_27 j
  · exact row_28 j
  · exact row_29 j
  · exact row_30 j
  · exact row_31 j
  · exact row_32 j
  · exact row_33 j
  · exact row_34 j
  · exact row_35 j
  · exact row_36 j
  · exact row_37 j
  · exact row_38 j
  · exact row_39 j
  · exact row_40 j
  · exact row_41 j
  · exact row_42 j
  · exact row_43 j
  · exact row_44 j
  · exact row_45 j
  · exact row_46 j
  · exact row_47 j
  · exact row_48 j
  · exact row_49 j
  · exact row_50 j
  · exact row_51 j
  · exact row_52 j
  · exact row_53 j
  · exact row_54 j
  · exact row_55 j
  · exact row_56 j
  · exact row_57 j
  · exact row_58 j
  · exact row_59 j
  · exact row_60 j
  · exact row_61 j
  · exact row_62 j
  · exact row_63 j
  · exact row_64 j
  · exact row_65 j
  · exact row_66 j
  · exact row_67 j
  · exact row_68 j
  · exact row_69 j
  · exact row_70 j
  · exact row_71 j
  · exact row_72 j
  · exact row_73 j
  · exact row_74 j
  · exact row_75 j
  · exact row_76 j
  · exact row_77 j
  · exact row_78 j
  · exact row_79 j
  · exact row_80 j
  · exact row_81 j
  · exact row_82 j
  · exact row_83 j
  · exact row_84 j
  · exact row_85 j
  · exact row_86 j
  · exact row_87 j
  · exact row_88 j
  · exact row_89 j
  · exact row_90 j
  · exact row_91 j
  · exact row_92 j
  · exact row_93 j
  · exact row_94 j
  · exact row_95 j
  · exact row_96 j
  · exact row_97 j
  · exact row_98 j
  · exact row_99 j
  · exact row_100 j
  · exact row_101 j
  · exact row_102 j
  · exact row_103 j
  · exact row_104 j
  · exact row_105 j
  · exact row_106 j
  · exact row_107 j
  · exact row_108 j
  · exact row_109 j
  · exact row_110 j
  · exact row_111 j
  · exact row_112 j
  · exact row_113 j
  · exact row_114 j
  · exact row_115 j
  · exact row_116 j
  · exact row_117 j
  · exact row_118 j
  · exact row_119 j
  · exact row_120 j
  · exact row_121 j
  · exact row_122 j
  · exact row_123 j
  · exact row_124 j
  · exact row_125 j
  · exact row_126 j
  · exact row_127 j
  · exact row_128 j
  · exact row_129 j
  · exact row_130 j
  · exact row_131 j
  · exact row_132 j

end HaradaNorton
