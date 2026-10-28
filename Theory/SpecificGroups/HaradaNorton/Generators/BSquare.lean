module

public import Theory.SpecificGroups.HaradaNorton.Generators.SparseRows
import Mathlib.Tactic.FinCases

/-!
# Harada–Norton BSquare certificate

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
    (bMatrix * bMatrix) 0 j = bInvMatrix 0 j := by
  have hs : ∀ k : Fin 133, k ∉ ({1} : Finset (Fin 133)) →
      bMatrix 0 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({1} : Finset (Fin 133)), bMatrix 0 k * bMatrix k j) =
        bInvMatrix 0 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 0 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_1 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 1 j = bInvMatrix 1 j := by
  have hs : ∀ k : Fin 133, k ∉ ({3} : Finset (Fin 133)) →
      bMatrix 1 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({3} : Finset (Fin 133)), bMatrix 1 k * bMatrix k j) =
        bInvMatrix 1 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 1 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_2 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 2 j = bInvMatrix 2 j := by
  have hs : ∀ k : Fin 133, k ∉ ({4} : Finset (Fin 133)) →
      bMatrix 2 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({4} : Finset (Fin 133)), bMatrix 2 k * bMatrix k j) =
        bInvMatrix 2 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 2 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_3 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 3 j = bInvMatrix 3 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0} : Finset (Fin 133)) →
      bMatrix 3 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0} : Finset (Fin 133)), bMatrix 3 k * bMatrix k j) =
        bInvMatrix 3 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 3 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_4 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 4 j = bInvMatrix 4 j := by
  have hs : ∀ k : Fin 133, k ∉ ({7} : Finset (Fin 133)) →
      bMatrix 4 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({7} : Finset (Fin 133)), bMatrix 4 k * bMatrix k j) =
        bInvMatrix 4 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 4 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_5 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 5 j = bInvMatrix 5 j := by
  have hs : ∀ k : Fin 133, k ∉ ({8} : Finset (Fin 133)) →
      bMatrix 5 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({8} : Finset (Fin 133)), bMatrix 5 k * bMatrix k j) =
        bInvMatrix 5 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 5 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_6 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 6 j = bInvMatrix 6 j := by
  have hs : ∀ k : Fin 133, k ∉ ({9} : Finset (Fin 133)) →
      bMatrix 6 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({9} : Finset (Fin 133)), bMatrix 6 k * bMatrix k j) =
        bInvMatrix 6 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 6 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_7 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 7 j = bInvMatrix 7 j := by
  have hs : ∀ k : Fin 133, k ∉ ({2} : Finset (Fin 133)) →
      bMatrix 7 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({2} : Finset (Fin 133)), bMatrix 7 k * bMatrix k j) =
        bInvMatrix 7 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 7 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_8 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 8 j = bInvMatrix 8 j := by
  have hs : ∀ k : Fin 133, k ∉ ({12} : Finset (Fin 133)) →
      bMatrix 8 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({12} : Finset (Fin 133)), bMatrix 8 k * bMatrix k j) =
        bInvMatrix 8 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 8 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_9 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 9 j = bInvMatrix 9 j := by
  have hs : ∀ k : Fin 133, k ∉ ({14} : Finset (Fin 133)) →
      bMatrix 9 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({14} : Finset (Fin 133)), bMatrix 9 k * bMatrix k j) =
        bInvMatrix 9 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 9 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_10 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 10 j = bInvMatrix 10 j := by
  have hs : ∀ k : Fin 133, k ∉ ({15} : Finset (Fin 133)) →
      bMatrix 10 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({15} : Finset (Fin 133)), bMatrix 10 k * bMatrix k j) =
        bInvMatrix 10 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 10 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_11 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 11 j = bInvMatrix 11 j := by
  have hs : ∀ k : Fin 133, k ∉ ({16} : Finset (Fin 133)) →
      bMatrix 11 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({16} : Finset (Fin 133)), bMatrix 11 k * bMatrix k j) =
        bInvMatrix 11 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 11 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_12 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 12 j = bInvMatrix 12 j := by
  have hs : ∀ k : Fin 133, k ∉ ({5} : Finset (Fin 133)) →
      bMatrix 12 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({5} : Finset (Fin 133)), bMatrix 12 k * bMatrix k j) =
        bInvMatrix 12 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 12 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_13 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 13 j = bInvMatrix 13 j := by
  have hs : ∀ k : Fin 133, k ∉ ({18} : Finset (Fin 133)) →
      bMatrix 13 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({18} : Finset (Fin 133)), bMatrix 13 k * bMatrix k j) =
        bInvMatrix 13 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 13 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_14 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 14 j = bInvMatrix 14 j := by
  have hs : ∀ k : Fin 133, k ∉ ({6} : Finset (Fin 133)) →
      bMatrix 14 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({6} : Finset (Fin 133)), bMatrix 14 k * bMatrix k j) =
        bInvMatrix 14 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 14 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_15 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 15 j = bInvMatrix 15 j := by
  have hs : ∀ k : Fin 133, k ∉ ({21} : Finset (Fin 133)) →
      bMatrix 15 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({21} : Finset (Fin 133)), bMatrix 15 k * bMatrix k j) =
        bInvMatrix 15 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 15 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_16 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 16 j = bInvMatrix 16 j := by
  have hs : ∀ k : Fin 133, k ∉ ({23} : Finset (Fin 133)) →
      bMatrix 16 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({23} : Finset (Fin 133)), bMatrix 16 k * bMatrix k j) =
        bInvMatrix 16 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 16 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_17 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 17 j = bInvMatrix 17 j := by
  have hs : ∀ k : Fin 133, k ∉ ({24} : Finset (Fin 133)) →
      bMatrix 17 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({24} : Finset (Fin 133)), bMatrix 17 k * bMatrix k j) =
        bInvMatrix 17 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 17 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_18 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 18 j = bInvMatrix 18 j := by
  have hs : ∀ k : Fin 133, k ∉ ({26} : Finset (Fin 133)) →
      bMatrix 18 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({26} : Finset (Fin 133)), bMatrix 18 k * bMatrix k j) =
        bInvMatrix 18 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 18 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_19 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 19 j = bInvMatrix 19 j := by
  have hs : ∀ k : Fin 133, k ∉ ({27} : Finset (Fin 133)) →
      bMatrix 19 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({27} : Finset (Fin 133)), bMatrix 19 k * bMatrix k j) =
        bInvMatrix 19 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 19 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_20 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 20 j = bInvMatrix 20 j := by
  have hs : ∀ k : Fin 133, k ∉ ({28} : Finset (Fin 133)) →
      bMatrix 20 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({28} : Finset (Fin 133)), bMatrix 20 k * bMatrix k j) =
        bInvMatrix 20 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 20 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_21 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 21 j = bInvMatrix 21 j := by
  have hs : ∀ k : Fin 133, k ∉ ({10} : Finset (Fin 133)) →
      bMatrix 21 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({10} : Finset (Fin 133)), bMatrix 21 k * bMatrix k j) =
        bInvMatrix 21 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 21 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_22 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 22 j = bInvMatrix 22 j := by
  have hs : ∀ k : Fin 133, k ∉ ({30} : Finset (Fin 133)) →
      bMatrix 22 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({30} : Finset (Fin 133)), bMatrix 22 k * bMatrix k j) =
        bInvMatrix 22 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 22 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_23 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 23 j = bInvMatrix 23 j := by
  have hs : ∀ k : Fin 133, k ∉ ({11} : Finset (Fin 133)) →
      bMatrix 23 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({11} : Finset (Fin 133)), bMatrix 23 k * bMatrix k j) =
        bInvMatrix 23 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 23 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_24 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 24 j = bInvMatrix 24 j := by
  have hs : ∀ k : Fin 133, k ∉ ({33} : Finset (Fin 133)) →
      bMatrix 24 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({33} : Finset (Fin 133)), bMatrix 24 k * bMatrix k j) =
        bInvMatrix 24 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 24 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_25 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 25 j = bInvMatrix 25 j := by
  have hs : ∀ k : Fin 133, k ∉ ({34} : Finset (Fin 133)) →
      bMatrix 25 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({34} : Finset (Fin 133)), bMatrix 25 k * bMatrix k j) =
        bInvMatrix 25 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 25 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_26 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 26 j = bInvMatrix 26 j := by
  have hs : ∀ k : Fin 133, k ∉ ({13} : Finset (Fin 133)) →
      bMatrix 26 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({13} : Finset (Fin 133)), bMatrix 26 k * bMatrix k j) =
        bInvMatrix 26 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 26 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_27 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 27 j = bInvMatrix 27 j := by
  have hs : ∀ k : Fin 133, k ∉ ({37} : Finset (Fin 133)) →
      bMatrix 27 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({37} : Finset (Fin 133)), bMatrix 27 k * bMatrix k j) =
        bInvMatrix 27 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 27 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_28 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 28 j = bInvMatrix 28 j := by
  have hs : ∀ k : Fin 133, k ∉ ({39} : Finset (Fin 133)) →
      bMatrix 28 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({39} : Finset (Fin 133)), bMatrix 28 k * bMatrix k j) =
        bInvMatrix 28 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 28 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_29 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 29 j = bInvMatrix 29 j := by
  have hs : ∀ k : Fin 133, k ∉ ({29} : Finset (Fin 133)) →
      bMatrix 29 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({29} : Finset (Fin 133)), bMatrix 29 k * bMatrix k j) =
        bInvMatrix 29 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 29 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_30 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 30 j = bInvMatrix 30 j := by
  have hs : ∀ k : Fin 133, k ∉ ({41} : Finset (Fin 133)) →
      bMatrix 30 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({41} : Finset (Fin 133)), bMatrix 30 k * bMatrix k j) =
        bInvMatrix 30 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 30 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_31 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 31 j = bInvMatrix 31 j := by
  have hs : ∀ k : Fin 133, k ∉ ({42} : Finset (Fin 133)) →
      bMatrix 31 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({42} : Finset (Fin 133)), bMatrix 31 k * bMatrix k j) =
        bInvMatrix 31 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 31 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_32 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 32 j = bInvMatrix 32 j := by
  have hs : ∀ k : Fin 133, k ∉ ({43} : Finset (Fin 133)) →
      bMatrix 32 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({43} : Finset (Fin 133)), bMatrix 32 k * bMatrix k j) =
        bInvMatrix 32 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 32 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_33 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 33 j = bInvMatrix 33 j := by
  have hs : ∀ k : Fin 133, k ∉ ({17} : Finset (Fin 133)) →
      bMatrix 33 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({17} : Finset (Fin 133)), bMatrix 33 k * bMatrix k j) =
        bInvMatrix 33 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 33 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_34 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 34 j = bInvMatrix 34 j := by
  have hs : ∀ k : Fin 133, k ∉ ({46} : Finset (Fin 133)) →
      bMatrix 34 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({46} : Finset (Fin 133)), bMatrix 34 k * bMatrix k j) =
        bInvMatrix 34 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 34 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_35 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 35 j = bInvMatrix 35 j := by
  have hs : ∀ k : Fin 133, k ∉ ({47} : Finset (Fin 133)) →
      bMatrix 35 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({47} : Finset (Fin 133)), bMatrix 35 k * bMatrix k j) =
        bInvMatrix 35 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 35 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_36 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 36 j = bInvMatrix 36 j := by
  have hs : ∀ k : Fin 133, k ∉ ({48} : Finset (Fin 133)) →
      bMatrix 36 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({48} : Finset (Fin 133)), bMatrix 36 k * bMatrix k j) =
        bInvMatrix 36 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 36 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_37 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 37 j = bInvMatrix 37 j := by
  have hs : ∀ k : Fin 133, k ∉ ({19} : Finset (Fin 133)) →
      bMatrix 37 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({19} : Finset (Fin 133)), bMatrix 37 k * bMatrix k j) =
        bInvMatrix 37 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 37 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_38 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 38 j = bInvMatrix 38 j := by
  have hs : ∀ k : Fin 133, k ∉ ({50} : Finset (Fin 133)) →
      bMatrix 38 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({50} : Finset (Fin 133)), bMatrix 38 k * bMatrix k j) =
        bInvMatrix 38 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 38 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_39 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 39 j = bInvMatrix 39 j := by
  have hs : ∀ k : Fin 133, k ∉ ({20} : Finset (Fin 133)) →
      bMatrix 39 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({20} : Finset (Fin 133)), bMatrix 39 k * bMatrix k j) =
        bInvMatrix 39 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 39 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_40 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 40 j = bInvMatrix 40 j := by
  have hs : ∀ k : Fin 133, k ∉ ({52} : Finset (Fin 133)) →
      bMatrix 40 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({52} : Finset (Fin 133)), bMatrix 40 k * bMatrix k j) =
        bInvMatrix 40 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 40 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_41 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 41 j = bInvMatrix 41 j := by
  have hs : ∀ k : Fin 133, k ∉ ({22} : Finset (Fin 133)) →
      bMatrix 41 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({22} : Finset (Fin 133)), bMatrix 41 k * bMatrix k j) =
        bInvMatrix 41 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 41 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_42 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 42 j = bInvMatrix 42 j := by
  have hs : ∀ k : Fin 133, k ∉ ({55} : Finset (Fin 133)) →
      bMatrix 42 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({55} : Finset (Fin 133)), bMatrix 42 k * bMatrix k j) =
        bInvMatrix 42 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 42 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_43 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 43 j = bInvMatrix 43 j := by
  have hs : ∀ k : Fin 133, k ∉ ({57} : Finset (Fin 133)) →
      bMatrix 43 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({57} : Finset (Fin 133)), bMatrix 43 k * bMatrix k j) =
        bInvMatrix 43 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 43 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_44 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 44 j = bInvMatrix 44 j := by
  have hs : ∀ k : Fin 133, k ∉ ({58} : Finset (Fin 133)) →
      bMatrix 44 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({58} : Finset (Fin 133)), bMatrix 44 k * bMatrix k j) =
        bInvMatrix 44 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 44 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_45 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 45 j = bInvMatrix 45 j := by
  have hs : ∀ k : Fin 133, k ∉ ({59} : Finset (Fin 133)) →
      bMatrix 45 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({59} : Finset (Fin 133)), bMatrix 45 k * bMatrix k j) =
        bInvMatrix 45 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 45 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_46 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 46 j = bInvMatrix 46 j := by
  have hs : ∀ k : Fin 133, k ∉ ({25} : Finset (Fin 133)) →
      bMatrix 46 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({25} : Finset (Fin 133)), bMatrix 46 k * bMatrix k j) =
        bInvMatrix 46 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 46 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_47 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 47 j = bInvMatrix 47 j := by
  have hs : ∀ k : Fin 133, k ∉ ({62} : Finset (Fin 133)) →
      bMatrix 47 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({62} : Finset (Fin 133)), bMatrix 47 k * bMatrix k j) =
        bInvMatrix 47 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 47 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_48 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 48 j = bInvMatrix 48 j := by
  have hs : ∀ k : Fin 133, k ∉ ({64} : Finset (Fin 133)) →
      bMatrix 48 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({64} : Finset (Fin 133)), bMatrix 48 k * bMatrix k j) =
        bInvMatrix 48 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 48 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_49 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 49 j = bInvMatrix 49 j := by
  have hs : ∀ k : Fin 133, k ∉ ({65} : Finset (Fin 133)) →
      bMatrix 49 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({65} : Finset (Fin 133)), bMatrix 49 k * bMatrix k j) =
        bInvMatrix 49 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 49 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_50 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 50 j = bInvMatrix 50 j := by
  have hs : ∀ k : Fin 133, k ∉ ({67} : Finset (Fin 133)) →
      bMatrix 50 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({67} : Finset (Fin 133)), bMatrix 50 k * bMatrix k j) =
        bInvMatrix 50 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 50 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_51 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 51 j = bInvMatrix 51 j := by
  have hs : ∀ k : Fin 133, k ∉ ({68} : Finset (Fin 133)) →
      bMatrix 51 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({68} : Finset (Fin 133)), bMatrix 51 k * bMatrix k j) =
        bInvMatrix 51 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 51 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_52 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 52 j = bInvMatrix 52 j := by
  have hs : ∀ k : Fin 133, k ∉ ({70} : Finset (Fin 133)) →
      bMatrix 52 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({70} : Finset (Fin 133)), bMatrix 52 k * bMatrix k j) =
        bInvMatrix 52 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 52 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_53 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 53 j = bInvMatrix 53 j := by
  have hs : ∀ k : Fin 133, k ∉ ({71} : Finset (Fin 133)) →
      bMatrix 53 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({71} : Finset (Fin 133)), bMatrix 53 k * bMatrix k j) =
        bInvMatrix 53 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 53 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_54 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 54 j = bInvMatrix 54 j := by
  have hs : ∀ k : Fin 133, k ∉ ({72} : Finset (Fin 133)) →
      bMatrix 54 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({72} : Finset (Fin 133)), bMatrix 54 k * bMatrix k j) =
        bInvMatrix 54 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 54 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_55 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 55 j = bInvMatrix 55 j := by
  have hs : ∀ k : Fin 133, k ∉ ({31} : Finset (Fin 133)) →
      bMatrix 55 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({31} : Finset (Fin 133)), bMatrix 55 k * bMatrix k j) =
        bInvMatrix 55 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 55 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_56 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 56 j = bInvMatrix 56 j := by
  have hs : ∀ k : Fin 133, k ∉ ({74} : Finset (Fin 133)) →
      bMatrix 56 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({74} : Finset (Fin 133)), bMatrix 56 k * bMatrix k j) =
        bInvMatrix 56 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 56 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_57 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 57 j = bInvMatrix 57 j := by
  have hs : ∀ k : Fin 133, k ∉ ({32} : Finset (Fin 133)) →
      bMatrix 57 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({32} : Finset (Fin 133)), bMatrix 57 k * bMatrix k j) =
        bInvMatrix 57 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 57 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_58 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 58 j = bInvMatrix 58 j := by
  have hs : ∀ k : Fin 133, k ∉ ({77} : Finset (Fin 133)) →
      bMatrix 58 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({77} : Finset (Fin 133)), bMatrix 58 k * bMatrix k j) =
        bInvMatrix 58 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 58 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_59 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 59 j = bInvMatrix 59 j := by
  have hs : ∀ k : Fin 133, k ∉ ({79} : Finset (Fin 133)) →
      bMatrix 59 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({79} : Finset (Fin 133)), bMatrix 59 k * bMatrix k j) =
        bInvMatrix 59 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 59 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_60 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 60 j = bInvMatrix 60 j := by
  have hs : ∀ k : Fin 133, k ∉ ({80} : Finset (Fin 133)) →
      bMatrix 60 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({80} : Finset (Fin 133)), bMatrix 60 k * bMatrix k j) =
        bInvMatrix 60 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 60 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_61 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 61 j = bInvMatrix 61 j := by
  have hs : ∀ k : Fin 133, k ∉ ({81} : Finset (Fin 133)) →
      bMatrix 61 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({81} : Finset (Fin 133)), bMatrix 61 k * bMatrix k j) =
        bInvMatrix 61 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 61 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_62 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 62 j = bInvMatrix 62 j := by
  have hs : ∀ k : Fin 133, k ∉ ({35} : Finset (Fin 133)) →
      bMatrix 62 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({35} : Finset (Fin 133)), bMatrix 62 k * bMatrix k j) =
        bInvMatrix 62 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 62 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_63 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 63 j = bInvMatrix 63 j := by
  have hs : ∀ k : Fin 133, k ∉ ({82} : Finset (Fin 133)) →
      bMatrix 63 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({82} : Finset (Fin 133)), bMatrix 63 k * bMatrix k j) =
        bInvMatrix 63 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 63 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_64 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 64 j = bInvMatrix 64 j := by
  have hs : ∀ k : Fin 133, k ∉ ({36} : Finset (Fin 133)) →
      bMatrix 64 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({36} : Finset (Fin 133)), bMatrix 64 k * bMatrix k j) =
        bInvMatrix 64 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 64 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_65 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 65 j = bInvMatrix 65 j := by
  have hs : ∀ k : Fin 133, k ∉ ({85} : Finset (Fin 133)) →
      bMatrix 65 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({85} : Finset (Fin 133)), bMatrix 65 k * bMatrix k j) =
        bInvMatrix 65 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 65 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_66 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 66 j = bInvMatrix 66 j := by
  have hs : ∀ k : Fin 133, k ∉ ({86} : Finset (Fin 133)) →
      bMatrix 66 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({86} : Finset (Fin 133)), bMatrix 66 k * bMatrix k j) =
        bInvMatrix 66 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 66 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_67 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 67 j = bInvMatrix 67 j := by
  have hs : ∀ k : Fin 133, k ∉ ({38} : Finset (Fin 133)) →
      bMatrix 67 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({38} : Finset (Fin 133)), bMatrix 67 k * bMatrix k j) =
        bInvMatrix 67 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 67 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_68 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 68 j = bInvMatrix 68 j := by
  have hs : ∀ k : Fin 133, k ∉ ({69} : Finset (Fin 133)) →
      bMatrix 68 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({69} : Finset (Fin 133)), bMatrix 68 k * bMatrix k j) =
        bInvMatrix 68 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 68 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_69 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 69 j = bInvMatrix 69 j := by
  have hs : ∀ k : Fin 133, k ∉ ({51} : Finset (Fin 133)) →
      bMatrix 69 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({51} : Finset (Fin 133)), bMatrix 69 k * bMatrix k j) =
        bInvMatrix 69 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 69 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_70 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 70 j = bInvMatrix 70 j := by
  have hs : ∀ k : Fin 133, k ∉ ({40} : Finset (Fin 133)) →
      bMatrix 70 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({40} : Finset (Fin 133)), bMatrix 70 k * bMatrix k j) =
        bInvMatrix 70 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 70 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_71 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 71 j = bInvMatrix 71 j := by
  have hs : ∀ k : Fin 133, k ∉ ({90} : Finset (Fin 133)) →
      bMatrix 71 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({90} : Finset (Fin 133)), bMatrix 71 k * bMatrix k j) =
        bInvMatrix 71 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 71 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_72 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 72 j = bInvMatrix 72 j := by
  have hs : ∀ k : Fin 133, k ∉ ({92} : Finset (Fin 133)) →
      bMatrix 72 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({92} : Finset (Fin 133)), bMatrix 72 k * bMatrix k j) =
        bInvMatrix 72 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 72 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_73 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 73 j = bInvMatrix 73 j := by
  have hs : ∀ k : Fin 133, k ∉ ({93} : Finset (Fin 133)) →
      bMatrix 73 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({93} : Finset (Fin 133)), bMatrix 73 k * bMatrix k j) =
        bInvMatrix 73 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 73 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_74 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 74 j = bInvMatrix 74 j := by
  have hs : ∀ k : Fin 133, k ∉ ({95} : Finset (Fin 133)) →
      bMatrix 74 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({95} : Finset (Fin 133)), bMatrix 74 k * bMatrix k j) =
        bInvMatrix 74 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 74 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_75 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 75 j = bInvMatrix 75 j := by
  have hs : ∀ k : Fin 133, k ∉ ({96} : Finset (Fin 133)) →
      bMatrix 75 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({96} : Finset (Fin 133)), bMatrix 75 k * bMatrix k j) =
        bInvMatrix 75 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 75 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_76 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 76 j = bInvMatrix 76 j := by
  have hs : ∀ k : Fin 133, k ∉ ({97} : Finset (Fin 133)) →
      bMatrix 76 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({97} : Finset (Fin 133)), bMatrix 76 k * bMatrix k j) =
        bInvMatrix 76 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 76 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_77 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 77 j = bInvMatrix 77 j := by
  have hs : ∀ k : Fin 133, k ∉ ({44} : Finset (Fin 133)) →
      bMatrix 77 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({44} : Finset (Fin 133)), bMatrix 77 k * bMatrix k j) =
        bInvMatrix 77 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 77 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_78 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 78 j = bInvMatrix 78 j := by
  have hs : ∀ k : Fin 133, k ∉ ({99} : Finset (Fin 133)) →
      bMatrix 78 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({99} : Finset (Fin 133)), bMatrix 78 k * bMatrix k j) =
        bInvMatrix 78 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 78 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_79 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 79 j = bInvMatrix 79 j := by
  have hs : ∀ k : Fin 133, k ∉ ({45} : Finset (Fin 133)) →
      bMatrix 79 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({45} : Finset (Fin 133)), bMatrix 79 k * bMatrix k j) =
        bInvMatrix 79 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 79 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_80 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 80 j = bInvMatrix 80 j := by
  have hs : ∀ k : Fin 133, k ∉ ({102} : Finset (Fin 133)) →
      bMatrix 80 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({102} : Finset (Fin 133)), bMatrix 80 k * bMatrix k j) =
        bInvMatrix 80 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 80 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_81 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 81 j = bInvMatrix 81 j := by
  have hs : ∀ k : Fin 133, k ∉ ({87} : Finset (Fin 133)) →
      bMatrix 81 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({87} : Finset (Fin 133)), bMatrix 81 k * bMatrix k j) =
        bInvMatrix 81 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 81 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_82 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 82 j = bInvMatrix 82 j := by
  have hs : ∀ k : Fin 133, k ∉ ({105} : Finset (Fin 133)) →
      bMatrix 82 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({105} : Finset (Fin 133)), bMatrix 82 k * bMatrix k j) =
        bInvMatrix 82 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 82 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_83 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 83 j = bInvMatrix 83 j := by
  have hs : ∀ k : Fin 133, k ∉ ({106} : Finset (Fin 133)) →
      bMatrix 83 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({106} : Finset (Fin 133)), bMatrix 83 k * bMatrix k j) =
        bInvMatrix 83 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 83 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_84 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 84 j = bInvMatrix 84 j := by
  have hs : ∀ k : Fin 133, k ∉ ({107} : Finset (Fin 133)) →
      bMatrix 84 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({107} : Finset (Fin 133)), bMatrix 84 k * bMatrix k j) =
        bInvMatrix 84 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 84 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_85 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 85 j = bInvMatrix 85 j := by
  have hs : ∀ k : Fin 133, k ∉ ({49} : Finset (Fin 133)) →
      bMatrix 85 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({49} : Finset (Fin 133)), bMatrix 85 k * bMatrix k j) =
        bInvMatrix 85 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 85 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_86 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 86 j = bInvMatrix 86 j := by
  have hs : ∀ k : Fin 133, k ∉ ({110} : Finset (Fin 133)) →
      bMatrix 86 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({110} : Finset (Fin 133)), bMatrix 86 k * bMatrix k j) =
        bInvMatrix 86 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 86 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_87 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 87 j = bInvMatrix 87 j := by
  have hs : ∀ k : Fin 133, k ∉ ({61} : Finset (Fin 133)) →
      bMatrix 87 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({61} : Finset (Fin 133)), bMatrix 87 k * bMatrix k j) =
        bInvMatrix 87 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 87 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_88 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 88 j = bInvMatrix 88 j := by
  have hs : ∀ k : Fin 133, k ∉ ({111} : Finset (Fin 133)) →
      bMatrix 88 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({111} : Finset (Fin 133)), bMatrix 88 k * bMatrix k j) =
        bInvMatrix 88 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 88 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_89 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 89 j = bInvMatrix 89 j := by
  have hs : ∀ k : Fin 133, k ∉ ({112} : Finset (Fin 133)) →
      bMatrix 89 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({112} : Finset (Fin 133)), bMatrix 89 k * bMatrix k j) =
        bInvMatrix 89 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 89 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_90 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 90 j = bInvMatrix 90 j := by
  have hs : ∀ k : Fin 133, k ∉ ({53} : Finset (Fin 133)) →
      bMatrix 90 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({53} : Finset (Fin 133)), bMatrix 90 k * bMatrix k j) =
        bInvMatrix 90 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 90 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_91 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 91 j = bInvMatrix 91 j := by
  have hs : ∀ k : Fin 133, k ∉ ({114} : Finset (Fin 133)) →
      bMatrix 91 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({114} : Finset (Fin 133)), bMatrix 91 k * bMatrix k j) =
        bInvMatrix 91 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 91 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_92 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 92 j = bInvMatrix 92 j := by
  have hs : ∀ k : Fin 133, k ∉ ({54} : Finset (Fin 133)) →
      bMatrix 92 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({54} : Finset (Fin 133)), bMatrix 92 k * bMatrix k j) =
        bInvMatrix 92 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 92 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_93 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 93 j = bInvMatrix 93 j := by
  have hs : ∀ k : Fin 133, k ∉ ({116} : Finset (Fin 133)) →
      bMatrix 93 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({116} : Finset (Fin 133)), bMatrix 93 k * bMatrix k j) =
        bInvMatrix 93 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 93 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_94 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 94 j = bInvMatrix 94 j := by
  have hs : ∀ k : Fin 133, k ∉ ({117} : Finset (Fin 133)) →
      bMatrix 94 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({117} : Finset (Fin 133)), bMatrix 94 k * bMatrix k j) =
        bInvMatrix 94 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 94 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_95 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 95 j = bInvMatrix 95 j := by
  have hs : ∀ k : Fin 133, k ∉ ({56} : Finset (Fin 133)) →
      bMatrix 95 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({56} : Finset (Fin 133)), bMatrix 95 k * bMatrix k j) =
        bInvMatrix 95 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 95 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_96 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 96 j = bInvMatrix 96 j := by
  have hs : ∀ k : Fin 133, k ∉ ({119} : Finset (Fin 133)) →
      bMatrix 96 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({119} : Finset (Fin 133)), bMatrix 96 k * bMatrix k j) =
        bInvMatrix 96 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 96 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_97 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 97 j = bInvMatrix 97 j := by
  have hs : ∀ k : Fin 133, k ∉ ({121} : Finset (Fin 133)) →
      bMatrix 97 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({121} : Finset (Fin 133)), bMatrix 97 k * bMatrix k j) =
        bInvMatrix 97 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 97 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_98 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 98 j = bInvMatrix 98 j := by
  have hs : ∀ k : Fin 133, k ∉ ({122} : Finset (Fin 133)) →
      bMatrix 98 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({122} : Finset (Fin 133)), bMatrix 98 k * bMatrix k j) =
        bInvMatrix 98 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 98 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_99 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 99 j = bInvMatrix 99 j := by
  have hs : ∀ k : Fin 133, k ∉ ({124} : Finset (Fin 133)) →
      bMatrix 99 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({124} : Finset (Fin 133)), bMatrix 99 k * bMatrix k j) =
        bInvMatrix 99 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 99 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_100 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 100 j = bInvMatrix 100 j := by
  have hs : ∀ k : Fin 133, k ∉ ({125} : Finset (Fin 133)) →
      bMatrix 100 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({125} : Finset (Fin 133)), bMatrix 100 k * bMatrix k j) =
        bInvMatrix 100 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 100 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_101 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 101 j = bInvMatrix 101 j := by
  have hs : ∀ k : Fin 133, k ∉ ({126} : Finset (Fin 133)) →
      bMatrix 101 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({126} : Finset (Fin 133)), bMatrix 101 k * bMatrix k j) =
        bInvMatrix 101 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 101 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_102 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 102 j = bInvMatrix 102 j := by
  have hs : ∀ k : Fin 133, k ∉ ({60} : Finset (Fin 133)) →
      bMatrix 102 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({60} : Finset (Fin 133)), bMatrix 102 k * bMatrix k j) =
        bInvMatrix 102 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 102 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_103 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 103 j = bInvMatrix 103 j := by
  have hs : ∀ k : Fin 133, k ∉ ({128} : Finset (Fin 133)) →
      bMatrix 103 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({128} : Finset (Fin 133)), bMatrix 103 k * bMatrix k j) =
        bInvMatrix 103 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 103 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_104 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 104 j = bInvMatrix 104 j := by
  have hs : ∀ k : Fin 133, k ∉ ({129} : Finset (Fin 133)) →
      bMatrix 104 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({129} : Finset (Fin 133)), bMatrix 104 k * bMatrix k j) =
        bInvMatrix 104 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 104 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_105 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 105 j = bInvMatrix 105 j := by
  have hs : ∀ k : Fin 133, k ∉ ({63} : Finset (Fin 133)) →
      bMatrix 105 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({63} : Finset (Fin 133)), bMatrix 105 k * bMatrix k j) =
        bInvMatrix 105 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 105 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_106 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 106 j = bInvMatrix 106 j := by
  have hs : ∀ k : Fin 133, k ∉ ({130} : Finset (Fin 133)) →
      bMatrix 106 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({130} : Finset (Fin 133)), bMatrix 106 k * bMatrix k j) =
        bInvMatrix 106 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 106 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_107 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 107 j = bInvMatrix 107 j := by
  have hs : ∀ k : Fin 133, k ∉ ({132} : Finset (Fin 133)) →
      bMatrix 107 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({132} : Finset (Fin 133)), bMatrix 107 k * bMatrix k j) =
        bInvMatrix 107 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 107 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_108 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 108 j = bInvMatrix 108 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 63, 64, 65, 66, 68, 69, 71, 72, 73, 74, 75, 76, 77, 79, 80, 81, 82, 84, 86, 87, 88, 91, 94, 95, 96, 97, 98, 100, 101, 102, 104, 105, 106, 107, 108, 109, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131} : Finset (Fin 133)) →
      bMatrix 108 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 63, 64, 65, 66, 68, 69, 71, 72, 73, 74, 75, 76, 77, 79, 80, 81, 82, 84, 86, 87, 88, 91, 94, 95, 96, 97, 98, 100, 101, 102, 104, 105, 106, 107, 108, 109, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131} : Finset (Fin 133)), bMatrix 108 k * bMatrix k j) =
        bInvMatrix 108 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 108 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_109 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 109 j = bInvMatrix 109 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 4, 5, 6, 8, 9, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 54, 56, 57, 58, 60, 61, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 74, 75, 77, 81, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 94, 95, 96, 97, 98, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 115, 116, 118, 119, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132} : Finset (Fin 133)) →
      bMatrix 109 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 4, 5, 6, 8, 9, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 54, 56, 57, 58, 60, 61, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 74, 75, 77, 81, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 94, 95, 96, 97, 98, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 115, 116, 118, 119, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132} : Finset (Fin 133)), bMatrix 109 k * bMatrix k j) =
        bInvMatrix 109 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 109 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_110 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 110 j = bInvMatrix 110 j := by
  have hs : ∀ k : Fin 133, k ∉ ({66} : Finset (Fin 133)) →
      bMatrix 110 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({66} : Finset (Fin 133)), bMatrix 110 k * bMatrix k j) =
        bInvMatrix 110 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 110 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_111 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 111 j = bInvMatrix 111 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 5, 6, 7, 8, 10, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 36, 37, 38, 40, 41, 42, 44, 45, 46, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 84, 85, 86, 87, 88, 89, 91, 92, 94, 95, 96, 100, 102, 104, 105, 107, 108, 110, 111, 112, 113, 114, 115, 116, 117, 119, 120, 122, 123, 124, 126, 127, 128, 131, 132} : Finset (Fin 133)) →
      bMatrix 111 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 5, 6, 7, 8, 10, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 36, 37, 38, 40, 41, 42, 44, 45, 46, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 84, 85, 86, 87, 88, 89, 91, 92, 94, 95, 96, 100, 102, 104, 105, 107, 108, 110, 111, 112, 113, 114, 115, 116, 117, 119, 120, 122, 123, 124, 126, 127, 128, 131, 132} : Finset (Fin 133)), bMatrix 111 k * bMatrix k j) =
        bInvMatrix 111 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 111 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_112 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 112 j = bInvMatrix 112 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 22, 23, 24, 25, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 61, 62, 63, 64, 65, 67, 69, 70, 71, 72, 74, 75, 77, 78, 79, 80, 81, 82, 83, 84, 86, 87, 88, 90, 92, 93, 94, 95, 96, 97, 99, 100, 101, 103, 104, 106, 107, 108, 109, 111, 112, 113, 114, 115, 116, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 131} : Finset (Fin 133)) →
      bMatrix 112 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 22, 23, 24, 25, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 61, 62, 63, 64, 65, 67, 69, 70, 71, 72, 74, 75, 77, 78, 79, 80, 81, 82, 83, 84, 86, 87, 88, 90, 92, 93, 94, 95, 96, 97, 99, 100, 101, 103, 104, 106, 107, 108, 109, 111, 112, 113, 114, 115, 116, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 131} : Finset (Fin 133)), bMatrix 112 k * bMatrix k j) =
        bInvMatrix 112 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 112 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_113 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 113 j = bInvMatrix 113 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22, 23, 25, 26, 28, 29, 30, 31, 32, 33, 34, 35, 37, 38, 40, 43, 44, 45, 46, 47, 48, 50, 51, 52, 54, 56, 57, 58, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 76, 77, 78, 79, 80, 82, 83, 85, 87, 88, 89, 90, 93, 94, 95, 96, 97, 98, 100, 101, 102, 103, 104, 106, 107, 108, 110, 112, 113, 114, 115, 116, 119, 120, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132} : Finset (Fin 133)) →
      bMatrix 113 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22, 23, 25, 26, 28, 29, 30, 31, 32, 33, 34, 35, 37, 38, 40, 43, 44, 45, 46, 47, 48, 50, 51, 52, 54, 56, 57, 58, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 76, 77, 78, 79, 80, 82, 83, 85, 87, 88, 89, 90, 93, 94, 95, 96, 97, 98, 100, 101, 102, 103, 104, 106, 107, 108, 110, 112, 113, 114, 115, 116, 119, 120, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132} : Finset (Fin 133)), bMatrix 113 k * bMatrix k j) =
        bInvMatrix 113 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 113 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_114 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 114 j = bInvMatrix 114 j := by
  have hs : ∀ k : Fin 133, k ∉ ({1, 2, 3, 4, 5, 6, 9, 10, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 35, 36, 37, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 52, 53, 54, 55, 57, 58, 60, 61, 62, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 75, 76, 78, 83, 84, 86, 87, 88, 89, 91, 92, 93, 94, 96, 97, 99, 100, 101, 102, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 118, 119, 123, 125, 126, 127, 128, 130} : Finset (Fin 133)) →
      bMatrix 114 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({1, 2, 3, 4, 5, 6, 9, 10, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 35, 36, 37, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 52, 53, 54, 55, 57, 58, 60, 61, 62, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 75, 76, 78, 83, 84, 86, 87, 88, 89, 91, 92, 93, 94, 96, 97, 99, 100, 101, 102, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 118, 119, 123, 125, 126, 127, 128, 130} : Finset (Fin 133)), bMatrix 114 k * bMatrix k j) =
        bInvMatrix 114 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 114 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_115 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 115 j = bInvMatrix 115 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 3, 5, 6, 7, 8, 10, 13, 14, 15, 16, 18, 19, 21, 22, 23, 24, 25, 26, 28, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 44, 47, 48, 49, 50, 53, 54, 55, 57, 58, 60, 61, 62, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 80, 82, 83, 84, 85, 86, 87, 88, 90, 91, 92, 93, 94, 95, 96, 97, 102, 103, 104, 105, 106, 107, 110, 111, 113, 114, 115, 116, 117, 118, 119, 120, 121, 123, 124, 125, 126, 127, 132} : Finset (Fin 133)) →
      bMatrix 115 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 3, 5, 6, 7, 8, 10, 13, 14, 15, 16, 18, 19, 21, 22, 23, 24, 25, 26, 28, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 44, 47, 48, 49, 50, 53, 54, 55, 57, 58, 60, 61, 62, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 80, 82, 83, 84, 85, 86, 87, 88, 90, 91, 92, 93, 94, 95, 96, 97, 102, 103, 104, 105, 106, 107, 110, 111, 113, 114, 115, 116, 117, 118, 119, 120, 121, 123, 124, 125, 126, 127, 132} : Finset (Fin 133)), bMatrix 115 k * bMatrix k j) =
        bInvMatrix 115 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 115 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_116 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 116 j = bInvMatrix 116 j := by
  have hs : ∀ k : Fin 133, k ∉ ({73} : Finset (Fin 133)) →
      bMatrix 116 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({73} : Finset (Fin 133)), bMatrix 116 k * bMatrix k j) =
        bInvMatrix 116 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 116 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_117 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 117 j = bInvMatrix 117 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 23, 25, 26, 28, 31, 32, 33, 34, 35, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 52, 53, 54, 55, 56, 58, 59, 60, 61, 62, 63, 64, 67, 68, 69, 71, 72, 73, 74, 75, 77, 78, 79, 80, 82, 83, 84, 85, 88, 90, 91, 92, 93, 94, 95, 96, 98, 99, 100, 101, 103, 105, 106, 108, 110, 112, 113, 115, 116, 117, 119, 120, 122, 123, 124, 125, 126, 127, 130, 131, 132} : Finset (Fin 133)) →
      bMatrix 117 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 23, 25, 26, 28, 31, 32, 33, 34, 35, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 52, 53, 54, 55, 56, 58, 59, 60, 61, 62, 63, 64, 67, 68, 69, 71, 72, 73, 74, 75, 77, 78, 79, 80, 82, 83, 84, 85, 88, 90, 91, 92, 93, 94, 95, 96, 98, 99, 100, 101, 103, 105, 106, 108, 110, 112, 113, 115, 116, 117, 119, 120, 122, 123, 124, 125, 126, 127, 130, 131, 132} : Finset (Fin 133)), bMatrix 117 k * bMatrix k j) =
        bInvMatrix 117 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 117 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_118 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 118 j = bInvMatrix 118 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 51, 52, 53, 54, 56, 58, 59, 60, 62, 63, 65, 66, 67, 68, 69, 71, 73, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 97, 98, 99, 100, 101, 103, 105, 107, 108, 111, 112, 113, 114, 115, 116, 117, 118, 119, 122, 123, 124, 125, 126, 127, 128, 130, 131} : Finset (Fin 133)) →
      bMatrix 118 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 51, 52, 53, 54, 56, 58, 59, 60, 62, 63, 65, 66, 67, 68, 69, 71, 73, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 97, 98, 99, 100, 101, 103, 105, 107, 108, 111, 112, 113, 114, 115, 116, 117, 118, 119, 122, 123, 124, 125, 126, 127, 128, 130, 131} : Finset (Fin 133)), bMatrix 118 k * bMatrix k j) =
        bInvMatrix 118 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 118 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_119 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 119 j = bInvMatrix 119 j := by
  have hs : ∀ k : Fin 133, k ∉ ({75} : Finset (Fin 133)) →
      bMatrix 119 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({75} : Finset (Fin 133)), bMatrix 119 k * bMatrix k j) =
        bInvMatrix 119 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 119 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_120 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 120 j = bInvMatrix 120 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 19, 21, 23, 24, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 37, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 58, 59, 60, 63, 64, 65, 66, 67, 68, 69, 72, 73, 74, 75, 77, 79, 81, 82, 83, 84, 85, 86, 87, 89, 90, 91, 92, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 108, 109, 110, 111, 112, 113, 114, 115, 116, 118, 119, 120, 122, 123, 124, 127, 129, 130, 131} : Finset (Fin 133)) →
      bMatrix 120 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 19, 21, 23, 24, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 37, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 58, 59, 60, 63, 64, 65, 66, 67, 68, 69, 72, 73, 74, 75, 77, 79, 81, 82, 83, 84, 85, 86, 87, 89, 90, 91, 92, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 108, 109, 110, 111, 112, 113, 114, 115, 116, 118, 119, 120, 122, 123, 124, 127, 129, 130, 131} : Finset (Fin 133)), bMatrix 120 k * bMatrix k j) =
        bInvMatrix 120 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 120 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_121 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 121 j = bInvMatrix 121 j := by
  have hs : ∀ k : Fin 133, k ∉ ({76} : Finset (Fin 133)) →
      bMatrix 121 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({76} : Finset (Fin 133)), bMatrix 121 k * bMatrix k j) =
        bInvMatrix 121 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 121 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_122 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 122 j = bInvMatrix 122 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 4, 5, 6, 7, 10, 12, 14, 15, 16, 18, 19, 22, 23, 24, 25, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 44, 46, 47, 49, 50, 51, 52, 53, 54, 56, 58, 59, 60, 62, 65, 66, 67, 68, 72, 73, 75, 76, 77, 79, 80, 82, 83, 85, 88, 89, 90, 91, 93, 94, 95, 96, 97, 98, 99, 100, 101, 105, 107, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 124, 126, 127, 128, 129, 130, 131, 132} : Finset (Fin 133)) →
      bMatrix 122 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 4, 5, 6, 7, 10, 12, 14, 15, 16, 18, 19, 22, 23, 24, 25, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 44, 46, 47, 49, 50, 51, 52, 53, 54, 56, 58, 59, 60, 62, 65, 66, 67, 68, 72, 73, 75, 76, 77, 79, 80, 82, 83, 85, 88, 89, 90, 91, 93, 94, 95, 96, 97, 98, 99, 100, 101, 105, 107, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 124, 126, 127, 128, 129, 130, 131, 132} : Finset (Fin 133)), bMatrix 122 k * bMatrix k j) =
        bInvMatrix 122 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 122 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_123 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 123 j = bInvMatrix 123 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 61, 63, 64, 65, 66, 68, 69, 70, 71, 73, 74, 75, 78, 80, 81, 82, 83, 84, 86, 87, 89, 90, 91, 93, 94, 96, 98, 99, 100, 102, 105, 106, 107, 108, 109, 110, 111, 112, 115, 117, 118, 119, 120, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132} : Finset (Fin 133)) →
      bMatrix 123 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 61, 63, 64, 65, 66, 68, 69, 70, 71, 73, 74, 75, 78, 80, 81, 82, 83, 84, 86, 87, 89, 90, 91, 93, 94, 96, 98, 99, 100, 102, 105, 106, 107, 108, 109, 110, 111, 112, 115, 117, 118, 119, 120, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132} : Finset (Fin 133)), bMatrix 123 k * bMatrix k j) =
        bInvMatrix 123 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 123 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_124 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 124 j = bInvMatrix 124 j := by
  have hs : ∀ k : Fin 133, k ∉ ({78} : Finset (Fin 133)) →
      bMatrix 124 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({78} : Finset (Fin 133)), bMatrix 124 k * bMatrix k j) =
        bInvMatrix 124 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 124 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_125 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 125 j = bInvMatrix 125 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 29, 31, 33, 36, 38, 39, 40, 43, 44, 45, 46, 47, 48, 49, 51, 52, 53, 56, 57, 58, 59, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 75, 76, 77, 79, 80, 81, 83, 85, 86, 87, 88, 90, 91, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 116, 117, 118, 119, 121, 122, 124, 125, 126, 127, 128, 129, 130, 132} : Finset (Fin 133)) →
      bMatrix 125 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 29, 31, 33, 36, 38, 39, 40, 43, 44, 45, 46, 47, 48, 49, 51, 52, 53, 56, 57, 58, 59, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 75, 76, 77, 79, 80, 81, 83, 85, 86, 87, 88, 90, 91, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 116, 117, 118, 119, 121, 122, 124, 125, 126, 127, 128, 129, 130, 132} : Finset (Fin 133)), bMatrix 125 k * bMatrix k j) =
        bInvMatrix 125 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 125 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_126 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 126 j = bInvMatrix 126 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 21, 22, 24, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 51, 53, 55, 56, 57, 59, 60, 61, 62, 64, 67, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 80, 83, 84, 85, 89, 92, 94, 95, 96, 97, 98, 99, 100, 102, 103, 104, 105, 106, 107, 108, 109, 112, 113, 114, 115, 116, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132} : Finset (Fin 133)) →
      bMatrix 126 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 21, 22, 24, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 51, 53, 55, 56, 57, 59, 60, 61, 62, 64, 67, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 80, 83, 84, 85, 89, 92, 94, 95, 96, 97, 98, 99, 100, 102, 103, 104, 105, 106, 107, 108, 109, 112, 113, 114, 115, 116, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132} : Finset (Fin 133)), bMatrix 126 k * bMatrix k j) =
        bInvMatrix 126 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 126 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_127 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 127 j = bInvMatrix 127 j := by
  have hs : ∀ k : Fin 133, k ∉ ({2, 3, 6, 7, 8, 9, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 52, 53, 54, 55, 56, 58, 59, 60, 61, 62, 64, 65, 67, 68, 69, 70, 71, 72, 73, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 87, 88, 91, 93, 95, 96, 97, 98, 99, 102, 103, 104, 106, 107, 108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 122, 123, 125, 126, 127, 128, 130, 132} : Finset (Fin 133)) →
      bMatrix 127 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({2, 3, 6, 7, 8, 9, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 52, 53, 54, 55, 56, 58, 59, 60, 61, 62, 64, 65, 67, 68, 69, 70, 71, 72, 73, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 87, 88, 91, 93, 95, 96, 97, 98, 99, 102, 103, 104, 106, 107, 108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 122, 123, 125, 126, 127, 128, 130, 132} : Finset (Fin 133)), bMatrix 127 k * bMatrix k j) =
        bInvMatrix 127 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 127 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_128 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 128 j = bInvMatrix 128 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 52, 54, 55, 56, 58, 59, 60, 61, 62, 64, 65, 67, 68, 69, 70, 71, 72, 73, 74, 76, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 94, 95, 96, 97, 98, 99, 100, 101, 102, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131} : Finset (Fin 133)) →
      bMatrix 128 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 52, 54, 55, 56, 58, 59, 60, 61, 62, 64, 65, 67, 68, 69, 70, 71, 72, 73, 74, 76, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 94, 95, 96, 97, 98, 99, 100, 101, 102, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131} : Finset (Fin 133)), bMatrix 128 k * bMatrix k j) =
        bInvMatrix 128 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 128 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_129 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 129 j = bInvMatrix 129 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 2, 3, 4, 5, 7, 8, 9, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 31, 32, 33, 35, 36, 37, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 53, 55, 56, 57, 58, 59, 60, 62, 64, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 85, 86, 88, 89, 90, 92, 93, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 113, 115, 116, 117, 118, 119, 120, 122, 123, 124, 125, 128, 131, 132} : Finset (Fin 133)) →
      bMatrix 129 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 2, 3, 4, 5, 7, 8, 9, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 31, 32, 33, 35, 36, 37, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 53, 55, 56, 57, 58, 59, 60, 62, 64, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 85, 86, 88, 89, 90, 92, 93, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 113, 115, 116, 117, 118, 119, 120, 122, 123, 124, 125, 128, 131, 132} : Finset (Fin 133)), bMatrix 129 k * bMatrix k j) =
        bInvMatrix 129 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 129 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_130 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 130 j = bInvMatrix 130 j := by
  have hs : ∀ k : Fin 133, k ∉ ({83} : Finset (Fin 133)) →
      bMatrix 130 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({83} : Finset (Fin 133)), bMatrix 130 k * bMatrix k j) =
        bInvMatrix 130 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 130 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_131 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 131 j = bInvMatrix 131 j := by
  have hs : ∀ k : Fin 133, k ∉ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 28, 29, 30, 31, 32, 33, 35, 36, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 58, 60, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 76, 78, 79, 80, 81, 82, 83, 86, 87, 88, 89, 92, 94, 95, 96, 97, 98, 102, 103, 104, 106, 107, 108, 109, 113, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 127, 128, 129} : Finset (Fin 133)) →
      bMatrix 131 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 28, 29, 30, 31, 32, 33, 35, 36, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 58, 60, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 76, 78, 79, 80, 81, 82, 83, 86, 87, 88, 89, 92, 94, 95, 96, 97, 98, 102, 103, 104, 106, 107, 108, 109, 113, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 127, 128, 129} : Finset (Fin 133)), bMatrix 131 k * bMatrix k j) =
        bInvMatrix 131 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 131 _ hs j).trans (hv j)

set_option maxHeartbeats 0 in
private theorem row_132 : ∀ j : Fin 133,
    (bMatrix * bMatrix) 132 j = bInvMatrix 132 j := by
  have hs : ∀ k : Fin 133, k ∉ ({84} : Finset (Fin 133)) →
      bMatrix 132 k = 0 := by decide +kernel
  have hv : ∀ j : Fin 133,
      (∑ k ∈ ({84} : Finset (Fin 133)), bMatrix 132 k * bMatrix k j) =
        bInvMatrix 132 j := by decide +kernel
  intro j
  exact (GeneratorCertificates.sparse_mul_row bMatrix bMatrix 132 _ hs j).trans (hv j)

/-- The kernel-certified BSquare identity for the ATLAS matrices. -/
public theorem bMatrix_mul_self : bMatrix * bMatrix = bInvMatrix := by
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
