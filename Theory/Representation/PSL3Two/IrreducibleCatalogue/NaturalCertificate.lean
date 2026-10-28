module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Coordinates
import Mathlib.Tactic

/-!
# A checked spanning certificate for the binary natural action

Nine explicit words in the coordinate cycle and a transvection span the
three-space endomorphism algebra. Their action matrices and an inverse
coefficient table are verified by kernel reduction. This is the natural-module
absolute irreducibility ingredient of Aschbacher–Smith H.6.1, printed p.386.
-/

@[expose] public section

open Matrix
namespace BinaryLinearThree.IrreducibleCatalogue
namespace NaturalCertificate

private def words : Fin 9 → List Bool := ![[],
    [false],
    [true],
    [false, false],
    [true, false],
    [false, true],
    [true, false, false],
    [false, true, false],
    [false, true, false, false]]

private def packed : Fin 9 → ℕ := ![273,
    98,
    281,
    140,
    99,
    114,
    204,
    142,
    401]

private def inverseColumns : Fin 9 → ℕ := ![18,
    136,
    268,
    5,
    34,
    194,
    72,
    257,
    49]

private def storedMatrix (k : Fin 9) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  fun i j => if (packed k).testBit (3 * j.val + i.val) then 1 else 0

private def matrixWord : List Bool → Matrix (Fin 3) (Fin 3) (ZMod 2)
  | [] => 1
  | b :: bs => (if b then shear.val else cycle.val) * matrixWord bs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem words_checked : ∀ k : Fin 9, matrixWord (words k) = storedMatrix k := by
  decide +kernel

private def coefficient (i j : Fin 3) (k : Fin 9) : ZMod 2 :=
  if (inverseColumns ⟨3 * j.val + i.val, by omega⟩).testBit k.val then 1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem inverse_checked : ∀ i j : Fin 3,
    (∑ k : Fin 9, coefficient i j k • storedMatrix k) = Matrix.single i j 1 := by
  decide +kernel

private theorem matrixWord_mem (A : Subalgebra (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hc : cycle.val ∈ A) (ht : shear.val ∈ A) (w : List Bool) : matrixWord w ∈ A := by
  induction w with
  | nil => exact A.one_mem
  | cons b bs ih =>
    apply A.mul_mem _ ih
    cases b
    · exact hc
    · exact ht

theorem matrix_algebra_eq_top (A : Subalgebra (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hc : cycle.val ∈ A) (ht : shear.val ∈ A) : A = ⊤ := by
  have hunit (i j : Fin 3) : Matrix.single i j (1 : ZMod 2) ∈ A := by
    rw [← inverse_checked i j]
    apply A.sum_mem
    intro k _
    apply A.smul_mem
    rw [← words_checked]
    exact matrixWord_mem A hc ht _
  apply top_unique
  intro M _
  have hM : M = ∑ i : Fin 3, ∑ j : Fin 3, M i j • Matrix.single i j 1 := by
    simpa using Matrix.matrix_eq_sum_single M
  rw [hM]
  apply A.sum_mem
  intro i _
  apply A.sum_mem
  intro j _
  exact A.smul_mem (hunit i j) (M i j)

end NaturalCertificate
end BinaryLinearThree.IrreducibleCatalogue
