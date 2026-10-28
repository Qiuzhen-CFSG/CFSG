module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.Arithmetic
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorInvariance.Arithmetic
/-!
# Transporting packed functionals to ambient forms

The binary matrix pairing moves restriction across to the functional:
pairing with E W Eᵀ equals pairing W with Eᵀ R E. A logarithmic XOR
fold evaluates the full 112 by 112 binary dot product. These arithmetic
identities allow the numerical checks to use the already certified full
encodings of every original exterior form.

The matrix and bit conventions are those of PolynomialCertificate/source/README.md
and KernelEquations/ExteriorInvariance. No numerical identity is assumed here.
-/

@[expose] public section
open scoped Matrix
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.ExteriorAnnihilators
open PullbackCoefficients ExteriorInvariance

def parity : ℕ → ℕ → ℕ
  | 0, x => x
  | k+1, x => parity k (x ^^^ (x >>> 2^k))

theorem bit_parity (k x j : ℕ) :
    bit (parity k x) j = ∑ i ∈ Finset.range (2^k), bit x (j+i) := by
  induction k generalizing x with
  | zero => simp only [parity, pow_zero, Finset.sum_range_one, Nat.add_zero]
  | succ k ih =>
    rw [parity, ih, show 2^(k+1) = 2^k+2^k by omega,
      Finset.sum_range_add]
    simp only [bit_xor, bit, Nat.testBit_shiftRight, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show 2^k+(j+i) = j+(2^k+i) by omega]

theorem bit_and (x y j : ℕ) : bit (x &&& y) j = bit x j * bit y j := by
  simp only [bit, Nat.testBit_and]
  cases x.testBit j <;> cases y.testBit j <;> decide

def pairing {m n : ℕ} (A B : Matrix (Fin m) (Fin n) (ZMod 2)) : ZMod 2 :=
  ∑ i, ∑ j, A i j * B i j

theorem pairing_comm {m n : ℕ} (A B : Matrix (Fin m) (Fin n) (ZMod 2)) :
    pairing A B = pairing B A := by
  simp only [pairing, mul_comm]

theorem pairing_mul_right {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (ZMod 2))
    (B : Matrix (Fin m) (Fin n) (ZMod 2)) (C : Matrix (Fin l) (Fin n) (ZMod 2)) :
    pairing (A*B) C = pairing A (C*Bᵀ) := by
  simp only [pairing, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem pairing_transpose {m n : ℕ} (A B : Matrix (Fin m) (Fin n) (ZMod 2)) :
    pairing Aᵀ Bᵀ = pairing A B := by
  exact Finset.sum_comm

theorem pairing_mul_left {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (ZMod 2))
    (B : Matrix (Fin m) (Fin n) (ZMod 2)) (C : Matrix (Fin l) (Fin n) (ZMod 2)) :
    pairing (A*B) C = pairing B (Aᵀ*C) := by
  rw [← pairing_transpose (A*B) C, Matrix.transpose_mul, pairing_mul_right,
    ← Matrix.transpose_mul, pairing_transpose]

def flatDot (x y : ℕ) : Bool :=
  (parity 14 ((x &&& y) % 2^12544)).testBit 0

theorem flatDot_spec (x y : ℕ) :
    (if flatDot x y then (1 : ZMod 2) else 0) = pairing (flatMatrix x) (flatMatrix y) := by
  change bit (parity 14 ((x &&& y) % 2^12544)) 0 = _
  rw [bit_parity]
  simp only [Nat.zero_add]
  change (∑ i ∈ Finset.range (12544 + 3840), bit ((x &&& y) % 2^12544) i) = _
  rw [Finset.sum_range_add]
  have hz : (∑ i ∈ Finset.range 3840, bit ((x &&& y) % 2^12544) (12544+i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [bit, Nat.testBit_mod_two_pow, show ¬12544+i < 12544 by omega,
      decide_false, Bool.false_and, Bool.false_eq_true, if_false]
  rw [hz, add_zero, ← Fin.sum_univ_eq_sum_range]
  have he := (finProdFinEquiv (m := 112) (n := 112)).sum_comp
    (fun i => bit ((x &&& y) % 2^12544) i.val)
  rw [← he, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change bit ((x &&& y) % 2^12544) (j.val + 112*i.val) = _
  have hb : j.val + 112*i.val < 12544 := by omega
  rw [show bit ((x &&& y) % 2^12544) (j.val+112*i.val) =
      bit (x &&& y) (j.val+112*i.val) by
    simp only [bit, Nat.testBit_mod_two_pow, hb, decide_true, Bool.true_and], bit_and]
  simp only [flatMatrix, Nat.add_comm]

def weightRows (w : ℕ) : Vector ℕ 50 := Vector.ofFn (weightRow w)

theorem weightRows_spec (w : ℕ) (R : RestrictionMatrix) :
    pairing (rowsMatrix (weightRows w)) R = upperValue w R := by
  simp only [pairing, rowsMatrix, weightRows, get_ofFn, bit_weightRow, upperValue]

theorem transport_spec (w : ℕ) (R : BinaryMatrix) :
    pairing (restrictionEmbedding * rowsMatrix (weightRows w) * restrictionEmbeddingᵀ) R =
      upperValue w (restrictionForm R) := by
  rw [pairing_mul_right, Matrix.transpose_transpose, pairing_mul_left,
    ← Matrix.mul_assoc, weightRows_spec]
  rfl

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.ExteriorAnnihilators
