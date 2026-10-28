module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement.Arithmetic
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators

/-! Packed parity and matrix transport for the displacement separation certificate.
The parity computation is interpreted as the ordinary Frobenius pairing.
Source: ../source/README.md and ../../source/README.md. -/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement.Separation
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open GeneratorCertificates LinearMembership.FiniteAlgebra
open PolynomialCertificate

/-- Logarithmic parity of a masked, finite binary scalar product. -/
def packedDot (n k x y : ℕ) : ℕ :=
  ExteriorAnnihilators.parity k ((x &&& y) % 2^n)

theorem packedDot_spec (n k x y : ℕ) (hn : n ≤ 2^k) :
    bit (packedDot n k x y) 0 = ev (fun i : Fin n => bit y i.val) x := by
  rw [packedDot, ExteriorAnnihilators.bit_parity]
  simp only [Nat.zero_add]
  rw [show 2^k = n + (2^k-n) by omega, Finset.sum_range_add]
  have hz : (∑ i ∈ Finset.range (2^k-n), bit ((x &&& y) % 2^n) (n+i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [bit, Nat.testBit_mod_two_pow, show ¬n+i < n by omega,
      decide_false, Bool.false_and, Bool.false_eq_true, if_false]
  rw [hz, add_zero, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [bit, Nat.testBit_mod_two_pow, i.isLt, decide_true, Bool.true_and,
    Nat.testBit_and]
  cases x.testBit i.val <;> cases y.testBit i.val <;> decide

theorem packedDot_matrix (x y : ℕ) :
    bit (packedDot 2500 12 x y) 0 =
      pairing (packedMatrix x) (packedMatrix y) := by
  rw [packedDot_spec _ _ _ _ (by decide)]
  rw [← flat_unflat (m := 50) (n := 50) (fun i : Fin 2500 => bit y i.val), ev_flat]
  rfl

theorem product_eq {m n k : ℕ} (A : Vector ℕ m) (B : Vector ℕ n)
    (C : Vector ℕ m) (h : ∀ i, scan (A.get i) B.toList = C.get i) :
    rectDecode n A * rectDecode k B = rectDecode k C := by
  rw [← decode_mulRows]
  congr 1
  apply Vector.ext
  intro i hi
  change (mulRows A B).get ⟨i,hi⟩ = C.get ⟨i,hi⟩
  simpa only [mulRows, get_ofFn] using h ⟨i,hi⟩

theorem transpose_eq {m n : ℕ} (A : Vector ℕ m) (B : Vector ℕ n)
    (h : ∀ i : Fin m, ∀ j : Fin n, (A.get i).testBit j.val = (B.get j).testBit i.val) :
    (rectDecode n A)ᵀ = rectDecode m B := by
  ext i j
  simp only [Matrix.transpose_apply, rectDecode, bit, h]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement.Separation
