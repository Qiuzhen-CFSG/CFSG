module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.FiniteAlgebra.Linear
/-!
# Parity checks for mixed matrices

Successive XORs of shifted masks compute the parity of the 600 entries.
The proof identifies this computation with the Frobenius pairing, so the
finite annihilator checks imply actual linear-form equalities over F₂.
See source/README.md for the mixed-space certificate and data provenance.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.FiniteAlgebra
open GeneratorCertificates

def foldPow : ℕ → ℕ → ℕ
  | 0, x => x
  | k+1, x => foldPow k (x ^^^ (x >>> 2^k))

lemma sum_bits_split (n m x : ℕ) :
    (∑ i : Fin (n+m), bit x i.val) =
      (∑ i : Fin n, bit x i.val) + (∑ i : Fin m, bit (x >>> n) i.val) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd, bit, Nat.testBit_shiftRight]

lemma bit_foldPow (k x : ℕ) :
    bit (foldPow k x) 0 = ∑ i : Fin (2^k), bit x i.val := by
  induction k generalizing x with
  | zero =>
    change bit x 0 = ∑ i : Fin 1, bit x i.val
    rw [Fin.sum_univ_one]
    rfl
  | succ k ih =>
    rw [foldPow, ih, show 2^(k+1) = 2^k+2^k by omega, sum_bits_split]
    simp only [bit_xor, Finset.sum_add_distrib]

/-- Logarithmic-depth parity of the 600 entries of a mixed matrix. -/
def parity600 (x : ℕ) : ℕ :=
  foldPow 9 x ^^^ (foldPow 6 (x >>> 512) ^^^
    (foldPow 4 (x >>> 576) ^^^ foldPow 3 (x >>> 592)))

lemma bit_parity600 (x : ℕ) : bit (parity600 x) 0 = ∑ i : Fin 600, bit x i.val := by
  rw [show 600 = 512+88 from rfl, sum_bits_split,
    show 88 = 64+24 from rfl, sum_bits_split, show 24 = 16+8 from rfl, sum_bits_split]
  simp only [parity600, bit_xor, bit_foldPow, ← Nat.shiftRight_add]
  rfl

lemma fast_pairing (x y : ℕ) :
    bit (parity600 (x &&& y)) 0 =
      pairing (rectDecode 50 (slices 12 50 x)) (rectDecode 50 (slices 12 50 y)) := by
  rw [← ev_packed_pairing, bit_dotMask, bit_parity600]
  apply Finset.sum_congr rfl
  intro i _
  simp only [bit, Nat.testBit_and]
  cases x.testBit i.val <;> cases y.testBit i.val <;> decide
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.FiniteAlgebra
