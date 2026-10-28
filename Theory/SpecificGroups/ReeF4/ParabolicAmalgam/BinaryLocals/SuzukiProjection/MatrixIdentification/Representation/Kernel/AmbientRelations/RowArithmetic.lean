module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.AmbientRelations.Data

/-!
# Certified packed row multiplication

XOR is addition in the binary field. Induction over the 52 possible summands
identifies the packed row product with the usual matrix product. This small
checker follows `Thompson.Model.GeneratorCertificates.BinaryMatrix`; it has no
hypothesis about a group or a representation.
-/

@[expose] public section
namespace ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof.AmbientComputation
open scoped BigOperators

private theorem bit_xor (a b j : ℕ) : bit (a ^^^ b) j = bit a j + bit b j := by
  simp only [bit, Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> decide

/-- Compute a row product by selecting and XORing rows of the right matrix. -/
def rowProduct (a : ℕ) (b : Array ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => rowProduct a b k ^^^ (if a.testBit k then b[k]! else 0)

private theorem bit_rowProduct (a : ℕ) (b : Array ℕ) (n j : ℕ) :
    bit (rowProduct a b n) j = ∑ k ∈ Finset.range n, bit a k * bit b[k]! j := by
  induction n with
  | zero => simp [rowProduct, bit]
  | succ n ih =>
    rw [rowProduct, bit_xor, ih, Finset.sum_range_succ]
    congr 1
    cases h : a.testBit n <;> simp [bit, h]

/-- A complete check of the packed rows proves equality of the full matrices. -/
theorem decode_mul (a b c : Array ℕ)
    (h : ∀ i : Fin 52, rowProduct a[i.val]! b 52 = c[i.val]!) :
    decode a * decode b = decode c := by
  ext i j
  change (∑ k : Fin 52, bit a[i.val]! k.val * bit b[k.val]! j.val) = bit c[i.val]! j.val
  rw [Fin.sum_univ_eq_sum_range (fun k => bit a[i.val]! k * bit b[k]! j.val),
    ← bit_rowProduct, h i]

end ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof.AmbientComputation
