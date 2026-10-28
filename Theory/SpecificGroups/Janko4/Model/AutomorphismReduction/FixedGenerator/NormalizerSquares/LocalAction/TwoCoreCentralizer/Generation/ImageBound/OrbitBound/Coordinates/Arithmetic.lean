module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitBound.Geometry
/-!
# Checked arithmetic for packed binary columns

A packed column is decoded with bit i as its ith coordinate. Selecting and XORing
columns implements left matrix multiplication. The proofs below connect the
finite certificates to ordinary linear algebra, using the checked XOR arithmetic
of Janko4.GeneratorCertificates.
-/

@[expose] public section
open Janko4.GeneratorCertificates
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry
namespace Coordinates
abbrev Bits (n : ℕ) := Fin n → ZMod 2
abbrev decode {n : ℕ} (x : ℕ) : Bits n := fun i => bit x i.val
def columns {m n : ℕ} (v : Fin n → ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bit (v j) i.val
def combine {n : ℕ} (cols : Fin n → ℕ) (x : ℕ) : ℕ :=
  xorList (List.ofFn (fun k : Fin n => if x.testBit k.val then cols k else 0))
theorem decode_combine {m n : ℕ} (cols : Fin n → ℕ) (x : ℕ) :
    (decode (combine cols x) : Bits m) = (columns cols) *ᵥ decode x := by
  ext i
  rw [decode, combine, bit_xorList, List.map_ofFn, List.sum_ofFn, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  simp only [decode, columns, bit]
  cases h : x.testBit k.val <;> simp [h]
theorem columns_mul {m n k : ℕ} (a : Fin n → ℕ) (b : Fin k → ℕ) :
    (columns a : Matrix (Fin m) (Fin n) (ZMod 2)) * columns b =
      columns (fun j => combine a (b j)) := by
  ext i j
  exact (congrFun (decode_combine (m := m) a (b j)) i).symm
theorem columns_xor {m n : ℕ} (a b : Fin n → ℕ) :
    (columns (fun j => a j ^^^ b j) : Matrix (Fin m) (Fin n) (ZMod 2)) =
      columns a + columns b := by
  ext i j
  exact bit_xor _ _ _
theorem columns_one (n : ℕ) :
    (columns (fun j : Fin n => 2 ^ j.val) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
  ext i j
  simp only [columns, bit, Nat.testBit_two_pow, decide_eq_true_eq, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> simp_all [eq_comm]
end Coordinates
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry
