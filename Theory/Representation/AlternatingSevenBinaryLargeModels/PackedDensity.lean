module

public import Theory.Representation.AbsolutelyIrreducible
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix

/-!
# Compact binary matrix spanning certificates

The action algebra is full when a checked list of its elements spans the matrix
units. Binary coefficient vectors are stored as natural numbers; XOR computes
linear combinations. The soundness proof relates each bit to the corresponding
matrix entry. This avoids reducing large sums of `ZMod 2` matrices in the kernel.

Application: the binary A₇ representations used in Aschbacher–Smith K.1.2.
-/

@[expose] public section

open Matrix
open Thompson.BinaryMatrix
namespace Representation.AlternatingSevenBinaryLargeModels
namespace Packed

/-- Row-major binary matrix, stored in one natural number. -/
def matrix (n : ℕ) (a : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => bit a (n * i.val + j.val)

/-- Extract the binary rows. -/
def rows (n : ℕ) (a : ℕ) : Array ℕ :=
  Array.ofFn fun i : Fin n => (a >>> (n * i.val)) % 2 ^ n

theorem decode_rows (n a : ℕ) : decode n (rows n a) = matrix n a := by
  ext i j
  simp [decode, rows, matrix, bit, Nat.testBit_mod_two_pow, i.isLt, j.isLt, Nat.testBit_shiftRight, Nat.add_comm]

/-- A row-wise XOR calculation certifies a matrix product. -/
theorem matrix_mul (n a b c : ℕ)
    (h : ∀ i : Fin n,
      rowProduct (rows n a)[i.val]! (rows n b) n = (rows n c)[i.val]!) :
    matrix n a * matrix n b = matrix n c := by
  rw [← decode_rows, ← decode_rows, ← decode_rows]
  exact decode_mul n (rows n a) (rows n b) (rows n c) h

/-- Checked coefficients expressing all matrix units prove matrix density. -/
theorem eq_top_of_spanning (n d : ℕ) (data coefficients : Array ℕ)
    (h : ∀ i j : Fin n,
      rowProduct coefficients[n * i.val + j.val]! data d = 2 ^ (n * i.val + j.val))
    (A : Subalgebra (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)))
    (hm : ∀ k : Fin d, matrix n data[k.val]! ∈ A) : A = ⊤ := by
  have units (i j : Fin n) : Matrix.single i j (1 : ZMod 2) ∈ A := by
    have he : (∑ k : Fin d, bit coefficients[n * i.val + j.val]! k.val •
        matrix n data[k.val]!) = Matrix.single i j 1 := by
      ext x y
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, matrix]
      rw [Fin.sum_univ_eq_sum_range (fun k =>
        bit coefficients[n * i.val + j.val]! k * bit data[k]! (n * x.val + y.val)),
        ← bit_rowProduct, h i j]
      simp only [bit, Nat.testBit_two_pow, Matrix.single_apply]
      have hi : n * i.val + j.val = n * x.val + y.val ↔ i = x ∧ j = y := by
        constructor
        · intro hxy
          have hr := congrArg (fun z => z % n) hxy
          have hq := congrArg (fun z => z / n) hxy
          simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add,
            Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt y.isLt] at hr
          simp only [Nat.mul_add_div (Nat.zero_lt_of_lt i.isLt),
            Nat.div_eq_of_lt j.isLt, Nat.div_eq_of_lt y.isLt, Nat.add_zero] at hq
          exact ⟨Fin.ext hq, Fin.ext hr⟩
        · rintro ⟨rfl, rfl⟩; rfl
      by_cases hxy : i = x ∧ j = y <;> simp [hi, hxy]
    rw [← he]
    exact A.sum_mem fun k _ => A.smul_mem (hm k) _
  apply top_unique
  intro M _
  rw [show M = ∑ i, ∑ j, M i j • Matrix.single i j 1 by
    simpa using Matrix.matrix_eq_sum_single M]
  exact A.sum_mem fun i _ => A.sum_mem fun j _ => A.smul_mem (units i j) _

end Packed
end Representation.AlternatingSevenBinaryLargeModels
