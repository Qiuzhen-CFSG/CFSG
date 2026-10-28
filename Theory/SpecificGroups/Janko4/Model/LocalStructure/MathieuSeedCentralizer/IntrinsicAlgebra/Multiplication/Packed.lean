module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Data

/-!
# Binary arithmetic for the literal seed algebra

A product row is the XOR of right rows selected by the left row. The lemmas
below prove the connection to matrix multiplication and linear combinations.
Only the resulting natural-number identities are evaluated by the kernel.
The row-major convention is the one in `IntrinsicAlgebra/source/README.md`.
-/

open scoped Matrix
@[expose] public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open GeneratorCertificates
namespace MultiplicationCertificate

def flatRows (x : ℕ) : Vector ℕ 56 :=
  Vector.ofFn fun i => (x >>> (56 * i.val)) % 2^56

lemma decode_flatRows (x : ℕ) : decodeMatrixRows (flatRows x) = decodeFlat x := by
  funext i j
  simp only [decodeMatrixRows, flatRows, get_ofFn, decodeFlat, bit,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, j.isLt, decide_true, Bool.true_and]

def rowProduct (x : ℕ) (ys : Fin 56 → ℕ) : ℕ :=
  xorList (List.ofFn (fun k : Fin 56 => if x.testBit k.val then ys k else 0))

lemma rowProduct_spec (x : ℕ) (ys : Fin 56 → ℕ) (j : Fin 56) :
    bit (rowProduct x ys) j.val = ∑ k : Fin 56, bit x k.val * bit (ys k) j.val := by
  change GeneratorCertificates.bit (rowProduct x ys) j.val = _
  rw [rowProduct, bit_xorList, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  simp only [bit, GeneratorCertificates.bit]
  cases h : x.testBit k.val <;> simp [h]

lemma flat_mul_eq (x y z : ℕ)
    (h : ∀ i : Fin 56, rowProduct ((x >>> (56*i.val)) % 2^56)
      (fun k => (y >>> (56*k.val)) % 2^56) = (z >>> (56*i.val)) % 2^56) :
    decodeFlat x * decodeFlat y = decodeFlat z := by
  funext i j
  have hj := congrArg (fun a => bit a j.val) (h i)
  rw [rowProduct_spec] at hj
  simpa only [bit, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Fin.isLt, decide_true, Bool.true_and, Matrix.mul_apply, decodeFlat] using hj

lemma decodeFlat_zero : decodeFlat 0 = 0 := by
  funext i j
  simp only [decodeFlat, bit, Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte]
  rfl

def flatRow (x : ℕ) (i : Fin 56) : ℕ := (x >>> (56*i.val)) % 2^56

def productRow (x y : ℕ) (i : Fin 56) : ℕ :=
  rowProduct (flatRow x i) (flatRow y)

lemma productRow_spec (x y : ℕ) (i j : Fin 56) :
    bit (productRow x y i) j.val = (decodeFlat x * decodeFlat y) i j := by
  rw [productRow, rowProduct_spec, Matrix.mul_apply]
  simp only [flatRow, bit, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Fin.isLt, decide_true, Bool.true_and, decodeFlat]

lemma flat_mul_eq_mul (x y : ℕ)
    (h : ∀ i : Fin 56, productRow x y i = productRow y x i) :
    decodeFlat x * decodeFlat y = decodeFlat y * decodeFlat x := by
  funext i j
  rw [← productRow_spec, ← productRow_spec, h]

lemma flat_eq_one (x : ℕ) (h : ∀ i : Fin 56, flatRow x i = 2^i.val) :
    decodeFlat x = 1 := by
  funext i j
  have hj := congrArg (fun a => bit a j.val) (h i)
  simpa only [flatRow, bit, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Fin.isLt, decide_true, Bool.true_and, Nat.testBit_two_pow, decide_eq_true_eq,
    decodeFlat, Matrix.one_apply, Fin.ext_iff] using hj

def combination {n : ℕ} (words : Vector ℕ n) (c : ℕ) : ℕ :=
  xorList (List.ofFn (fun i : Fin n => if c.testBit i.val then words.get i else 0))

lemma decode_combination {n : ℕ} (words : Vector ℕ n) (c : ℕ) :
    decodeFlat (combination words c) =
      ∑ i : Fin n, bit c i.val • decodeFlat (words.get i) := by
  funext j k
  change GeneratorCertificates.bit (combination words c) (56*j.val+k.val) = _
  rw [combination, bit_xorList, List.map_ofFn, List.sum_ofFn]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, decodeFlat]
  apply Finset.sum_congr rfl
  intro i _
  change (if (if c.testBit i.val then words.get i else 0).testBit _ then 1 else 0) = _
  cases h : c.testBit i.val <;> simp only [h, Bool.false_eq_true, ↓reduceIte,
    bit, Nat.zero_testBit, zero_mul, one_mul]

end MultiplicationCertificate
end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
