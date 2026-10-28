module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
/-!
# Packed natural-number matrix certificates

A single natural number stores all binary rows consecutively. Arithmetic
shifts replace indexed array lookups in the kernel. XOR row multiplication
is proved entry by entry, and the checked predicates imply literal matrix,
vector, inverse, transpose and outer-product identities over ZMod 2.
The degree-220 M24 certificates use these operations with untrusted ATLAS
witnesses; every numerical premise is separately reduced in Lean's kernel.
-/

@[expose] public section
open Thompson.BinaryMatrix
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.Packed

def rowAt (n b i : ℕ) : ℕ := (b >>> (n*i)) % (2^n)
def decodePacked (n b : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => bit (rowAt n b i.val) j.val

def row (n a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => row n a b k ^^^ (if a.testBit k then rowAt n b k else 0)

theorem bit_row (n a b k j : ℕ) :
    bit (row n a b k) j = ∑ i ∈ Finset.range k, bit a i * bit (rowAt n b i) j := by
  induction k with
  | zero => simp [row, bit]
  | succ k ih =>
    rw [row, bit_xor, ih, Finset.sum_range_succ]
    congr 1
    cases h : a.testBit k <;> simp [bit, h]

def checkMul (n a b c : ℕ) : Bool :=
  (List.range n).all fun i => row n (rowAt n a i) b n == rowAt n c i

theorem mul_sound (n a b c : ℕ) (h : checkMul n a b c = true) :
    decodePacked n a * decodePacked n b = decodePacked n c := by
  ext i j
  change (∑ k : Fin n, bit (rowAt n a i.val) k.val * bit (rowAt n b k.val) j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k => bit (rowAt n a i.val) k * bit (rowAt n b k) j.val), ← bit_row]
  have hi : row n (rowAt n a i.val) b n = rowAt n c i.val :=
    of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  exact congrArg (fun x => bit x j.val) hi
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.Packed

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.Packed

def checkInverse (n a b : ℕ) : Bool :=
  (List.range n).all fun i => row n (rowAt n a i) b n == 2 ^ i

theorem inverse_sound (n a b : ℕ) (h : checkInverse n a b = true) :
    decodePacked n a * decodePacked n b = 1 := by
  ext i j
  change (∑ k : Fin n, bit (rowAt n a i.val) k.val * bit (rowAt n b k.val) j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k => bit (rowAt n a i.val) k * bit (rowAt n b k) j.val), ← bit_row]
  have hi : row n (rowAt n a i.val) b n = 2 ^ i.val :=
    of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  rw [hi]
  simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

def checkRows (n b : ℕ) (a : Array ℕ) : Bool :=
  (List.range n).all fun i => rowAt n b i == a[i]!

theorem rows_sound (n b : ℕ) (a : Array ℕ) (h : checkRows n b a = true) :
    decodePacked n b = decode n a := by
  ext i j
  have hi : rowAt n b i.val = a[i.val]! :=
    of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  change bit (rowAt n b i.val) j.val = bit a[i.val]! j.val
  rw [hi]

def checkAdd (n a b c : ℕ) : Bool :=
  (List.range n).all fun i => rowAt n a i ^^^ rowAt n b i == rowAt n c i

theorem add_sound (n a b c : ℕ) (h : checkAdd n a b c = true) :
    decodePacked n a + decodePacked n b = decodePacked n c := by
  ext i j
  have hi : rowAt n a i.val ^^^ rowAt n b i.val = rowAt n c i.val :=
    of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  change bit (rowAt n a i.val) j.val + bit (rowAt n b i.val) j.val = _
  rw [← bit_xor, hi]
  rfl

def vector (n x : ℕ) : Fin n → ZMod 2 := fun i => bit x i.val

theorem vector_row (n x a : ℕ) :
    vector n (row n x a n) = Matrix.vecMul (vector n x) (decodePacked n a) := by
  ext j
  change bit (row n x a n) j.val = ∑ i : Fin n, bit x i.val * bit (rowAt n a i.val) j.val
  rw [bit_row, Fin.sum_univ_eq_sum_range (fun i => bit x i * bit (rowAt n a i) j.val)]

def checkTranspose (n a b : ℕ) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j =>
    (rowAt n a i).testBit j == (rowAt n b j).testBit i

theorem transpose_sound (n a b : ℕ) (h : checkTranspose n a b = true) :
    decodePacked n a = (decodePacked n b).transpose := by
  ext i j
  have hh := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  have hi : (rowAt n a i.val).testBit j.val = (rowAt n b j.val).testBit i.val :=
    of_decide_eq_true (List.all_eq_true.mp hh j.val (List.mem_range.mpr j.isLt))
  simp only [decodePacked, Matrix.transpose_apply, bit, hi]

def checkOuter (n a v l : ℕ) : Bool :=
  (List.range n).all fun i => rowAt n a i == if v.testBit i then l else 0

theorem outer_sound (n a v l : ℕ) (h : checkOuter n a v l = true) :
    decodePacked n a = Matrix.vecMulVec (vector n v) (vector n l) := by
  ext i j
  have hi : rowAt n a i.val = if v.testBit i.val then l else 0 :=
    of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  simp only [decodePacked, hi, Matrix.vecMulVec_apply, vector, bit]
  cases hv : v.testBit i.val <;> cases hl : l.testBit j.val <;> simp [hl]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.Packed
