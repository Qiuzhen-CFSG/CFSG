module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.Seed
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Bits
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Sequential binary arithmetic for the degree-1242 orbit certificates

Packed multiplication and transposition are identified with matrices over
`ZMod 2`. A checked left inverse makes the stored rows span. Interval checks
allow dense computations to be verified in bounded batches. The sequential
multiplication follows JankoTwo's `OneSixty/Arithmetic.lean` in this project;
the inverse-to-span argument follows M23's `FactorMatrices/Certificate.lean`.

The concrete consumers use the literal ATLAS M24 degree-1242 matrices and the
witnesses documented in `../source/README.md`. Application: James,
J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases
open Thompson.BinaryMatrix Matrix

/-- Sequential XOR of the rows selected by a packed binary vector. -/
def packedRow (a : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | b :: bs, k => (if a.testBit k then b else 0) ^^^ packedRow a bs (k+1)

def entry (xs : List ℕ) (i : ℕ) : ℕ := xs[i]?.getD 0
def vector {n : ℕ} (x : ℕ) : Fin n → ZMod 2 := fun i => bit x i.val
def matrix {n : ℕ} (xs : List ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i => vector (entry xs i.val)

theorem bit_packedRow (n : ℕ) (f : Fin n → ℕ) (a j k : ℕ) :
    bit (packedRow a (List.ofFn f) k) j = ∑ i, bit a (k + i.val) * bit (f i) j := by
  induction n generalizing k with
  | zero => simp [List.ofFn_zero, packedRow, bit]
  | succ n ih =>
    rw [List.ofFn_succ, packedRow, bit_xor, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    · cases h : a.testBit k <;> simp [bit, h]
    · apply Finset.sum_congr rfl
      intro i _
      simp [Nat.add_left_comm, Nat.add_comm]

theorem ofFn_entry (xs : List ℕ) :
    List.ofFn (fun i : Fin xs.length => entry xs i.val) = xs := by
  simp [entry]

theorem vector_packedRow {n : ℕ} (xs : List ℕ) (hx : xs.length = n) (a : ℕ) :
    vector (n := n) (packedRow a xs 0) = vecMul (vector a) (matrix xs) := by
  subst n
  funext j
  have he := bit_packedRow xs.length (fun i => entry xs i.val) a j.val 0
  simpa only [ofFn_entry, Nat.zero_add, vecMul, dotProduct, matrix, vector] using he

/-- Pack one column of a row table; the first entry becomes the low bit. -/
def transposeRow : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: as, j => Nat.bit (a.testBit j) (transposeRow as j)

theorem bit_transposeRow (n : ℕ) (f : Fin n → ℕ) (i : Fin n) (j : ℕ) :
    bit (transposeRow (List.ofFn f) j) i.val = bit (f i) j := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [List.ofFn_succ, transposeRow]
    cases i using Fin.cases with
    | zero => simp only [Fin.val_zero, bit, Nat.testBit_bit_zero]
    | succ i =>
      simp only [bit, Fin.val_succ, Nat.testBit_bit_succ]
      exact ih _ i

theorem transpose_sound {n : ℕ} (xs ys : List ℕ) (hx : xs.length = n)
    (h : ∀ i : Fin n, transposeRow xs i.val = entry ys i.val) :
    (matrix (n := n) xs).transpose = matrix ys := by
  subst n
  ext i j
  change bit (entry xs j.val) i.val = bit (entry ys i.val) j.val
  rw [← h i]
  simpa only [ofFn_entry] using
    (bit_transposeRow xs.length (fun k => entry xs k.val) j i.val).symm

theorem matrix_array {n : ℕ} (xs : Array ℕ) :
    matrix (n := n) xs.toList = decode n xs := by
  ext i j
  simp [matrix, vector, entry, decode, getElem!_def]
  cases xs[i.val]? <;> rfl

/-- A half-open interval of arithmetic checks, split without rerunning earlier checks. -/
def checkRange (f : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | len + 1 => f start && checkRange f (start + 1) len

theorem checkRange_sound (f : ℕ → Bool) (start len : ℕ)
    (h : checkRange f start len = true) (i : ℕ) (hlo : start ≤ i) (hhi : i < start + len) :
    f i = true := by
  induction len generalizing start with
  | zero => omega
  | succ len ih =>
    simp only [checkRange, Bool.and_eq_true] at h
    obtain ⟨hs, ht⟩ := h
    by_cases he : i = start
    · simpa [he] using hs
    · exact ih (start + 1) ht (by omega) (by omega)

theorem checkRange_add (f : ℕ → Bool) (start m n : ℕ) :
    checkRange f start (m + n) = (checkRange f start m && checkRange f (start + m) n) := by
  induction m generalizing start with
  | zero => simp [checkRange]
  | succ m ih =>
    simp only [Nat.succ_add, checkRange, ih, Bool.and_assoc]
    congr 2

theorem checked_all (f : ℕ → Bool) (n : ℕ) (h : checkRange f 0 n = true) :
    ∀ i : Fin n, f i.val = true := by
  intro i
  exact checkRange_sound f 0 n h i.val (Nat.zero_le _) (by omega)

theorem span_rows_of_inverse {n : ℕ} (xs ys : List ℕ) (hx : xs.length = n)
    (h : ∀ i : Fin n, packedRow (entry ys i.val) xs 0 = 2 ^ i.val) :
    Submodule.span (ZMod 2) (Set.range (matrix (n := n) xs)) = ⊤ := by
  have hm : matrix (n := n) ys * matrix xs = 1 := by
    funext i j
    have he := congrArg (fun v => v j) (vector_packedRow xs hx (entry ys i.val))
    rw [h i] at he
    simpa only [vector, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.val_inj,
      Matrix.mul_apply, vecMul, dotProduct, matrix, decide_eq_true_eq] using he.symm
  change Submodule.span (ZMod 2) (Set.range (matrix xs).row) = ⊤
  rw [← range_vecMulLinear, LinearMap.range_eq_top]
  intro v
  refine ⟨vecMul v (matrix ys), ?_⟩
  change vecMul (vecMul v (matrix ys)) (matrix xs) = v
  rw [vecMul_vecMul, hm, vecMul_one]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases
