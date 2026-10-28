module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Mathlib.Data.List.OfFn
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Packed multiplication for the degree-320 candidates

Sequential XOR of selected rows is matrix multiplication over the binary field.
This is the same elementary checker as the degree-160 Hall--Janko certificate,
adapted here with no dependency on its group or representation. The concrete
products serve the trace comparison of the ATLAS M24 degree-320 pair.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
open Thompson.BinaryMatrix

def row (a : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | b :: bs, k => (if a.testBit k then b else 0) ^^^ row a bs (k + 1)

theorem bit_row (n : ℕ) (f : Fin n → ℕ) (a j k : ℕ) :
    bit (row a (List.ofFn f) k) j = ∑ i, bit a (k + i.val) * bit (f i) j := by
  induction n generalizing k with
  | zero => simp [List.ofFn_zero, row, bit]
  | succ n ih =>
    rw [List.ofFn_succ, row, bit_xor, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    · cases h : a.testBit k <;> simp [bit, h]
    · apply Finset.sum_congr rfl
      intro i _
      simp [Nat.add_left_comm, Nat.add_comm]

theorem bit_row_array (n : ℕ) (b : Array ℕ) (hb : b.size = n) (a j : ℕ) :
    bit (row a b.toList 0) j = ∑ i : Fin n, bit a i.val * bit b[i.val]! j := by
  subst n
  have he : List.ofFn (fun i : Fin b.size => b[i.val]!) = b.toList := by
    conv_rhs => rw [← List.ofFn_get b.toList]
    congr 1
    funext i
    simp
  rw [← he, bit_row]
  simp only [Nat.zero_add]

def checkProduct (n : ℕ) (a b c : Array ℕ) : Bool :=
  (b.size == n) && (List.range n).all fun i => row a[i]! b.toList 0 == c[i]!

theorem product_sound (n : ℕ) (a b c : Array ℕ)
    (h : checkProduct n a b c = true) : decode n a * decode n b = decode n c := by
  simp only [checkProduct, Bool.and_eq_true] at h
  obtain ⟨hb, hh⟩ := h
  have hb' : b.size = n := of_decide_eq_true hb
  ext i j
  change (∑ k : Fin n, bit a[i.val]! k.val * bit b[k.val]! j.val) = bit c[i.val]! j.val
  rw [← bit_row_array n b hb']
  have hi : row a[i.val]! b.toList 0 = c[i.val]! :=
    of_decide_eq_true (List.all_eq_true.mp hh i.val (List.mem_range.mpr i.isLt))
  rw [hi]

/-- Consume successive bits by division by two. Testing bit k independently
would repeat k divisions at each step of the kernel computation. -/
def shiftRow (a : ℕ) : List ℕ → ℕ
  | [] => 0
  | b :: bs => (if a.testBit 0 then b else 0) ^^^ shiftRow (a / 2) bs

private theorem row_div_two (a : ℕ) (b : List ℕ) (k : ℕ) :
    row (a / 2) b k = row a b (k + 1) := by
  induction b generalizing k with
  | nil => rfl
  | cons x xs ih => simp only [row, Nat.testBit_div_two, ih]

theorem shiftRow_eq_row (a : ℕ) (b : List ℕ) : shiftRow a b = row a b 0 := by
  induction b generalizing a with
  | nil => rfl
  | cons x xs ih => rw [shiftRow, row, ih, row_div_two]

/-- Traverse the stored left and output rows directly, without indexed lookup. -/
def checkRows : List ℕ → List ℕ → List ℕ → Bool
  | [], _, [] => true
  | a :: as, b, c :: cs => (shiftRow a b == c) && checkRows as b cs
  | _, _, _ => false

theorem checkRows_get (a b c : List ℕ) (h : checkRows a b c = true)
    (i : ℕ) (hi : i < a.length) : shiftRow a[i]! b = c[i]! := by
  induction a generalizing c i with
  | nil => simp at hi
  | cons x xs ih =>
    cases c with
    | nil => simp [checkRows] at h
    | cons y ys =>
      simp only [checkRows, Bool.and_eq_true, beq_iff_eq] at h
      cases i with
      | zero => simpa using h.1
      | succ i => simpa using ih _ h.2 i (Nat.lt_of_succ_lt_succ hi)

theorem product_sound_list (n : ℕ) (a b c : List ℕ)
    (ha : a.length = n) (hb : b.length = n) (h : checkRows a b c = true) :
    decode n a.toArray * decode n b.toArray = decode n c.toArray := by
  apply product_sound
  simp only [checkProduct, Bool.and_eq_true]
  constructor
  · simp [hb]
  · apply List.all_eq_true.mpr
    intro i hi
    have hx := checkRows_get a b c h i (by simpa [ha] using List.mem_range.mp hi)
    simpa [shiftRow_eq_row] using hx

/-- The diagonal sum, reading the stored rows once. -/
def traceRows : List ℕ → ℕ → ZMod 2
  | [], _ => 0
  | a :: as, i => bit a i + traceRows as (i + 1)

theorem traceRows_ofFn (n : ℕ) (a : Fin n → ℕ) (k : ℕ) :
    traceRows (List.ofFn a) k = ∑ i, bit (a i) (k + i.val) := by
  induction n generalizing k with
  | zero => simp [List.ofFn_zero, traceRows]
  | succ n ih =>
    rw [List.ofFn_succ, traceRows, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp [Nat.add_left_comm, Nat.add_comm]

theorem trace_sound_list (n : ℕ) (a : List ℕ) (ha : a.length = n) :
    Matrix.trace (decode n a.toArray) = traceRows a 0 := by
  subst n
  have h := traceRows_ofFn a.length a.get 0
  rw [List.ofFn_get] at h
  simpa [decode, Matrix.trace] using h.symm

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
