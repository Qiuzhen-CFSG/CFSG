module
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Binary
public import Mathlib.Data.List.OfFn

/-!
# Sequential packed-row multiplication for the degree-160 certificates

Reading the right matrix as a list avoids a fresh indexed lookup at each
summand. The proof identifies the XOR recursion with the usual matrix product
over `ZMod 2`; every concrete certificate is checked by the kernel.
This is used for the ATLAS J2G1-f2r160B0 data in `../source/README.md`.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty
open Thompson.BinaryMatrix

def row (a : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | b :: bs, k => (if a.testBit k then b else 0) ^^^ row a bs (k+1)

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

def checkInverse (n : ℕ) (a b : Array ℕ) : Bool :=
  (b.size == n) && (List.range n).all fun i => row a[i]! b.toList 0 == 2 ^ i

theorem inverse_sound (n : ℕ) (a b : Array ℕ)
    (h : checkInverse n a b = true) : decode n a * decode n b = 1 := by
  simp only [checkInverse, Bool.and_eq_true] at h
  obtain ⟨hb, hh⟩ := h
  have hb' : b.size = n := of_decide_eq_true hb
  ext i j
  change (∑ k : Fin n, bit a[i.val]! k.val * bit b[k.val]! j.val) = _
  rw [← bit_row_array n b hb']
  have hi : row a[i.val]! b.toList 0 = 2 ^ i.val :=
    of_decide_eq_true (List.all_eq_true.mp hh i.val (List.mem_range.mpr i.isLt))
  rw [hi]
  simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

def checkOne (n : ℕ) (a : Array ℕ) : Bool :=
  (List.range n).all fun i => a[i]! == 2 ^ i

theorem one_sound (F : Type*) [Field F] [CharP F 2] (n : ℕ) (a : Array ℕ)
    (h : checkOne n a = true) : Binary.eval F n a = 1 := by
  ext i j
  have hi : a[i.val]! = 2 ^ i.val :=
    of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  simp [Binary.eval_apply, hi, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

def checkSum (n : ℕ) (as : List (Array ℕ)) (c : Array ℕ) : Bool :=
  (List.range n).all fun i =>
    ((as.map fun a => a[i]!).foldr Nat.xor 0) == c[i]!

theorem bit_sum (xs : List ℕ) (j : ℕ) :
    bit (xs.foldr Nat.xor 0) j = (xs.map fun x => bit x j).sum := by
  induction xs with
  | nil => simp [bit]
  | cons x xs ih => simp [bit_xor, ih]

theorem sum_sound (F : Type*) [Field F] [CharP F 2] (n : ℕ)
    (as : List (Array ℕ)) (c : Array ℕ) (h : checkSum n as c = true) :
    (as.map (Binary.eval F n)).sum = Binary.eval F n c := by
  ext i j
  have hi : ((as.map fun a => a[i.val]!).foldr Nat.xor 0) = c[i.val]! :=
    of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  have he := congrArg (fun x => ZMod.castHom (dvd_refl 2) F (bit x j.val)) hi
  rw [bit_sum, map_list_sum, List.map_map, List.map_map] at he
  convert he using 1
  · clear h hi he
    induction as with
    | nil => rfl
    | cons a as ih => simp only [List.map_cons, List.sum_cons, Matrix.add_apply, ih]; rfl
  · rfl

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty
