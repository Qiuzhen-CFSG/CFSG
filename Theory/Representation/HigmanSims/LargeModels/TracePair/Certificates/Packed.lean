module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Field
import Mathlib.Data.List.GetD
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed

/-!
# Sound packed arithmetic for the literal degree-896 matrix certificates

Each pair of natural numbers stores the coefficients of 1 and omega in a row.
This reuses the proved characteristic-two row operations of the J2 checker,
traversing a list once instead of repeatedly indexing its matrix array.
`entry_interleave` and `eval_eq_of_interleave` connect these two planes to the
exact two-bit encoding used by the ATLAS matrices in `TracePair.Data`.

The product and inverse theorems accept only numerical equalities that must be
checked in Lean. No externally computed result is trusted. See `source/README.md`
for the measured degree-896 row-product benchmark and remaining finite checks.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Packed

namespace Base
export Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed
  (Row addRow timesT entry entry_add entry_timesT entry_zero)
end Base

abbrev Row := Base.Row
abbrev Mat := List Row

def decode (a : Row) (i : ℕ) : Four := Base.entry omega a i

def interleave : ℕ → Row → ℕ
  | 0, _ => 0
  | n + 1, a => Nat.bit (a.1.testBit 0) (Nat.bit (a.2.testBit 0)
      (interleave n (a.1 >>> 1, a.2 >>> 1)))

private theorem decode_mk (a : Row) (i : ℕ) : decode a i =
    ⟨if a.1.testBit i then 1 else 0, if a.2.testBit i then 1 else 0⟩ := by
  unfold decode Base.entry
  unfold Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit
  cases a.1.testBit i <;> cases a.2.testBit i <;> decide +kernel

private theorem entry_bit_bit_succ (a b : Bool) (r i : ℕ) :
    TracePair.entry (Nat.bit a (Nat.bit b r)) (i + 1) = TracePair.entry r i := by
  simp only [TracePair.entry, Nat.mul_add, Nat.mul_one, Nat.testBit_bit_succ]

theorem entry_interleave (n : ℕ) (a : Row) (i : Fin n) :
    TracePair.entry (interleave n a) i.val = decode a i.val := by
  induction n generalizing a with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [decode_mk]
      simp only [interleave, TracePair.entry, Fin.val_zero, Nat.mul_zero, Nat.zero_add,
        Nat.testBit_bit_zero, Nat.testBit_bit_succ]
      rfl
    · rw [interleave, Fin.val_succ, entry_bit_bit_succ, ih, decode_mk, decode_mk]
      simp only [Nat.testBit_shiftRight, Nat.add_comm]

private theorem decode_selected (a b : Row) (k i : ℕ) :
    decode (Base.addRow (if a.1.testBit k then b else (0, 0))
      (if a.2.testBit k then Base.timesT b else (0, 0))) i = decode a k * decode b i := by
  rw [decode, Base.entry_add]
  cases h₀ : a.1.testBit k <;> cases h₁ : a.2.testBit k <;>
    simp only [Bool.false_eq_true, if_false, if_true,
      Base.entry_zero, Base.entry_timesT omega omega_sq]
  all_goals simp [decode, Base.entry,
    Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit,
    h₀, h₁, add_mul]

private theorem decode_add (a b : Row) (i : ℕ) :
    decode (Base.addRow a b) i = decode a i + decode b i := Base.entry_add omega a b i

def rowProductFrom (a : Row) : Mat → ℕ → Row
  | [], _ => (0, 0)
  | b :: bs, k => Base.addRow
      (Base.addRow (if a.1.testBit k then b else (0, 0))
        (if a.2.testBit k then Base.timesT b else (0, 0)))
      (rowProductFrom a bs (k + 1))

def rowProduct (a : Row) (b : Mat) : Row := rowProductFrom a b 0

private theorem decode_rowProductFrom (a : Row) (b : Mat) (k i : ℕ) :
    decode (rowProductFrom a b k) i =
      (b.mapIdx fun j r => decode a (k + j) * decode r i).sum := by
  induction b generalizing k with
  | nil => simp [rowProductFrom, decode]
  | cons b bs ih =>
    rw [rowProductFrom, decode_add, decode_selected, ih, List.mapIdx_cons, List.sum_cons]
    simp only [Nat.add_zero]
    simp only [Nat.add_assoc, Nat.add_comm 1]

theorem decode_rowProduct (a : Row) (b : Mat) (n : ℕ) (hb : b.length = n) (i : ℕ) :
    decode (rowProduct a b) i =
      ∑ j : Fin n, decode a j.val * decode (b.getD j.val (0, 0)) i := by
  subst n
  rw [rowProduct, decode_rowProductFrom]
  simp only [Nat.zero_add]
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp only [List.getElem_mapIdx, List.getElem_ofFn]
    simp only [List.length_mapIdx] at hj
    rw [List.getD_eq_getElem _ _ hj]

/-- Decode a matrix stored as a linear list of two-plane rows. -/
def eval (n : ℕ) (a : Mat) : Matrix (Fin n) (Fin n) Four :=
  fun i j => decode (a.getD i.val (0, 0)) j.val

theorem eval_product (n : ℕ) (a b c : Mat) (hb : b.length = n)
    (h : ∀ i : Fin n, rowProduct (a.getD i.val (0, 0)) b = c.getD i.val (0, 0)) :
    eval n a * eval n b = eval n c := by
  funext i j
  change (∑ k : Fin n, decode (a.getD i.val (0, 0)) k.val *
    decode (b.getD k.val (0, 0)) j.val) = _
  rw [← decode_rowProduct _ _ n hb, h]
  rfl

/-- A checked re-encoding connects packed arithmetic to the literal shared rows. -/
theorem eval_eq_of_interleave (n : ℕ) (a : Mat) (b : Array ℕ)
    (h : ∀ i : Fin n, interleave n (a.getD i.val (0, 0)) = b.getD i.val 0) :
    eval n a = fun i j : Fin n => TracePair.entry (b.getD i.val 0) j.val := by
  funext i j
  change decode (a.getD i.val (0, 0)) j.val = _
  rw [← entry_interleave n _ j, h]

private theorem decode_power (i j : ℕ) :
    decode (2 ^ i, 0) j = if i = j then 1 else 0 := by
  simp [decode, Base.entry,
    Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit,
    Nat.testBit_two_pow]

theorem eval_inverse (n : ℕ) (a b : Mat) (hb : b.length = n)
    (h : ∀ i : Fin n, rowProduct (a.getD i.val (0, 0)) b = (2 ^ i.val, 0)) :
    eval n a * eval n b = 1 := by
  funext i j
  change (∑ k : Fin n, decode (a.getD i.val (0, 0)) k.val *
    decode (b.getD k.val (0, 0)) j.val) = _
  rw [← decode_rowProduct _ _ n hb, h, decode_power]
  simp only [Matrix.one_apply, Fin.val_inj]

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Packed
