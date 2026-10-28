module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Indexes
/-!
# Carry-free arithmetic for 45-dimensional matrices over GF(7)

A row is a natural number in base 2048, least significant entry first.
`Good` says that its 45 digits are canonical residues modulo seven.
A weighted sum of 45 rows has digits at most 45 * 6 * 6 = 1620;
there are therefore no carries between columns. Reduction modulo seven
of each digit gives ordinary matrix multiplication (`decode_packedMul`).

This adapts the natural-number certificate principle of
`Lyons.Atlas111Arithmetic` and the row-product interface of
`Thompson.Model.GeneratorCertificates.BinaryMatrix`. Numerical data are
untrusted: every use passes through these proved decoding theorems.
-/

open scoped BigOperators

namespace ONan.OrderCertificate.UpperBound.Packed

/-- Encode a row, allowing unreduced natural coefficients. -/
@[expose] public def pack {n : ℕ} (v : Fin n → ℕ) : ℕ := Nat.ofDigits 2048 (List.ofFn v)

/-- Extract an unreduced base-2048 digit. -/
@[expose] public def digit (a j : ℕ) : ℕ := a / 2048 ^ j % 2048

public theorem digit_pack {n : ℕ} (v : Fin n → ℕ) (hv : ∀ j, v j < 2048)
  (j : Fin n) : digit (pack v) j.val = v j := by
  unfold digit pack
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop]
  · rw [Nat.ofDigits_mod_eq_head!]
    simp [List.head!_eq_head?_getD, Nat.mod_eq_of_lt (hv j)]
  · decide
  · simpa using hv

public theorem pack_sum {n m : ℕ} (v : Fin m → Fin n → ℕ) :
  pack (fun j => ∑ k, v k j) = ∑ k, pack (v k) := by
  simp only [pack, Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn, List.length_ofFn, List.get_ofFn, List.sum_ofFn]
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

public theorem pack_mul {n : ℕ} (c : ℕ) (v : Fin n → ℕ) :
  pack (fun j => c * v j) = c * pack v := by
  simp only [pack, Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.length_ofFn,
    List.get_ofFn, List.sum_ofFn, Finset.mul_sum, mul_assoc]
  rfl

/-- Decode one digit modulo seven. -/
@[expose] public def entry (a j : ℕ) : ℕ := digit a j % 7

/-- Interpret the first 45 rows and columns over GF(7). -/
@[expose] public def decode (A : Array ℕ) : Matrix (Fin 45) (Fin 45) (ZMod 7) :=
  fun i j => (entry A[i.val]! j.val : ZMod 7)

/-- The stored rows consist of exactly 45 canonical GF(7) digits. -/
@[expose] public def Good (A : Array ℕ) : Prop :=
  ∀ i : Fin 45, A[i.val]! = pack (fun j : Fin 45 => entry A[i.val]! j.val)

/-- Accumulate all columns simultaneously, before reduction modulo seven. -/
@[expose] public def rowProduct (a : ℕ) (B : Array ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => rowProduct a B k + entry a k * B[k]!

public theorem rowProduct_eq (a : ℕ) (B : Array ℕ) (n : ℕ) :
  rowProduct a B n = ∑ k : Fin n, entry a k.val * B[k.val]! := by
  induction n with
  | zero => simp [rowProduct]
  | succ n ih => simp [rowProduct, ih, Fin.sum_univ_castSucc]

public theorem rowProduct_pack (a : ℕ) (B : Array ℕ) (hB : Good B) :
  rowProduct a B 45 = pack (fun j : Fin 45 =>
  ∑ k : Fin 45, entry a k.val * entry B[k.val]! j.val) := by
  rw [rowProduct_eq, pack_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [pack_mul, ← hB k]

public theorem digit_rowProduct (a : ℕ) (B : Array ℕ) (hB : Good B) (j : Fin 45) :
  digit (rowProduct a B 45) j.val =
  ∑ k : Fin 45, entry a k.val * entry B[k.val]! j.val := by
  rw [rowProduct_pack a B hB]
  apply digit_pack
  intro j
  have h : (∑ k : Fin 45, entry a k.val * entry B[k.val]! j.val) ≤ 45 * 36 := by
    calc
      _ ≤ ∑ _k : Fin 45, 36 := by
        apply Finset.sum_le_sum
        intro k _
        have ha : entry a k.val ≤ 6 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
        have hb : entry B[k.val]! j.val ≤ 6 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
        exact Nat.mul_le_mul ha hb
      _ = _ := by simp
  omega

/-- Reduce all 45 digits modulo seven and repack. -/
@[expose] public def reduceRow (a : ℕ) : ℕ := pack (fun j : Fin 45 => entry a j.val)

public theorem entry_reduceRow (a : ℕ) (j : Fin 45) :
  entry (reduceRow a) j.val = entry a j.val := by
  simp only [entry, reduceRow]
  rw [digit_pack _ (fun _ => lt_trans (Nat.mod_lt _ (by decide)) (by decide))]
  exact Nat.mod_mod ..

/-- Check one full row of a proposed product. -/
@[expose] public def checkRow (A B C : Array ℕ) (i : Fin 45) : Bool :=
  reduceRow (rowProduct A[i.val]! B 45) == C[i.val]!

public theorem mul_sound (A B C : Array ℕ) (hB : Good B)
  (h : ∀ i, checkRow A B C i = true) : decode A * decode B = decode C := by
  ext i j
  have hi := h i
  simp only [checkRow, beq_iff_eq] at hi
  change (∑ k : Fin 45, (entry A[i.val]! k.val : ZMod 7) *
  (entry B[k.val]! j.val : ZMod 7)) = (entry C[i.val]! j.val : ZMod 7)
  rw [← hi, entry_reduceRow]
  unfold entry
  rw [ZMod.natCast_mod, digit_rowProduct _ _ hB, Nat.cast_sum]
  simp only [Nat.cast_mul]
  rfl

public theorem get_ofFn (f : Fin 45 → ℕ) (i : Fin 45) : (Array.ofFn f)[i.val]! = f i := by
  simp [i.isLt]

public theorem good_reduced (f : Fin 45 → ℕ) : Good (Array.ofFn (fun i => reduceRow (f i))) := by
  intro i
  simp only [get_ofFn, entry_reduceRow]
  rfl

/-- Executable matrix multiplication, sound when the right matrix is canonical. -/
@[expose] public def packedMul (A B : Array ℕ) : Array ℕ :=
  Array.ofFn (fun i : Fin 45 => reduceRow (rowProduct A[i.val]! B 45))

public theorem decode_packedMul (A B : Array ℕ) (hB : Good B) :
  decode (packedMul A B) = decode A * decode B := by
  symm
  apply mul_sound A B _ hB
  intro i
  simp only [checkRow, packedMul, get_ofFn, beq_self_eq_true]

public theorem good_packedMul (A B : Array ℕ) : Good (packedMul A B) := good_reduced _

@[expose] public def encodeMatrix (M : Matrix (Fin 45) (Fin 45) (ZMod 7)) : Array ℕ :=
  Array.ofFn (fun i => pack (fun j => (M i j).val))

public theorem decode_encodeMatrix (M : Matrix (Fin 45) (Fin 45) (ZMod 7)) :
  decode (encodeMatrix M) = M := by
  ext i j
  change (entry (encodeMatrix M)[i.val]! j.val : ZMod 7) = M i j
  rw [encodeMatrix, get_ofFn]
  unfold entry
  rw [digit_pack _ (fun j => lt_trans (ZMod.val_lt (M i j)) (by decide))]
  simp only [ZMod.natCast_mod, ZMod.natCast_zmod_val]

public theorem good_encodeMatrix (M : Matrix (Fin 45) (Fin 45) (ZMod 7)) : Good (encodeMatrix M) := by
  intro i
  simp only [encodeMatrix, get_ofFn]
  congr 1
  funext j
  unfold entry
  rw [digit_pack _ (fun j => lt_trans (ZMod.val_lt (M i j)) (by decide))]
  exact (Nat.mod_eq_of_lt (ZMod.val_lt (M i j))).symm
end ONan.OrderCertificate.UpperBound.Packed
