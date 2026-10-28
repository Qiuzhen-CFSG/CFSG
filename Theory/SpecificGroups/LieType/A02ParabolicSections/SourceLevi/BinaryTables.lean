module
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
import Mathlib.Tactic

/-!
# Compact checks of integral matrices modulo two

Pack a finite integral row by XOR of the positions of its odd entries.
Induction on the row length proves that every decoded bit is the original
entry modulo two. Equality of the packed rows therefore identifies the
whole reduced matrix, without expanding a separate large expression for
every pair of indices. The exceptional Levi producers apply this to their
actual integral Geck tables before using the binary word certificates.

Source: elementary matrix reduction modulo two; GLS3 §1.12 for its use
in the integral root-curve construction.
-/

@[expose] public section
namespace Theory.SpecificGroups.LieType.SourceLevi.BinaryTables
open Thompson.BinaryMatrix
variable {n : ℕ}

def rowCode (f : Fin n → ℤ) : ℕ → ℕ
  | 0 => 0
  | k+1 => rowCode f k ^^^
      (if h : k < n then if f ⟨k,h⟩ % 2 = 1 then 2 ^ k else 0 else 0)

private theorem single_bit (f : Fin n → ℤ) (k : ℕ) (j : Fin n) :
    bit (if h : k < n then if f ⟨k,h⟩ % 2 = 1 then 2 ^ k else 0 else 0) j.val =
      if j.val = k then (f j : ZMod 2) else 0 := by
  by_cases hk : k < n
  · rw [dif_pos hk]
    by_cases hj : j.val = k
    · have he : j = ⟨k,hk⟩ := Fin.ext hj
      subst j
      have hv : (f ⟨k,hk⟩ : ZMod 2) = ((f ⟨k,hk⟩ % 2 : ℤ) : ZMod 2) :=
        (ZMod.intCast_mod _ 2).symm
      rcases Int.emod_two_eq_zero_or_one (f ⟨k,hk⟩) with h | h <;>
        simp [bit, h, hv]
    · have hne : k ≠ j.val := Ne.symm hj
      by_cases he : f ⟨k,hk⟩ % 2 = 1 <;>
        simp [bit, he, hj, hne]
  · rw [dif_neg hk]
    have hj : j.val ≠ k := by intro h; exact hk (h ▸ j.isLt)
    simp [bit, hj]

theorem bit_rowCode (f : Fin n → ℤ) (k : ℕ) (j : Fin n) :
    bit (rowCode f k) j.val = if j.val < k then (f j : ZMod 2) else 0 := by
  induction k with
  | zero => simp [rowCode, bit]
  | succ k ih =>
    rw [rowCode, bit_xor, ih, single_bit]
    by_cases hlt : j.val < k
    · have hne : j.val ≠ k := ne_of_lt hlt
      simp [hlt, hne, Nat.lt_succ_of_lt hlt]
    · by_cases heq : j.val = k
      · simp [heq]
      · have hnot : ¬ j.val < k+1 := by omega
        simp [hlt, heq, hnot]

theorem cast_matrix_eq_decode (A : Matrix (Fin n) (Fin n) ℤ) (rows : Array ℕ)
    (h : ∀ r : Fin n, rowCode (A r) n = rows[r.val]!) :
    A.map (Int.castRingHom (ZMod 2)) = decode n rows := by
  ext r c
  change (A r c : ZMod 2) = bit rows[r.val]! c.val
  rw [← h, bit_rowCode, if_pos c.isLt]

end Theory.SpecificGroups.LieType.SourceLevi.BinaryTables
