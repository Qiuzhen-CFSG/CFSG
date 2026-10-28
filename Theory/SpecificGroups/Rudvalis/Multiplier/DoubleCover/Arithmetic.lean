module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Checked arithmetic for the Rudvalis covering matrices

Three-bit digits encode the entries of the degree-28 matrices over GF(5).
Natural-number dot products, reduced modulo five at the end, certify ordinary
matrix products. The proof follows the finite arithmetic checker in
`ONan.ProjectiveSimplicity.PrimeCoverage.Seven.MatrixCertificates.Checker`.
This module is independent of any recognition or covering assertion.
-/

namespace Rudvalis.Multiplier.DoubleCover
public section

abbrev Mat := Matrix (Fin 28) (Fin 28) (ZMod 5)

@[expose] def entryNat (packed i j : ℕ) : ℕ :=
  (packed >>> (3 * (28 * i + j))) % 8

@[expose] def decodeMatrix (packed : ℕ) : Mat :=
  fun i j => (entryNat packed i.val j.val : ℕ)

@[expose] def dotNat (f g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => dotNat f g k + f k * g k

@[expose] def checkAll (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => checkAll f n && f n

theorem checkAll_spec (f : ℕ → Bool) (n : ℕ) :
    checkAll f n = true ↔ ∀ i, i < n → f i = true := by
  induction n with
  | zero => simp [checkAll]
  | succ n ih =>
    rw [checkAll, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact h i hlt
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

theorem dotNat_cast (f g : ℕ → ℕ) (n : ℕ) :
    (dotNat f g n : ZMod 5) = ∑ k : Fin n, (f k.val : ZMod 5) * (g k.val : ZMod 5) := by
  induction n with
  | zero => simp [dotNat]
  | succ n ih =>
    rw [dotNat, Nat.cast_add, Nat.cast_mul, ih, Fin.sum_univ_castSucc]
    rfl

@[expose] def checkProduct (a b c : ℕ) : Bool :=
  checkAll (fun i => checkAll (fun j =>
    dotNat (entryNat a i) (fun k => entryNat b k j) 28 % 5 == entryNat c i j % 5) 28) 28

theorem checkProduct_sound (a b c : ℕ) (h : checkProduct a b c = true) :
    decodeMatrix a * decodeMatrix b = decodeMatrix c := by
  have hh := (checkAll_spec _ _).mp h
  apply Matrix.ext
  intro i j
  have hij := (checkAll_spec _ _).mp (hh i.val i.isLt) j.val j.isLt
  have hn : dotNat (entryNat a i.val) (fun k => entryNat b k j.val) 28 % 5 =
      entryNat c i.val j.val % 5 := by simpa only [beq_iff_eq] using hij
  have hc := congrArg (fun n : ℕ => (n : ZMod 5)) hn
  simp only [ZMod.natCast_mod] at hc
  change (∑ k : Fin 28, (entryNat a i.val k.val : ZMod 5) *
    (entryNat b k.val j.val : ZMod 5)) = (entryNat c i.val j.val : ZMod 5)
  rw [← dotNat_cast (entryNat a i.val) (fun k => entryNat b k j.val) 28]
  exact hc

end
end Rudvalis.Multiplier.DoubleCover
