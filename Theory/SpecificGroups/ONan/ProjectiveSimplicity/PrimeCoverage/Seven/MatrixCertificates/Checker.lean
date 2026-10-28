module

public import Theory.SpecificGroups.ONan.MatrixData
public import Mathlib.Algebra.BigOperators.Fin
/-!
# Sound finite arithmetic checks for the seven-subgroup matrices

Base-eight digits encode entries in GF(7). A Boolean checker computes ordinary
natural-number dot products, reducing modulo seven only at the end. Induction
identifies these computations with matrix multiplication, so kernel reduction
of a Boolean equality certifies each complete matrix product.

The Boolean finite-check pattern follows the project's Thompson `RowCheck`;
the present arithmetic is for GF(7), not binary matrices.
-/

namespace ONan.Simplicity.Seven.Certificate
@[expose] public def entryNat (packed i j : ℕ) : ℕ :=
  (packed >>> (3 * (45 * i + j))) % 8
@[expose] public def decodeMatrix (packed : ℕ) : Matrix (Fin 45) (Fin 45) (ZMod 7) :=
  fun i j => (entryNat packed i.val j.val : ℕ)
@[expose] public def dotNat (f g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => dotNat f g k + f k * g k
@[expose] public def checkAll (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => checkAll f n && f n

public theorem checkAll_spec (f : ℕ → Bool) (n : ℕ) :
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

public theorem dotNat_cast (f g : ℕ → ℕ) (n : ℕ) :
    (dotNat f g n : ZMod 7) = ∑ k : Fin n, (f k.val : ZMod 7) * (g k.val : ZMod 7) := by
  induction n with
  | zero => simp [dotNat]
  | succ n ih =>
    rw [dotNat, Nat.cast_add, Nat.cast_mul, ih, Fin.sum_univ_castSucc]
    rfl

@[expose] public def checkProduct (a b c : ℕ) : Bool :=
  checkAll (fun i => checkAll (fun j =>
    dotNat (entryNat a i) (fun k => entryNat b k j) 45 % 7 == entryNat c i j % 7) 45) 45

public theorem checkProduct_sound (a b c : ℕ) (h : checkProduct a b c = true) :
    decodeMatrix a * decodeMatrix b = decodeMatrix c := by
  have hh := (checkAll_spec _ _).mp h
  apply Matrix.ext
  intro i j
  have hij := (checkAll_spec _ _).mp (hh i.val i.isLt) j.val j.isLt
  have hn : dotNat (entryNat a i.val) (fun k => entryNat b k j.val) 45 % 7 =
      entryNat c i.val j.val % 7 := by simpa only [beq_iff_eq] using hij
  have hc := congrArg (fun n : ℕ => (n : ZMod 7)) hn
  simp only [ZMod.natCast_mod] at hc
  change (∑ k : Fin 45, (entryNat a i.val k.val : ZMod 7) *
    (entryNat b k.val j.val : ZMod 7)) = (entryNat c i.val j.val : ZMod 7)
  rw [← dotNat_cast (entryNat a i.val) (fun k => entryNat b k j.val) 45]
  exact hc
end ONan.Simplicity.Seven.Certificate
