module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Two

/-!
# Binary mask evaluation for extension certificates

Bit-vector masks encode linear combinations of binary coordinates. Evaluation
respects xor, finite sums, and substitution of masks, and the one-bit mask
selects its coordinate. These identities apply in arbitrary finite dimensions.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.Mask

/-- Evaluate the binary linear form encoded by a mask. -/
def evalRow {n : ℕ} (d : Fin n → ZMod 2) (v : BitVec n) : ZMod 2 :=
  ∑ i, if v.getLsbD i.val then d i else 0

theorem evalRow_zero {n : ℕ} (d : Fin n → ZMod 2) : evalRow d 0 = 0 := by
  simp [evalRow]

theorem evalRow_xor {n : ℕ} (d : Fin n → ZMod 2) (v w : BitVec n) :
    evalRow d (v ^^^ w) = evalRow d v + evalRow d w := by
  simp only [evalRow, BitVec.getLsbD_xor, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases v.getLsbD i.val <;> cases w.getLsbD i.val <;>
    simp [CharTwo.add_self_eq_zero]

private theorem evalRow_fold {m : ℕ} (d : Fin m → ZMod 2)
    (l : List (BitVec m)) :
    evalRow d (l.foldr (· ^^^ ·) 0) = (l.map (evalRow d)).sum := by
  induction l with
  | nil => exact evalRow_zero d
  | cons a l ih =>
    simp only [List.foldr_cons, evalRow_xor, ih, List.map_cons, List.sum_cons]

/-- The xor sum of a finite family of masks. -/
def sum {n m : ℕ} (rows : Fin n → BitVec m) : BitVec m :=
  (List.ofFn rows).foldr (· ^^^ ·) 0

theorem evalRow_sum {n m : ℕ} (d : Fin m → ZMod 2) (rows : Fin n → BitVec m) :
    evalRow d (sum rows) = ∑ i, evalRow d (rows i) := by
  rw [sum, evalRow_fold, List.map_ofFn, List.sum_ofFn]
  rfl

/-- Substitute a family of masks for the coordinates of a mask. -/
def substitute {n m : ℕ} (rows : Fin n → BitVec m) (v : BitVec n) : BitVec m :=
  (List.ofFn (fun i => if v.getLsbD i.val then rows i else 0)).foldr (· ^^^ ·) 0

theorem evalRow_substitute {n m : ℕ} (d : Fin m → ZMod 2)
    (rows : Fin n → BitVec m) (v : BitVec n) :
    evalRow d (substitute rows v) = evalRow (fun i => evalRow d (rows i)) v := by
  rw [substitute, evalRow_fold, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  change evalRow d (if v.getLsbD i.val then rows i else 0) =
    if v.getLsbD i.val then evalRow d (rows i) else 0
  cases v.getLsbD i.val
  · exact evalRow_zero d
  · rfl

/-- The mask with only coordinate `i` set. -/
def unit {n : ℕ} (i : Fin n) : BitVec n := BitVec.ofNat n (2 ^ i.val)

theorem evalRow_unit {n : ℕ} (d : Fin n → ZMod 2) (i : Fin n) :
    evalRow d (unit i) = d i := by
  simp only [evalRow, unit, BitVec.getLsbD_ofNat, Fin.isLt, decide_true,
    Bool.true_and, Nat.testBit_two_pow, ← Fin.ext_iff, decide_eq_true_eq]
  simp

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.Mask
