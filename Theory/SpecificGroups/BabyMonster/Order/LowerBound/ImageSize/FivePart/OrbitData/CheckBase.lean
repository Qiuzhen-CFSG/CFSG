module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.FivePart.OrbitData.Tables
public import Mathlib.Data.BitVec

/-!
# Finite checks for the five-part orbit

The first 64 coordinates distinguish all points, as certified by a left inverse.
The two forward tables have explicit inverses. The breadth-first parent table
strictly decreases away from zero and its labelled edges are table transitions.
The block checks are reduced by the Lean kernel in the `CheckPart` modules.
-/

@[expose] public section
namespace BabyMonster.OrderLowerBound.FivePart.OrbitTables

def checkFin {n : ℕ} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i, h⟩ else true)

private theorem allFin {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt, decide_eq_true_eq] using hi

def signature (i : Fin 15625) : BitVec 64 := BitVec.ofNat 64 (signatureNat i)

def forward (j : Fin 2) (i : Fin 15625) : Fin 15625 :=
  ⟨(if j.val = 0 then forward0 i else forward1 i) % 15625, Nat.mod_lt _ (by decide)⟩

def backward (j : Fin 2) (i : Fin 15625) : Fin 15625 :=
  ⟨(if j.val = 0 then backward0 i else backward1 i) % 15625, Nat.mod_lt _ (by decide)⟩

def parent (i : Fin 15625) : Fin 15625 :=
  ⟨parentNat i % 15625, Nat.mod_lt _ (by decide)⟩

def edge (i : Fin 15625) : Fin 2 :=
  ⟨edgeNat i % 2, Nat.mod_lt _ (by decide)⟩

def blockIndex (b : ℕ) (k : Fin 64) : Fin 15625 :=
  ⟨(b * 64 + k.val) % 15625, Nat.mod_lt _ (by decide)⟩
def entryCheck (i : Fin 15625) : Prop :=
  signatureIndex (signature i).toNat = i.val ∧
  backward 0 (forward 0 i) = i ∧ forward 0 (backward 0 i) = i ∧
  backward 1 (forward 1 i) = i ∧ forward 1 (backward 1 i) = i ∧
  (i ≠ 0 → (parent i).val < i.val ∧ forward (edge i) (parent i) = i)
instance (i : Fin 15625) : Decidable (entryCheck i) := inferInstanceAs (Decidable (_ ∧ _))
def checkBlock (b : ℕ) : Bool := checkFin (fun k => decide (entryCheck (blockIndex b k)))

/-- Every finite ordinal index occurs in a checked block. -/
theorem entryCheck_of_blocks
    (h : ∀ b : Fin 245, checkBlock b.val = true) : ∀ i, entryCheck i := by
  intro i
  let b : Fin 245 := ⟨i.val / 64, by have := i.isLt; omega⟩
  let k : Fin 64 := ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  have hi : blockIndex b.val k = i := by
    apply Fin.ext
    simp only [blockIndex, b, k]
    have he : i.val / 64 * 64 + i.val % 64 = i.val := by omega
    rw [he, Nat.mod_eq_of_lt i.isLt]
  have hc : ∀ k, entryCheck (blockIndex b.val k) := allFin _ (h b)
  simpa only [hi] using hc k

end BabyMonster.OrderLowerBound.FivePart.OrbitTables
