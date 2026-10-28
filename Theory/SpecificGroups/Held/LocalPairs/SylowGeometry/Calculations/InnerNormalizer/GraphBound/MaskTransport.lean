module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.GraphTable

/-!
# Checking graph transport one packed row at a time

Pull back a binary row along a permutation and compare the resulting natural
number with the original row. The bit lemma turns this single equality into
all adjacency equivalences in that row. This avoids repeatedly looking up both
large graph rows in an all-pairs decision procedure.

Source context: the literal ATLAS Held relation used in GLS3 Table 5.3p.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound
open Held.NormalizerGraph

@[expose] public def pullMask (p : ℕ → ℕ) (mask : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => pullMask p mask n ||| (if mask.testBit (p n) then 2^n else 0)

private theorem pullMask_bit (p : ℕ → ℕ) (mask n k : ℕ) :
    (pullMask p mask n).testBit k = (decide (k < n) && mask.testBit (p k)) := by
  induction n with
  | zero => simp [pullMask]
  | succ n ih =>
    rw [pullMask, Nat.testBit_or, ih]
    have he : (if mask.testBit (p n) then 2^n else 0).testBit k =
        (decide (k = n) && mask.testBit (p n)) := by
      cases mask.testBit (p n) <;> simp [Nat.testBit_two_pow, eq_comm]
    rw [he]
    by_cases hkn : k = n
    · subst k
      simp
    · have hh : k < n + 1 ↔ k < n := by omega
      simp only [hkn, decide_false, Bool.false_and, Bool.or_false, hh]

public theorem checked_graph_mask (σ : Equiv.Perm (Fin 2058)) (lo hi : ℕ)
    (h : ∀ x : Fin 2058, lo ≤ x.val → x.val < hi →
      pullMask (fun i => (σ (vertex i)).val) (fastRow (σ x)) 2058 = fastRow x) :
    ∀ x : Fin 2058, lo ≤ x.val → x.val < hi → ∀ y,
      Adj (σ x) (σ y) ↔ Adj x y := by
  intro x hl hu y
  have hb := congrArg (fun m : ℕ => m.testBit y.val) (h x hl hu)
  rw [pullMask_bit] at hb
  have hy : vertex y.val = y := Fin.ext (Nat.mod_eq_of_lt y.isLt)
  simp only [y.isLt, decide_true, Bool.true_and, hy] at hb
  rw [adj_iff_fast, adj_iff_fast, hb]

end Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound
