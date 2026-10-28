module

public import Theory.SpecificGroups.Held.Model.Basic
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphData
public import Mathlib.Data.Nat.Bits
/-!
# Soundness of the Held generator certificates

A balanced tree records the input bit for each output position. Its numeric
value packs those bits, using 32-bit chunks so large division is shared across
nearby input bits. The bit theorem proves the exact connection to `Nat.testBit`;
the final lemma turns whole-row equalities into membership of the full
relation-preserving subgroup. No property of Held is assumed in this lemma.

The concrete trees and row equalities use the retained ATLAS permutations and
`Normalizer/Source/generate_graph.py`, supporting the normalizer argument for
GLS3 Table 5.3p.
-/

namespace Held.NormalizerGraph.Orbital.GeneratorInvariance

public section

@[expose] def radix : ℕ → ℕ
  | 0 => 2
  | d+1 => radix d * radix d

theorem radix_eq (d : ℕ) : radix d = 2 ^ (2^d) := by
  induction d with
  | zero => rfl
  | succ d ih => rw [radix, ih, ← pow_add, pow_succ]; congr 1; omega

inductive Weights : ℕ → Type
  | leaf (w : ℕ) : Weights 0
  | node {d : ℕ} (l r : Weights d) : Weights (d+1)

@[expose] def sample (m i : ℕ) : ℕ := m / 2^(i/32*32) % 2^32 / 2^(i%32) % 2

theorem sample_spec (m i : ℕ) : decide (sample m i = 1) = m.testBit i := by
  unfold sample
  rw [← Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  have h : i % 32 < 32 := Nat.mod_lt _ (by decide)
  simp only [h, decide_true, Bool.true_and]
  congr 1
  omega

@[expose] def packed : {d : ℕ} → Weights d → ℕ → ℕ
  | 0, .leaf w, m => sample m w
  | d+1, .node l r, m => packed l m + radix d * packed r m

@[expose] def weightAt : {d : ℕ} → Weights d → ℕ → ℕ
  | 0, .leaf w, _ => w
  | d+1, .node l r, i => if i < 2^d then weightAt l i else weightAt r (i-2^d)

theorem packed_lt {d : ℕ} (w : Weights d) (m : ℕ) : packed w m < 2^(2^d) := by
  induction w with
  | leaf w => exact Nat.mod_lt _ (by decide)
  | @node d l r ihl ihr =>
    rw [packed, ← radix_eq, radix]
    rw [← radix_eq] at ihl ihr
    calc
      _ < radix d + radix d * packed r m := Nat.add_lt_add_right ihl _
      _ = radix d * (packed r m + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ ihr

theorem packed_testBit {d : ℕ} (w : Weights d) (m i : ℕ) (hi : i < 2^d) :
    (packed w m).testBit i = decide (sample m (weightAt w i) = 1) := by
  induction w generalizing i with
  | leaf w =>
    have he : i = 0 := by simpa using hi
    subst i
    simp only [packed, weightAt, sample, Nat.testBit_eq_decide_div_mod_eq, pow_zero,
      Nat.div_one, Nat.mod_mod]
    rfl
  | @node d l r ihl ihr =>
    rw [packed, radix_eq, Nat.add_comm,
      Nat.testBit_two_pow_mul_add _ (packed_lt l m), weightAt]
    split
    next hil => exact ihl i hil
    next hil => exact ihr (i-2^d) (by rw [pow_succ] at hi; omega)

theorem preserve (g : Equiv.Perm (Fin 2058)) (w : Weights 12)
    (hw : ∀ y : Fin 2058, weightAt w y.val = (g y).val)
    (hc : ∀ x, packed w (rowMask (g x)) = rowMask x) : g ∈ preservingGroup := by
  intro x y
  have ht := packed_testBit w (rowMask (g x)) y.val (by omega)
  rw [hc x, hw y] at ht
  rw [sample_spec] at ht
  exact (Bool.eq_iff_iff.mp ht).symm

end

end Held.NormalizerGraph.Orbital.GeneratorInvariance
