module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.RowArithmetic

/-!
# Bounded row arithmetic for the degree-1000 orbit certificate

Leaves evaluate small sequential blocks using `RowArithmetic.combine`; nodes
join them using its XOR append identity. A checked tree is therefore just a
computational view of the original row list. Interval lemmas assemble small
kernel checks without repeating the alignment proof for each product.

The consumers are the literal row-orbit recurrences and inverse matrix below.
Source and ATLAS attribution: `RowSpan/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan
open RowArithmetic

inductive Tree where
  | leaf (rows : List ℕ)
  | node (size : ℕ) (left right : Tree)
def Tree.rows : Tree → List ℕ
  | .leaf rows => rows
  | .node _ l r => l.rows ++ r.rows
def Tree.valid : Tree → Bool
  | .leaf _ => true
  | .node n l r => decide (n = l.rows.length) && l.valid && r.valid
def Tree.product (mask : ℕ) : Tree → ℕ
  | .leaf rows => combine rows mask
  | .node n l r => l.product mask ^^^ r.product (mask >>> n)
theorem Tree.product_eq (t : Tree) (h : t.valid = true) (mask : ℕ) :
    t.product mask = combine t.rows mask := by
  induction t generalizing mask with
  | leaf rows => rfl
  | node n l r il ir =>
    simp only [Tree.valid, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Tree.product, Tree.rows, combine_append]
    rw [il h.1.2, ir h.2, h.1.1]

/-- A checked product of a computational tree acts by the original matrix. -/
theorem vecMul_of_tree (n : ℕ) (t : Tree) (rows : Array ℕ)
    (ht : t.valid = true) (ha : t.rows = rows.toList) (hn : rows.size = n)
    (x y : ℕ) (h : t.product x = y) :
    Matrix.vecMul (vector n x) (Thompson.BinaryMatrix.decode n rows) = vector n y := by
  have hc : combine rows.toList x = y := by
    rw [← ha, ← t.product_eq ht]
    exact h
  have hv := vector_combine rows.toList n n (by simpa using hn) x
  rw [matrix_toList] at hv
  exact hv.symm.trans (congrArg (vector n) hc)

/-- A predicate holds throughout a half-open interval of natural indices. -/
def On (lo hi : ℕ) (P : ℕ → Prop) : Prop := ∀ i, lo ≤ i → i < hi → P i

theorem On.of_fin {P : ℕ → Prop} (lo count : ℕ)
    (h : ∀ i : Fin count, P (lo + i.val)) : On lo (lo + count) P := by
  intro i hlo hhi
  have hlt : i - lo < count := by omega
  simpa only [Nat.add_sub_of_le hlo] using h ⟨i - lo, hlt⟩

theorem On.append {P : ℕ → Prop} {lo mid hi : ℕ}
    (h₁ : On lo mid P) (h₂ : On mid hi P) : On lo hi P := by
  intro i hlo hhi
  by_cases hm : i < mid
  · exact h₁ i hlo hm
  · exact h₂ i (by omega) hhi

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan
