module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.RowArithmetic

/-!
# Balanced bounded-block checks for the degree-1000 rank-one certificate

Every leaf uses `Large.RowArithmetic.combine`. The node theorem proves that
balanced evaluation is the same XOR combination of the flattened rows. The
literal table alignments are proved separately in `Blocks`. Division by a
power of two avoids repeatedly reducing a large shift count in the kernel.
The concrete vector consumers are in `Values`; the recurrence and inverse
certificates can share the same checked trees.

Source: R. A. Wilson et al., ATLAS HSG1-f2r1000B0, with attribution in
`Binary/source/README.md`. The balanced-tree proof follows this repository's
HS degree-1408 `Cyclicity/Spanning/Arithmetic.lean`; code is Apache-2.0.
-/

@[expose] public section
open Matrix Thompson.BinaryMatrix
open scoped BigOperators
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
open RowArithmetic

/-- A balanced organization of bounded sequential row blocks. -/
inductive RowTree where
  | leaf (rows : List ℕ)
  | node (leftSize : ℕ) (left right : RowTree)

def RowTree.rows : RowTree → List ℕ
  | .leaf rs => rs
  | .node _ l r => l.rows ++ r.rows

def RowTree.valid : RowTree → Bool
  | .leaf _ => true
  | .node n l r => decide (n = l.rows.length) && l.valid && r.valid

def RowTree.product (x : ℕ) : RowTree → ℕ
  | .leaf rs => combine rs x
  | .node n l r => l.product x ^^^ r.product (x / 2^n)

theorem RowTree.product_eq (t : RowTree) (ht : t.valid = true) (x : ℕ) :
    t.product x = combine t.rows x := by
  induction t generalizing x with
  | leaf rs => rfl
  | node n l r ihl ihr =>
    simp only [RowTree.valid, Bool.and_eq_true, decide_eq_true_eq] at ht
    simp only [RowTree.product, RowTree.rows, combine_append]
    rw [ihl ht.1.2, ihr ht.2, ht.1.1, Nat.shiftRight_eq_div_pow]

theorem RowTree.vecMul_of_product (t : RowTree) (ht : t.valid = true)
    (rs : Array ℕ) (halign : t.rows = rs.toList) (n : ℕ) (hs : rs.size = n)
    (x y : ℕ) (h : t.product x = y) :
    vecMul (vector n x) (decode n rs) = vector n y := by
  have he := vector_combine rs.toList n n (by simpa using hs) x
  rw [matrix_toList] at he
  rw [t.product_eq ht, halign] at h
  exact he.symm.trans (congrArg (vector n) h)

def RowTree.checkProducts (t : RowTree) : List (ℕ × ℕ) → Bool
  | [] => true
  | (x, y) :: pairs => decide (t.product x = y) && t.checkProducts pairs

theorem RowTree.checked_product (t : RowTree) (ps : List (ℕ × ℕ))
    (h : t.checkProducts ps = true) (x y : ℕ) (hp : (x,y) ∈ ps) :
    t.product x = y := by
  induction ps with
  | nil => simp at hp
  | cons p ps ih =>
    obtain ⟨a,b⟩ := p
    simp only [RowTree.checkProducts, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hp with he | he
    · cases he
      exact h.1
    · exact ih h.2 he

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
