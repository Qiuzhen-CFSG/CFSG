module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.SpanningInput

/-!
# Balanced evaluation of packed binary combinations

A balanced tree is a computational view of a row list. Checked subtree sizes
and the XOR append identity prove that its product equals `listProduct`.
Small kernel-checked batches then certify coverage of coordinate intervals;
adjacent intervals combine to give the exact packed spanning contract.
This module uses only elementary XOR arithmetic; the concrete application
and source data are documented in `Spanning/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning

inductive RowTree where
  | leaf (rows : List Nat)
  | node (leftSize : Nat) (left right : RowTree)

def RowTree.rows : RowTree → List Nat
  | .leaf rs => rs
  | .node _ l r => l.rows ++ r.rows

def RowTree.valid : RowTree → Bool
  | .leaf _ => true
  | .node n l r => decide (n = l.rows.length) && l.valid && r.valid

def RowTree.product (x start : Nat) : RowTree → Nat
  | .leaf rs => PackedBinaryRows.listProduct x start rs
  | .node n l r => l.product x start ^^^ r.product x (start + n)

lemma listProduct_append (x start : Nat) (as bs : List Nat) :
    PackedBinaryRows.listProduct x start (as ++ bs) =
      PackedBinaryRows.listProduct x start as ^^^
        PackedBinaryRows.listProduct x (start + as.length) bs := by
  induction as generalizing start with
  | nil => simp [PackedBinaryRows.listProduct]
  | cons a as ih =>
    simp only [List.cons_append, PackedBinaryRows.listProduct, List.length_cons]
    rw [ih, Nat.xor_assoc]
    rw [show start + 1 + as.length = start + (as.length + 1) by omega]

lemma RowTree.product_eq (t : RowTree) (h : t.valid = true) (x start : Nat) :
    t.product x start = PackedBinaryRows.listProduct x start t.rows := by
  induction t generalizing start with
  | leaf rs => rfl
  | node n l r il ir =>
    simp only [RowTree.valid, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [RowTree.product, RowTree.rows, listProduct_append]
    rw [il h.1.2, ir h.2, h.1.1]

def treeChecks (t : RowTree) (start : Nat) : List Nat → Bool
  | [] => true
  | c :: cs => decide (t.product c 0 = 2 ^ start) && treeChecks t (start + 1) cs

/-- Coverage by explicit binary combinations on a half-open coordinate interval. -/
def Covers (rows : List Nat) (lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i → i < hi → ∃ c, PackedBinaryRows.listProduct c 0 rows = 2 ^ i

lemma covers_of_treeChecks (t : RowTree) (ht : t.valid = true)
    (start : Nat) (cs : List Nat) (h : treeChecks t start cs = true) :
    Covers t.rows start (start + cs.length) := by
  induction cs generalizing start with
  | nil =>
    intro i hlo hhi
    simp only [List.length_nil, Nat.add_zero] at hhi
    omega
  | cons c cs ih =>
    simp only [treeChecks, Bool.and_eq_true, decide_eq_true_eq] at h
    intro i hlo hhi
    by_cases hi : i = start
    · refine ⟨c, ?_⟩
      rw [← t.product_eq ht c 0, hi]
      exact h.1
    · apply ih (start + 1) h.2 i
      · omega
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 cs.length] using hhi

lemma Covers.append {rows : List Nat} {lo mid hi : Nat}
    (h₁ : Covers rows lo mid) (h₂ : Covers rows mid hi) : Covers rows lo hi := by
  intro i hlo hhi
  by_cases hm : i < mid
  · exact h₁ i hlo hm
  · exact h₂ i (by omega) hhi

lemma packedSpanning_of_covers (rows : Array Nat) (h : Covers rows.toList 0 1408) :
    PackedSpanning rows := fun i => h i.val (Nat.zero_le _) i.isLt

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning
