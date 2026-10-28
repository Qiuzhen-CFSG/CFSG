module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.Checks

/-!
# Bounded checks of the saved HS row products

The coefficient at position k is selected by division by 2^k. This avoids
repeated single-bit shifts during kernel reduction. The induction below proves
that the result is exactly the published packed product, without changing any
row, parent, letter, or field convention. Small consecutive ranges let the
numerical certificates run sequentially with bounded reduction caches.

Source: `Certificates/source/witnesses.json.gz` and its accompanying README.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.RowChecks

def directProductFrom (a : Packed.Row) : Packed.Mat → ℕ → Packed.Row
  | [], _ => (0, 0)
  | b :: bs, k => Packed.Base.addRow
      (Packed.Base.addRow (if a.1 / 2^k % 2 = 1 then b else (0, 0))
        (if a.2 / 2^k % 2 = 1 then Packed.Base.timesT b else (0, 0)))
      (directProductFrom a bs (k + 1))

theorem directProductFrom_eq (a : Packed.Row) (bs : Packed.Mat) (k : ℕ) :
    directProductFrom a bs k = Packed.rowProductFrom a bs k := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih =>
    simp only [directProductFrom, Packed.rowProductFrom, ih,
      Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]

def inverseAt (i : ℕ) : Bool :=
  directProductFrom (rowInverseRows.getD i (0, 0)) rowRows 0 == (2^i, 0)

def recursionAt (i : ℕ) : Bool :=
  directProductFrom (rowRows.getD (rowParents.getD i 0) (0, 0))
    (packedLetter (rowLetters.getD i 0)) 0 == rowRows.getD (i + 1) (0, 0)

def checkRange (f : ℕ → Bool) (start count : ℕ) : Bool :=
  (List.range count).all (fun i => f (start + i))

def CheckedRange (f : ℕ → Bool) (start count : ℕ) : Prop :=
  ∀ i, start ≤ i → i < start + count → f i = true

theorem checkedRange_of_check (f : ℕ → Bool) (start count : ℕ)
    (h : checkRange f start count = true) : CheckedRange f start count := by
  intro i hlo hhi
  have hi : i - start < count := by omega
  have he : start + (i - start) = i := by omega
  have := List.all_eq_true.mp h (i - start) (List.mem_range.mpr hi)
  simpa only [he] using this

theorem checkedRange_append (f : ℕ → Bool) (start left right : ℕ)
    (hl : CheckedRange f start left)
    (hr : CheckedRange f (start + left) right) :
    CheckedRange f start (left + right) := by
  intro i hlo hhi
  by_cases h : i < start + left
  · exact hl i hlo h
  · exact hr i (by omega) (by omega)

theorem inverse_of_checkedRange (h : CheckedRange inverseAt 0 896) :
    rowInverse * rowMatrix = 1 := by
  apply row_inverse_of_products
  intro i
  have he := eq_of_beq (h i.val (Nat.zero_le _) i.isLt)
  simpa only [inverseAt, directProductFrom_eq, Packed.rowProduct] using he

theorem recursion_of_checkedRange (h : CheckedRange recursionAt 0 895) :
    RowRecursion := by
  apply row_recursion_of_products
  intro i
  have he := eq_of_beq (h i.val (Nat.zero_le _) i.isLt)
  simpa only [recursionAt, directProductFrom_eq, Packed.rowProduct, rowParent,
    Fin.val_succ] using he

end Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.RowChecks
