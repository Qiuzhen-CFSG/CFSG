module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Blocks
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Orbit
open Representation.HigmanSims.LargeModels.Binary
open Representation.HigmanSims.LargeModels.Binary.Large
open Representation.HigmanSims.LargeModels.Binary.Large.Density518
open RowArithmetic
/-!
# Interfaces for the degree-518 row certificates

The finite checks below use the literal row data from R. A. Wilson et al.,
ATLAS HSG1-f2r518B0, as transcribed in `Binary/source/density518.json`.
A certificate consists of a right-inverse row and the incoming orbit edge.
The arithmetic-to-matrix conversion keeps the appended-letter convention of
`Orbit.lean`. Small intervals let separate batches assemble without another
large kernel computation.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density518.Rows

def parent (i : Fin 517) : Fin 518 := ⟨rowParents[i.val + 1]! % 518, Nat.mod_lt _ (by decide)⟩
def letter (i : Fin 517) : Bool := rowLetters[i.val + 1]!
def Step (i : Fin 517) : Prop :=
  parent i < i.succ ∧
  rowWords[i.succ.val]! = rowWords[(parent i).val]! ++ [letter i] ∧
  Matrix.vecMul (R.row (parent i)) (if letter i then B else A) = R.row i.succ

theorem step_of_check (i : Fin 517)
    (hm : parent i < i.succ ∧
      rowWords[i.succ.val]! = rowWords[(parent i).val]! ++ [letter i])
    (hc : combine (if letter i then D518.bRows else D518.aRows).toList
      rowRows[(parent i).val]! = rowRows[i.succ.val]!) : Step i := by
  refine ⟨hm.1, hm.2, ?_⟩
  have hsize : (if letter i then D518.bRows else D518.aRows).size = 518 := by
    split
    · exact Blocks.b_size
    · exact Blocks.a_size
  have h := vector_combine (if letter i then D518.bRows else D518.aRows).toList
    518 518 (by simpa using hsize) rowRows[(parent i).val]!
  rw [matrix_toList, hc] at h
  change Matrix.vecMul (vector 518 rowRows[(parent i).val]!)
    (if letter i then B else A) = vector 518 rowRows[i.succ.val]!
  cases hb : letter i <;> simpa only [hb, Bool.false_eq_true, if_false, if_true, A, B]
    using h.symm


def Checked (i : Fin 518) : Prop :=
  (R * Ri) i = (1 : Matrix518) i ∧
    ∀ h : 0 < i.val, Step ⟨i.val - 1, by omega⟩

def OnInterval (P : Fin 518 → Prop) (lo hi : ℕ) : Prop :=
  ∀ i, lo ≤ i.val → i.val < hi → P i

theorem interval_of_block (P : Fin 518 → Prop) (lo count : ℕ)
    (hbound : lo + count ≤ 518)
    (h : ∀ j : Fin count, P ⟨lo + j.val, by omega⟩) :
    OnInterval P lo (lo + count) := by
  intro i hlo hhi
  have heq : (⟨lo + (i.val - lo), by omega⟩ : Fin 518) = i := by
    apply Fin.ext
    exact Nat.add_sub_of_le hlo
  rw [← heq]
  exact h ⟨i.val - lo, by omega⟩

theorem interval_join (P : Fin 518 → Prop) (lo mid hi : ℕ)
    (hl : OnInterval P lo mid) (hr : OnInterval P mid hi) : OnInterval P lo hi := by
  intro i hlo hhi
  by_cases hm : i.val < mid
  · exact hl i hlo hm
  · exact hr i (by omega) hhi

/-- Every nonroot row has its checked incoming edge. -/
theorem steps_of_checked (h : OnInterval Checked 0 518) :
    ∀ i : Fin 517, Step i := by
  intro i
  exact (h i.succ (Nat.zero_le _) i.succ.isLt).2 (Nat.succ_pos _)

/-- The checked rows are exactly the rows of the literal right-inverse identity. -/
theorem inverse_of_checked (h : OnInterval Checked 0 518) : R * Ri = 1 := by
  funext i
  exact (h i (Nat.zero_le _) i.isLt).1

end Representation.HigmanSims.LargeModels.Binary.Large.Density518.Rows
