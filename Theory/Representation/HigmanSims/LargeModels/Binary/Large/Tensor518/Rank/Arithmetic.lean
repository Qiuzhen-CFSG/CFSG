module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Data
/-!
# Arithmetic interpretation of the tensor-section pivot columns

Contiguous runs of source columns are packed by shifts and truncation. The
bit theorem proves their precise interpretation for arbitrary source rows.
`basisMatrix_eq` also checks the actual sum-index convention: the 21 kernel
rows precede the 518 lifts. These lemmas are used by `Rank/Certificate.lean`.
Source: the pivot data in `Binary/source/section518.json` and the row-section
construction documented in `Tensor518/source/README.md`.
-/

@[expose] public section
open Thompson.BinaryMatrix
open Representation.HigmanSims.LargeModels.Binary.Large
namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank

def gather : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (s, n) :: rs, x => (x >>> s) % 2 ^ n ||| (gather rs x <<< n)

def column : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (s, n) :: rs, j => if j < n then s + j else column rs (j-n)

def width : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (_, n) :: rs => n + width rs

theorem testBit_gather (rs : List (ℕ × ℕ)) (x j : ℕ) (h : j < width rs) :
    (gather rs x).testBit j = x.testBit (column rs j) := by
  induction rs generalizing j with
  | nil => simp [width] at h
  | cons r rs ih =>
    rcases r with ⟨s, n⟩
    simp only [width] at h
    simp only [gather, Nat.testBit_or, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight, Nat.testBit_shiftLeft, column]
    split_ifs with hj
    · simp [hj, Nat.not_le_of_gt hj]
    · have hn : n ≤ j := Nat.le_of_not_gt hj
      simp [hj, hn, ih (j-n) (by omega)]

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank

namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank
open RowArithmetic

theorem basisMatrix_eq : basisMatrix = matrix 539 1120 (kernelRows ++ liftRows) := by
  funext i j
  refine Fin.addCases (m := 21) (n := 518) (fun a => ?_) (fun b => ?_) i
  · change (Sum.elim kernelMatrix liftMatrix) (finSumFinEquiv.symm (Fin.castAdd 518 a)) j = _
    rw [finSumFinEquiv_symm_apply_castAdd]
    change Thompson.BinaryMatrix.bit kernelRows[a.val]! j.val =
      Thompson.BinaryMatrix.bit (kernelRows ++ liftRows)[a.val]! j.val
    simp only [List.getElem!_eq_getElem?_getD,
      List.getElem?_append_left (show a.val < kernelRows.length from a.isLt)]
  · change (Sum.elim kernelMatrix liftMatrix) (finSumFinEquiv.symm (Fin.natAdd 21 b)) j = _
    rw [finSumFinEquiv_symm_apply_natAdd]
    change Thompson.BinaryMatrix.bit liftRows[b.val]! j.val =
      Thompson.BinaryMatrix.bit (kernelRows ++ liftRows)[21 + b.val]! j.val
    rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
      List.getElem?_append_right (show kernelRows.length ≤ 21 + b.val by change 21 ≤ _; omega)]
    change _ = Thompson.BinaryMatrix.bit (liftRows[21 + b.val - 21]?.getD 0) j.val
    rw [Nat.add_sub_cancel_left]
    rfl
end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank

namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank

theorem map_entry (xs ys : List ℕ) (f : ℕ → ℕ) (h : xs.map f = ys)
    (n : ℕ) (hlen : xs.length = n) (i : Fin n) : f xs[i.val]! = ys[i.val]! := by
  have hi : i.val < xs.length := by rw [hlen]; exact i.isLt
  rw [← h]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank
