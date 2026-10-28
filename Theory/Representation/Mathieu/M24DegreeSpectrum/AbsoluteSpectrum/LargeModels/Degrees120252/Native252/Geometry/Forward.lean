module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Geometry.Tables

/-!
# The saved forward maps act on the literal partitions

Each bounded certificate transforms six packed masks, sorts them, and compares
with the saved target row. The bit-network semantics in `Certificate` turn
these integer identities into the native finset action. All 1771 rows for both
generators are checked by the kernel; the data are never trusted externally.

Sources and conventions: `Degrees120252/Native252/source/README.md` and
`Degrees120252/source/README.md`; James (1973), GM02 Proposition 5.1.
-/

-- Bounded certificates were measured before expansion. Sequential elaboration
-- avoids retaining many independent kernel computations at once.
set_option Elab.async false

public section
open scoped Pointwise
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Geometry
open Certificate

private theorem row_length (i : Fin 1771) : ((pointMasks[i.val]?).getD []).length = 6 := by
  have h := congrArg (fun rows : List ℕ => rows[i.val]?.getD 0) lengths
  simp only [List.getElem?_map, List.getElem?_replicate, i.isLt, if_true,
    Option.getD_some] at h
  cases hr : pointMasks[i.val]? with
  | none => simp [hr] at h
  | some row => simpa only [hr, Option.map_some, Option.getD_some] using h

private theorem forward_length (j : Fin 2) : (![forwardRows0, forwardRows1] j).length = 1771 := by
  fin_cases j <;> decide +kernel

private theorem forward_row (j : Fin 2) (i : Fin 1771) :
    transform j (pointMasks[i.val]?.getD []) =
      pointMasks[(forward j i).val]?.getD [] := by
  have hrows := rows_forward j
  have h := congrArg (fun rows : List (List ℕ) => rows[i.val]?.getD []) hrows
  have hi : i.val < (![forwardRows0, forwardRows1] j).length := by
    rw [forward_length]; exact i.isLt
  rw [List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem hi] at h
  simp only [Option.map_some, Option.getD_some] at h
  change transform j (pointMasks[i.val]?.getD []) =
    lookup ((![forwardRows0, forwardRows1] j)[i.val]?.getD 0)
  rw [List.getElem?_eq_getElem hi, Option.getD_some]
  rw [← h]
  cases pointMasks[i.val]? <;> rfl

/-- The saved forward index maps are the actual native generator action. -/
theorem pointParts_forward (j : Fin 2) (i : Fin 1771) :
    actor j • pointParts i = pointParts (forward j i) := by
  change actor j • (Finset.univ.image fun k : Fin 6 =>
    mask ((pointMasks[i.val]?.getD [])[k.val]?.getD 0)) = _
  rw [← parts_six _ (row_length i), ← parts_transform, forward_row,
    parts_six _ (row_length (forward j i))]
  rfl

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Geometry
