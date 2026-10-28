module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Data
import Mathlib.Tactic.FinCases

/-!
# Point-action certificate for letter 2

Each finite point equation is kernel-checked against the preserved ATLAS words.
The bounded blocks cover all 4060 points. See `Max4Normalizers/source/actions.py`
and `SylowOvergroups.Definitions` for witness generation and ATLAS attribution.
These are point-action comparisons, independent of any subgroup order.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers

set_option maxRecDepth 30000
set_option Elab.async false

private theorem letter2_eq_chunk0 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 0 = true := by
  decide +kernel

private theorem letter2_eq_chunk1 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 1 = true := by
  decide +kernel

private theorem letter2_eq_chunk2 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 2 = true := by
  decide +kernel

private theorem letter2_eq_chunk3 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 3 = true := by
  decide +kernel

private theorem letter2_eq_chunk4 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 4 = true := by
  decide +kernel

private theorem letter2_eq_chunk5 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 5 = true := by
  decide +kernel

private theorem letter2_eq_chunk6 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 6 = true := by
  decide +kernel

private theorem letter2_eq_chunk7 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 7 = true := by
  decide +kernel

private theorem letter2_eq_chunk8 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 8 = true := by
  decide +kernel

private theorem letter2_eq_chunk9 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 9 = true := by
  decide +kernel

private theorem letter2_eq_chunk10 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 10 = true := by
  decide +kernel

private theorem letter2_eq_chunk11 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 11 = true := by
  decide +kernel

private theorem letter2_eq_chunk12 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 12 = true := by
  decide +kernel

private theorem letter2_eq_chunk13 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 13 = true := by
  decide +kernel

private theorem letter2_eq_chunk14 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 14 = true := by
  decide +kernel

private theorem letter2_eq_chunk15 : checkChunk (fun x : Fin 4060 => letter2 x = tableLocalLetter 2 x) 15 = true := by
  decide +kernel

public theorem letter2_eq : ∀ x : Fin 4060, letter2 x = tableLocalLetter 2 x := by
  apply allFinChunks
  intro b
  fin_cases b
  · exact letter2_eq_chunk0
  · exact letter2_eq_chunk1
  · exact letter2_eq_chunk2
  · exact letter2_eq_chunk3
  · exact letter2_eq_chunk4
  · exact letter2_eq_chunk5
  · exact letter2_eq_chunk6
  · exact letter2_eq_chunk7
  · exact letter2_eq_chunk8
  · exact letter2_eq_chunk9
  · exact letter2_eq_chunk10
  · exact letter2_eq_chunk11
  · exact letter2_eq_chunk12
  · exact letter2_eq_chunk13
  · exact letter2_eq_chunk14
  · exact letter2_eq_chunk15

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers
