module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Rows.Packed

/-!
# Bounded comparisons with the candidate word columns

Eight chunks of 126 output indices cover the original 1008 roots. Every
comparison retains `combined`, hence every original catalogue occurrence.
The certified packed-row extraction bounds the cost of each kernel check.
No word-action correctness or group geometry is assumed.

Source: Columns/source/README.md and Rows/source/README.md.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.Rows

-- Bounded sequential certificates avoid concurrent large reduction caches.
set_option Elab.async false

private def chunkIndex (q : Fin 8) (r : Fin 126) : Fin 1008 :=
  ⟨126 * q.val + r.val, by have := q.isLt; have := r.isLt; omega⟩

private def ChunkCheck (k : Fin 9) (q : Fin 8) : Prop :=
  ∀ r : Fin 126, combined k (chunkIndex q r) = fastColumn k (chunkIndex q r)

set_option maxRecDepth 4096 in
private theorem check0_0 : ChunkCheck 0 0 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check0_1 : ChunkCheck 0 1 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check0_2 : ChunkCheck 0 2 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check0_3 : ChunkCheck 0 3 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check0_4 : ChunkCheck 0 4 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check0_5 : ChunkCheck 0 5 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check0_6 : ChunkCheck 0 6 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check0_7 : ChunkCheck 0 7 := by
  unfold ChunkCheck
  decide +kernel

private theorem chunks0 (q : Fin 8) : ChunkCheck 0 q := by
  fin_cases q
  · exact check0_0
  · exact check0_1
  · exact check0_2
  · exact check0_3
  · exact check0_4
  · exact check0_5
  · exact check0_6
  · exact check0_7

set_option maxRecDepth 4096 in
private theorem check1_0 : ChunkCheck 1 0 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1_1 : ChunkCheck 1 1 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1_2 : ChunkCheck 1 2 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1_3 : ChunkCheck 1 3 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1_4 : ChunkCheck 1 4 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1_5 : ChunkCheck 1 5 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1_6 : ChunkCheck 1 6 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1_7 : ChunkCheck 1 7 := by
  unfold ChunkCheck
  decide +kernel

private theorem chunks1 (q : Fin 8) : ChunkCheck 1 q := by
  fin_cases q
  · exact check1_0
  · exact check1_1
  · exact check1_2
  · exact check1_3
  · exact check1_4
  · exact check1_5
  · exact check1_6
  · exact check1_7

set_option maxRecDepth 4096 in
private theorem check2_0 : ChunkCheck 2 0 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2_1 : ChunkCheck 2 1 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2_2 : ChunkCheck 2 2 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2_3 : ChunkCheck 2 3 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2_4 : ChunkCheck 2 4 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2_5 : ChunkCheck 2 5 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2_6 : ChunkCheck 2 6 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2_7 : ChunkCheck 2 7 := by
  unfold ChunkCheck
  decide +kernel

private theorem chunks2 (q : Fin 8) : ChunkCheck 2 q := by
  fin_cases q
  · exact check2_0
  · exact check2_1
  · exact check2_2
  · exact check2_3
  · exact check2_4
  · exact check2_5
  · exact check2_6
  · exact check2_7

set_option maxRecDepth 4096 in
private theorem check3_0 : ChunkCheck 3 0 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3_1 : ChunkCheck 3 1 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3_2 : ChunkCheck 3 2 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3_3 : ChunkCheck 3 3 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3_4 : ChunkCheck 3 4 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3_5 : ChunkCheck 3 5 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3_6 : ChunkCheck 3 6 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3_7 : ChunkCheck 3 7 := by
  unfold ChunkCheck
  decide +kernel

private theorem chunks3 (q : Fin 8) : ChunkCheck 3 q := by
  fin_cases q
  · exact check3_0
  · exact check3_1
  · exact check3_2
  · exact check3_3
  · exact check3_4
  · exact check3_5
  · exact check3_6
  · exact check3_7

set_option maxRecDepth 4096 in
private theorem check4_0 : ChunkCheck 4 0 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check4_1 : ChunkCheck 4 1 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check4_2 : ChunkCheck 4 2 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check4_3 : ChunkCheck 4 3 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check4_4 : ChunkCheck 4 4 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check4_5 : ChunkCheck 4 5 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check4_6 : ChunkCheck 4 6 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check4_7 : ChunkCheck 4 7 := by
  unfold ChunkCheck
  decide +kernel

private theorem chunks4 (q : Fin 8) : ChunkCheck 4 q := by
  fin_cases q
  · exact check4_0
  · exact check4_1
  · exact check4_2
  · exact check4_3
  · exact check4_4
  · exact check4_5
  · exact check4_6
  · exact check4_7

set_option maxRecDepth 4096 in
private theorem check5_0 : ChunkCheck 5 0 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check5_1 : ChunkCheck 5 1 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check5_2 : ChunkCheck 5 2 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check5_3 : ChunkCheck 5 3 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check5_4 : ChunkCheck 5 4 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check5_5 : ChunkCheck 5 5 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check5_6 : ChunkCheck 5 6 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check5_7 : ChunkCheck 5 7 := by
  unfold ChunkCheck
  decide +kernel

private theorem chunks5 (q : Fin 8) : ChunkCheck 5 q := by
  fin_cases q
  · exact check5_0
  · exact check5_1
  · exact check5_2
  · exact check5_3
  · exact check5_4
  · exact check5_5
  · exact check5_6
  · exact check5_7

set_option maxRecDepth 4096 in
private theorem check6_0 : ChunkCheck 6 0 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check6_1 : ChunkCheck 6 1 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check6_2 : ChunkCheck 6 2 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check6_3 : ChunkCheck 6 3 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check6_4 : ChunkCheck 6 4 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check6_5 : ChunkCheck 6 5 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check6_6 : ChunkCheck 6 6 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check6_7 : ChunkCheck 6 7 := by
  unfold ChunkCheck
  decide +kernel

private theorem chunks6 (q : Fin 8) : ChunkCheck 6 q := by
  fin_cases q
  · exact check6_0
  · exact check6_1
  · exact check6_2
  · exact check6_3
  · exact check6_4
  · exact check6_5
  · exact check6_6
  · exact check6_7

set_option maxRecDepth 4096 in
private theorem check7_0 : ChunkCheck 7 0 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check7_1 : ChunkCheck 7 1 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check7_2 : ChunkCheck 7 2 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check7_3 : ChunkCheck 7 3 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check7_4 : ChunkCheck 7 4 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check7_5 : ChunkCheck 7 5 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check7_6 : ChunkCheck 7 6 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check7_7 : ChunkCheck 7 7 := by
  unfold ChunkCheck
  decide +kernel

private theorem chunks7 (q : Fin 8) : ChunkCheck 7 q := by
  fin_cases q
  · exact check7_0
  · exact check7_1
  · exact check7_2
  · exact check7_3
  · exact check7_4
  · exact check7_5
  · exact check7_6
  · exact check7_7

set_option maxRecDepth 4096 in
private theorem check8_0 : ChunkCheck 8 0 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check8_1 : ChunkCheck 8 1 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check8_2 : ChunkCheck 8 2 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check8_3 : ChunkCheck 8 3 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check8_4 : ChunkCheck 8 4 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check8_5 : ChunkCheck 8 5 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check8_6 : ChunkCheck 8 6 := by
  unfold ChunkCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check8_7 : ChunkCheck 8 7 := by
  unfold ChunkCheck
  decide +kernel

private theorem chunks8 (q : Fin 8) : ChunkCheck 8 q := by
  fin_cases q
  · exact check8_0
  · exact check8_1
  · exact check8_2
  · exact check8_3
  · exact check8_4
  · exact check8_5
  · exact check8_6
  · exact check8_7

private theorem chunkChecks (k : Fin 9) (q : Fin 8) : ChunkCheck k q := by
  fin_cases k
  · exact chunks0 q
  · exact chunks1 q
  · exact chunks2 q
  · exact chunks3 q
  · exact chunks4 q
  · exact chunks5 q
  · exact chunks6 q
  · exact chunks7 q
  · exact chunks8 q

/-- All nine combinations agree with the certified packed original rows. -/
theorem combined_eq_fastColumn (k : Fin 9) (j : Fin 1008) :
    combined k j = fastColumn k j := by
  let q : Fin 8 := ⟨j.val / 126, by have := j.isLt; omega⟩
  let r : Fin 126 := ⟨j.val % 126, Nat.mod_lt _ (by decide)⟩
  have hj : chunkIndex q r = j := by
    apply Fin.ext
    simp only [chunkIndex, q, r]
    omega
  simpa only [hj] using chunkChecks k q r

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.Rows
