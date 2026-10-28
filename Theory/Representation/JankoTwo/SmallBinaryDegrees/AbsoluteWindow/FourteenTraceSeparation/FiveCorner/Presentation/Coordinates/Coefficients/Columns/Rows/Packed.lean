module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Rows.Data

/-!
# Certified packing of the original row arrays

Each numerical certificate checks the full unchanged array, its length and
its entry bound. The mask is checked independently. The general extraction
proof then identifies `fastColumn` with the literal `columnFromRows`, without
assuming any candidate-word equality.

Source: Presentation/OperatorData.lean and Rows/source/README.md.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.Rows

-- The bounded checks are sequential to keep temporary kernel caches bounded.
set_option Elab.async false

private def DataCheck (k : Fin 9) : Prop :=
  packed k = pack 1024 (rows k).toList ∧
    (rows k).size = 1008 ∧
    (rows k).toList.all (fun r => decide (r < 2 ^ 1024)) = true

set_option maxRecDepth 4096 in
private theorem data0 : DataCheck 0 := by
  unfold DataCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem data1 : DataCheck 1 := by
  unfold DataCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem data2 : DataCheck 2 := by
  unfold DataCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem data3 : DataCheck 3 := by
  unfold DataCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem data4 : DataCheck 4 := by
  unfold DataCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem data5 : DataCheck 5 := by
  unfold DataCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem data6 : DataCheck 6 := by
  unfold DataCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem data7 : DataCheck 7 := by
  unfold DataCheck
  decide +kernel

set_option maxRecDepth 4096 in
private theorem data8 : DataCheck 8 := by
  unfold DataCheck
  decide +kernel

private theorem dataCheck (k : Fin 9) : DataCheck k := by
  fin_cases k
  · exact data0
  · exact data1
  · exact data2
  · exact data3
  · exact data4
  · exact data5
  · exact data6
  · exact data7
  · exact data8

set_option maxRecDepth 4096 in
private theorem mask_eq : mask = pack 1024 (List.replicate 1008 1) := by
  decide +kernel

/-- The fast extraction is exactly the original column traversal. -/
theorem fastColumn_eq (k : Fin 9) (j : Fin 1008) :
    fastColumn k j = columnFromRows j.val (rows k).toList := by
  obtain ⟨hp, hs, hb⟩ := dataCheck k
  have hl : (rows k).toList.length = 1008 := by simpa using hs
  have hm : mask = pack 1024 (List.replicate (rows k).toList.length 1) := by
    rw [hl]
    exact mask_eq
  have hr : ∀ r ∈ (rows k).toList, r < 2 ^ 1024 := by
    intro r h
    exact of_decide_eq_true (List.all_eq_true.mp hb r h)
  unfold fastColumn
  rw [hp, hm]
  apply fast_column 1024 _ (by decide) _ hr
  · decide +kernel
  · rw [hl]
    decide +kernel
  · have := j.isLt
    omega

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.Rows
