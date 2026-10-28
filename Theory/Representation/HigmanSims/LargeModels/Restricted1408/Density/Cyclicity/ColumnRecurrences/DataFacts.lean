module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.StepData
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.TransposeData
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnData

/-!
# Correspondence of proposed steps with the published column orbit

The layout scan retains every parent, generator choice and output row. A second
scan checks every input against its literal parent row. Neither scan asserts
matrix arithmetic or spanning. Source conventions are in `source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences

set_option maxRecDepth 4096 in
theorem transposeARows_size : transposeARows.size = 1408 := by decide +kernel

set_option maxRecDepth 4096 in
theorem transposeBRows_size : transposeBRows.size = 1408 := by decide +kernel

set_option maxRecDepth 4096 in
theorem steps_length : steps.length = 1407 := by decide +kernel

set_option maxRecDepth 4096 in
theorem steps_layout :
    layoutCheck (columnOrbitRows.toList.drop 1) (columnOrbitParents.toList.drop 1)
      (columnOrbitChoices.toList.drop 1) steps = true := by decide +kernel

set_option maxRecDepth 4096 in
theorem steps_inputs : inputsCheck 0 columnOrbitRows.toList steps = true := by decide +kernel

/-- Every positive orbit index has its literal parent, input, choice and output in the step list. -/
theorem steps_spec (i : Fin 1408) (hi : 0 < i.val) :
    ∃ s ∈ steps,
      s.parent = columnOrbitParents[i.val]! ∧
      s.input = columnOrbitRows[columnOrbitParents[i.val]!]! ∧
      s.choice = columnOrbitChoices[i.val]! ∧ s.output = columnOrbitRows[i.val]! := by
  have hk : i.val-1 < steps.length := by rw [steps_length]; omega
  have hs : steps[i.val-1]! ∈ steps := by
    rw [getElem!_pos steps (i.val-1) hk]
    exact List.getElem_mem hk
  refine ⟨steps[i.val-1]!, hs, ?_⟩
  have h := layoutCheck_sound _ _ _ _ steps_layout (i.val-1) hk
  have hin := inputsCheck_sound _ _ _ steps_inputs _ hs
  have hadd : 1+(i.val-1) = i.val := by omega
  simp only [getElem!_drop, hadd, Array.getElem!_toList] at h
  simp only [Nat.sub_zero, Array.getElem!_toList, h.2.1] at hin
  exact ⟨h.2.1, hin.2.symm, h.2.2, h.1⟩

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences
