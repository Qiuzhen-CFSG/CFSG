module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Actions.Networks.Masks

/-!
# All fifteen mask equalities for the first Fi23 loop

This checks the square on the entire padded set simultaneously. Each of the
fifteen coordinate masks has a separate kernel reduction, bounding memory.
The actual `ActionCheck` follows once the fixed transforms' source and table
semantics are supplied. Those remain explicit here and are not asserted by
these numerical equalities. The coordinate-mask interpretation is proved.

Source: retained ATLAS F23G1-p31671B0, first A loop at zero-based letter 80,
inverse-cycle convention; GLS3 Table 5.3u.
-/

set_option Elab.async false

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Actions

private theorem plane0 : MaskEquation 0 0 := by
  unfold MaskEquation
  decide +kernel

private theorem plane1 : MaskEquation 0 1 := by
  unfold MaskEquation
  decide +kernel

private theorem plane2 : MaskEquation 0 2 := by
  unfold MaskEquation
  decide +kernel

private theorem plane3 : MaskEquation 0 3 := by
  unfold MaskEquation
  decide +kernel

private theorem plane4 : MaskEquation 0 4 := by
  unfold MaskEquation
  decide +kernel

private theorem plane5 : MaskEquation 0 5 := by
  unfold MaskEquation
  decide +kernel

private theorem plane6 : MaskEquation 0 6 := by
  unfold MaskEquation
  decide +kernel

private theorem plane7 : MaskEquation 0 7 := by
  unfold MaskEquation
  decide +kernel

private theorem plane8 : MaskEquation 0 8 := by
  unfold MaskEquation
  decide +kernel

private theorem plane9 : MaskEquation 0 9 := by
  unfold MaskEquation
  decide +kernel

private theorem plane10 : MaskEquation 0 10 := by
  unfold MaskEquation
  decide +kernel

private theorem plane11 : MaskEquation 0 11 := by
  unfold MaskEquation
  decide +kernel

private theorem plane12 : MaskEquation 0 12 := by
  unfold MaskEquation
  decide +kernel

private theorem plane13 : MaskEquation 0 13 := by
  unfold MaskEquation
  decide +kernel

private theorem plane14 : MaskEquation 0 14 := by
  unfold MaskEquation
  decide +kernel

theorem first_mask_equation (k : Fin 15) : MaskEquation 0 k := by
  fin_cases k
  · exact plane0
  · exact plane1
  · exact plane2
  · exact plane3
  · exact plane4
  · exact plane5
  · exact plane6
  · exact plane7
  · exact plane8
  · exact plane9
  · exact plane10
  · exact plane11
  · exact plane12
  · exact plane13
  · exact plane14

/-- The representative full numerical equation after shared semantic certification. -/
theorem first_action_of_pullbacks (hs : SourcePullbacks) (hc : CorePullbacks)
    (x : Fin 31671) : ActionCheck 0 x :=
  actionCheck_of_certificate hs hc coordinate_mask_sound 0 first_mask_equation x

theorem first_edge_mem_of_pullbacks (hcore : CoreActions)
    (hs : SourcePullbacks) (hc : CorePullbacks) :
    edge (loopGenerator 0) (loopPoint 0) ∈ KernelUpperData.first :=
  edge_mem_of_certificate hcore hs hc coordinate_mask_sound 0 first_mask_equation

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Actions
