module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Actions
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Checks

/-!
# Certified shared-register actions for the first Fi23 loops

The candidate maps agree with the actual words of the unchanged two-generator
subgroup at every natural-number index, including the default identity case.
The proof assembles short checked composition equations without expanding the
shared straight-line program. The final consumer uses the checked tree paths
and retains exactly the independent numerical action-square premise.

Source: retained ATLAS F23G1-p31671B0 in the inverse-cycle convention;
GLS3 Table 5.3u and the Fischer paragraph near line 1042 of
`refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops

/-- Every numerical shared-register map is the actual subgroup word. -/
theorem core_actions : CoreActions := by
  intro i x
  unfold coreMap coreWord
  split
  · exact Core.action1 x
  · exact Core.action2 x
  · exact Core.action3 x
  · exact Core.action4 x
  · exact Core.action7 x
  · exact Core.action9 x
  · exact Core.action11 x
  · exact Core.action16 x
  · exact Core.action18 x
  · exact Core.action20 x
  · exact Core.action35 x
  · exact Core.action48 x
  · exact Core.action49 x
  · exact Core.action50 x
  · exact Core.action52 x
  · exact Core.action54 x
  · exact Core.action66 x
  · exact Core.action67 x
  · exact Core.action72 x
  · exact Core.action74 x
  · exact Core.action76 x
  · exact Core.action91 x
  · exact Core.action101 x
  · exact Core.action102 x
  · exact Core.action103 x
  · exact Core.action105 x
  · exact Core.action107 x
  · exact Core.action116 x
  · exact Core.action117 x
  · exact Core.action128 x
  · exact Core.action137 x
  · exact Core.action138 x
  · exact Core.action139 x
  · exact Core.action141 x
  · exact Core.action143 x
  · exact Core.action154 x
  · exact Core.action158 x
  · exact Core.action159 x
  · exact Core.action179 x
  · exact Core.action181 x
  · exact Core.action182 x
  · exact Core.action192 x
  · exact Core.action193 x
  · exact Core.action200 x
  · exact Core.action202 x
  · exact Core.action203 x
  · exact Core.action214 x
  · exact Core.action217 x
  · exact Core.action218 x
  · split <;> first | contradiction | rfl

/-- The literal Schreier loop belongs to the original subgroup once its
independent numerical action square has been checked. -/
theorem loop_edge_mem_of_action_check (i : Fin 722) (ha : ∀ x, ActionCheck i x) :
    edge (loopGenerator i) (loopPoint i) ∈ KernelUpperData.first := by
  have hp := path_properties i
  exact loop_edge_mem core_actions i hp.1
    (by simpa only [sourceGenerator_eq] using hp.2) ha

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops
