module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck23

/-! The separately checked branches assemble the complete finite certificate. -/
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound

theorem tree_checked :
    check compatible fixed 2048 tree000 (List.finRange 192) (List.finRange 2048) = true := by
  have hu : actors000 = List.finRange 192 := by decide +kernel
  simpa only [hu, allMasks] using tree000_valid
end Janko4.TwoRank.Finite
