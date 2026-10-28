module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.Block22

/-! Kernel-checked table block 23; see `Finite.Block` for its mathematical contract. -/

-- The representative block measured under 3 GiB when checked sequentially.
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
theorem blockValid23 : BlockValid 23 := by
  constructor
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
end Janko4.TwoRank.Finite
