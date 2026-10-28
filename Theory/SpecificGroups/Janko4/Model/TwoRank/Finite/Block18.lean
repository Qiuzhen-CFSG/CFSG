module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.Block17

/-! Kernel-checked table block 18; see `Finite.Block` for its mathematical contract. -/

-- The representative block measured under 3 GiB when checked sequentially.
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
theorem blockValid18 : BlockValid 18 := by
  constructor
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
end Janko4.TwoRank.Finite
