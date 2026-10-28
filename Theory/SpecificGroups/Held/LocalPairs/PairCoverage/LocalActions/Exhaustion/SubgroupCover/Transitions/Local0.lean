module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.Transitions.CheckSupport

/-!
# Positive Held transitions in local overgroup 0

The 135 right representatives and both positive local generators are checked
on the four-point base. Each Boolean certificate covers eight representatives;
the final block repeats the initial row once. `all_of_blocks` proves that these
blocks cover every requested row. Every check is performed by the Lean kernel.

Source: the fixed factor words in `SubgroupCover/source/factors.json`, from
ATLAS HeG1-p2058B0 and max3W1/max4W1, with the existing inversion convention.
-/

set_option maxRecDepth 8192

namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.TransitionChecks

private theorem block0 : blockCheck false 0 = true := by decide +kernel

private theorem block1 : blockCheck false 1 = true := by decide +kernel

private theorem block2 : blockCheck false 2 = true := by decide +kernel

private theorem block3 : blockCheck false 3 = true := by decide +kernel

private theorem block4 : blockCheck false 4 = true := by decide +kernel

private theorem block5 : blockCheck false 5 = true := by decide +kernel

private theorem block6 : blockCheck false 6 = true := by decide +kernel

private theorem block7 : blockCheck false 7 = true := by decide +kernel

private theorem block8 : blockCheck false 8 = true := by decide +kernel

private theorem block9 : blockCheck false 9 = true := by decide +kernel

private theorem block10 : blockCheck false 10 = true := by decide +kernel

private theorem block11 : blockCheck false 11 = true := by decide +kernel

private theorem block12 : blockCheck false 12 = true := by decide +kernel

private theorem block13 : blockCheck false 13 = true := by decide +kernel

private theorem block14 : blockCheck false 14 = true := by decide +kernel

private theorem block15 : blockCheck false 15 = true := by decide +kernel

private theorem block16 : blockCheck false 16 = true := by decide +kernel

/-- All positive transition point checks in the false local overgroup. -/
public theorem checks_false : ∀ (r : Fin 135) (k : Fin 2), pointCheck false r k := by
  apply all_of_blocks
  intro b
  match b with
  | 0 => exact block0
  | 1 => exact block1
  | 2 => exact block2
  | 3 => exact block3
  | 4 => exact block4
  | 5 => exact block5
  | 6 => exact block6
  | 7 => exact block7
  | 8 => exact block8
  | 9 => exact block9
  | 10 => exact block10
  | 11 => exact block11
  | 12 => exact block12
  | 13 => exact block13
  | 14 => exact block14
  | 15 => exact block15
  | 16 => exact block16
  | ⟨n + 17, hn⟩ => omega

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.TransitionChecks
