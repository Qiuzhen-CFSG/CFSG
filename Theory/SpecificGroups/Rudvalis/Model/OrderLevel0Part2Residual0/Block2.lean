module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point48
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point49
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point50
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point51
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point52
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point53
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point54
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point55
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point56
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point57
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point58
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point59
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point60
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point61
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point62
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point63
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point64
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point65
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point66
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point67
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point68
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point69
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point70
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block2.Point71
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residuals 48 through 71

Each supporting module certifies one prescribed transition on all 4060 points,
using 203 kernel-checked slices. The transfer lemmas in `Words` identify these
checks with the exact representative and factor words of the source data.
This module assembles the 24 transitions into the third residual block.

Source: `OrderLevel0Data`, `Part2Residual.target`, and the candidate generator
`OrderCertificate/GenerateLevel0Part2Residual0Blocks.py`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual0Checks
set_option Elab.async false

public theorem checked2 : block 2 := by
  intro s
  fin_cases s
  · exact Block2.point48
  · exact Block2.point49
  · exact Block2.point50
  · exact Block2.point51
  · exact Block2.point52
  · exact Block2.point53
  · exact Block2.point54
  · exact Block2.point55
  · exact Block2.point56
  · exact Block2.point57
  · exact Block2.point58
  · exact Block2.point59
  · exact Block2.point60
  · exact Block2.point61
  · exact Block2.point62
  · exact Block2.point63
  · exact Block2.point64
  · exact Block2.point65
  · exact Block2.point66
  · exact Block2.point67
  · exact Block2.point68
  · exact Block2.point69
  · exact Block2.point70
  · exact Block2.point71

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual0Checks
