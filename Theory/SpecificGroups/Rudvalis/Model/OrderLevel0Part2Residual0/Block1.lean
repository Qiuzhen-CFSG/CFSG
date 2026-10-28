module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point24
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point25
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point26
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point27
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point28
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point29
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point30
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point31
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point32
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point33
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point34
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point35
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point36
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point37
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point38
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point39
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point40
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point41
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point42
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point43
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point44
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point45
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point46
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block1.Point47
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residuals 24 through 47

The individual transition certificates each check 203 twenty-point slices of
explicit words. The checked word-transfer theorems identify these with the
prescribed transitions in `Part2Residual.target` and `OrderLevel0Data`.
This module assembles the second interval of the first residual batch.

Source: `OrderCertificate/GenerateLevel0Part2Residual0Blocks.py`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual0Checks

public theorem checked1 : block 1 := by
  intro s
  fin_cases s
  · exact checkedPoint24
  · exact checkedPoint25
  · exact checkedPoint26
  · exact checkedPoint27
  · exact checkedPoint28
  · exact checkedPoint29
  · exact checkedPoint30
  · exact checkedPoint31
  · exact checkedPoint32
  · exact checkedPoint33
  · exact checkedPoint34
  · exact checkedPoint35
  · exact checkedPoint36
  · exact checkedPoint37
  · exact checkedPoint38
  · exact checkedPoint39
  · exact checkedPoint40
  · exact checkedPoint41
  · exact checkedPoint42
  · exact checkedPoint43
  · exact checkedPoint44
  · exact checkedPoint45
  · exact checkedPoint46
  · exact checkedPoint47

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual0Checks
