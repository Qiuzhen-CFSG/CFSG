module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point00
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point01
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point02
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point03
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point04
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point05
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point06
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point07
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point08
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point09
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point10
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point11
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point12
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point13
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point14
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point15
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point16
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point17
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point18
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point19
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point20
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point21
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point22
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0.Block0.Point23
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residuals 0 through 23

The 24 transition certificates evaluate the prescribed representative and factor
words on all 4060 points, in kernel-checked slices of 20 points. This module
assembles them in the exact order of `Part2Residual.target` to certify `block 0`.
Source: `OrderLevel0Data` and `OrderLevel0Part2ResidualReduction`; the numerical
certificates adapt `OrderCertificate/GenerateLevel0Part2Residual0Blocks.py`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual0Checks

public theorem checked0 : block 0 := by
  intro s
  fin_cases s
  · exact Block0.certifiedPoint0
  · exact Block0.certifiedPoint1
  · exact Block0.certifiedPoint2
  · exact Block0.certifiedPoint3
  · exact Block0.certifiedPoint4
  · exact Block0.certifiedPoint5
  · exact Block0.certifiedPoint6
  · exact Block0.certifiedPoint7
  · exact Block0.certifiedPoint8
  · exact Block0.certifiedPoint9
  · exact Block0.certifiedPoint10
  · exact Block0.certifiedPoint11
  · exact Block0.certifiedPoint12
  · exact Block0.certifiedPoint13
  · exact Block0.certifiedPoint14
  · exact Block0.certifiedPoint15
  · exact Block0.certifiedPoint16
  · exact Block0.certifiedPoint17
  · exact Block0.certifiedPoint18
  · exact Block0.certifiedPoint19
  · exact Block0.certifiedPoint20
  · exact Block0.certifiedPoint21
  · exact Block0.certifiedPoint22
  · exact Block0.certifiedPoint23

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual0Checks
