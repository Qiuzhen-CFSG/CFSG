module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Block00
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Block01
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Block02
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Block03
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Block04
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Block05
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Block06
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Block07
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Block08
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Block09
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Block10
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Block11
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Block12
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Block13
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Block14
import Mathlib.Tactic.FinCases

/-!
# First group of Rudvalis part-1 residual transitions

The original transitions at residual indices 0–70 are assembled from kernel
checks on 29 slices covering all 4060 points. Source: `OrderLevel0Data` and
`OrderLevel0Part1ResidualReduction.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part1Residual

/-- The first 71 residual transitions in level-0 part 1. -/
public theorem residuals0 : residualBatch 0 := by
  intro s h
  fin_cases s
  · exact Residual0Checks.point0
  · exact Residual0Checks.point1
  · exact Residual0Checks.point2
  · exact Residual0Checks.point3
  · exact Residual0Checks.point4
  · exact Residual0Checks.point5
  · exact Residual0Checks.point6
  · exact Residual0Checks.point7
  · exact Residual0Checks.point8
  · exact Residual0Checks.point9
  · exact Residual0Checks.point10
  · exact Residual0Checks.point11
  · exact Residual0Checks.point12
  · exact Residual0Checks.point13
  · exact Residual0Checks.point14
  · exact Residual0Checks.point15
  · exact Residual0Checks.point16
  · exact Residual0Checks.point17
  · exact Residual0Checks.point18
  · exact Residual0Checks.point19
  · exact Residual0Checks.point20
  · exact Residual0Checks.point21
  · exact Residual0Checks.point22
  · exact Residual0Checks.point23
  · exact Residual0Checks.point24
  · exact Residual0Checks.point25
  · exact Residual0Checks.point26
  · exact Residual0Checks.point27
  · exact Residual0Checks.point28
  · exact Residual0Checks.point29
  · exact Residual0Checks.point30
  · exact Residual0Checks.point31
  · exact Residual0Checks.point32
  · exact Residual0Checks.point33
  · exact Residual0Checks.point34
  · exact Residual0Checks.point35
  · exact Residual0Checks.point36
  · exact Residual0Checks.point37
  · exact Residual0Checks.point38
  · exact Residual0Checks.point39
  · exact Residual0Checks.point40
  · exact Residual0Checks.point41
  · exact Residual0Checks.point42
  · exact Residual0Checks.point43
  · exact Residual0Checks.point44
  · exact Residual0Checks.point45
  · exact Residual0Checks.point46
  · exact Residual0Checks.point47
  · exact Residual0Checks.point48
  · exact Residual0Checks.point49
  · exact Residual0Checks.point50
  · exact Residual0Checks.point51
  · exact Residual0Checks.point52
  · exact Residual0Checks.point53
  · exact Residual0Checks.point54
  · exact Residual0Checks.point55
  · exact Residual0Checks.point56
  · exact Residual0Checks.point57
  · exact Residual0Checks.point58
  · exact Residual0Checks.point59
  · exact Residual0Checks.point60
  · exact Residual0Checks.point61
  · exact Residual0Checks.point62
  · exact Residual0Checks.point63
  · exact Residual0Checks.point64
  · exact Residual0Checks.point65
  · exact Residual0Checks.point66
  · exact Residual0Checks.point67
  · exact Residual0Checks.point68
  · exact Residual0Checks.point69
  · exact Residual0Checks.point70

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual
