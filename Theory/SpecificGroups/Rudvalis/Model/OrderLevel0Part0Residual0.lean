module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual0.Block00
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual0.Block01
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual0.Block02
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual0.Block03
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual0.Block04
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual0.Block05
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual0.Block06
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual0.Block07
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual0.Block08
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual0.Block09
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual0.Block10
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual0.Block11
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual0.Block12
import Mathlib.Tactic.FinCases

/-!
# First group of Rudvalis part-0 residual transitions

This certificate proves the original transition checks at residual indices
0 through 64. Each identity is assembled from kernel-checked point slices in
the supporting modules. Source: `OrderLevel0Part0ResidualReduction.target`,
with permutation and word witnesses from `OrderLevel0Data`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual

/-- The first 65 residual transitions in level-0 part 0. -/
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

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual
