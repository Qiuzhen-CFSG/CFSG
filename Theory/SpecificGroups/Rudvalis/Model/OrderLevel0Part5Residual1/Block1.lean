module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row92
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row93
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row94
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row95
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row96
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row97
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row98
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row99
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row100
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row101
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row102
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row103
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row104
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row105
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row106
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row107
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row108
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row109
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row110
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row111
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row112
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row113
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block1.Row114
import Mathlib.Tactic.FinCases

/-!
# Cached Rudvalis residual checks 92–114

Assemble the 23 independently kernel-checked residual identities, each checked
in 203 slices of twenty points. These raw checks require no cache composition
certificates. Source: the explicit representative words and factor cache in
`OrderLevel0Part5Residual1.Words`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual1Checks

public theorem checked1 : block 1 := by
  intro s
  fin_cases s
  · exact Block1.point92
  · exact Block1.point93
  · exact Block1.point94
  · exact Block1.point95
  · exact Block1.point96
  · exact Block1.point97
  · exact Block1.point98
  · exact Block1.point99
  · exact Block1.point100
  · exact Block1.point101
  · exact Block1.point102
  · exact Block1.point103
  · exact Block1.point104
  · exact Block1.point105
  · exact Block1.point106
  · exact Block1.point107
  · exact Block1.point108
  · exact Block1.point109
  · exact Block1.point110
  · exact Block1.point111
  · exact Block1.point112
  · exact Block1.point113
  · exact Block1.point114

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual1Checks
