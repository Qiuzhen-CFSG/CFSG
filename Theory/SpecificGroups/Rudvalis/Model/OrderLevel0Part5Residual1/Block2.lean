module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual115
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual116
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual117
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual118
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual119
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual120
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual121
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual122
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual123
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual124
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual125
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual126
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual127
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual128
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual129
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual130
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual131
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual132
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual133
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual134
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual135
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual136
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block2Checks.Residual137
import Mathlib.Tactic.FinCases

/-!
# Cached point checks for Rudvalis residuals 115–137

Assemble the 203 twenty-point slice checks for each of the 23 residuals.
Each imported certificate uses kernel reduction of the explicit cached words;
the final residual owner supplies the independent cache composition proofs.
Source: the prescribed words in `OrderLevel0Part5Residual1.Words`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual1Checks

public theorem checked2 : block 2 := by
  intro s
  fin_cases s
  · exact block2point115
  · exact block2point116
  · exact block2point117
  · exact block2point118
  · exact block2point119
  · exact block2point120
  · exact block2point121
  · exact block2point122
  · exact block2point123
  · exact block2point124
  · exact block2point125
  · exact block2point126
  · exact block2point127
  · exact block2point128
  · exact block2point129
  · exact block2point130
  · exact block2point131
  · exact block2point132
  · exact block2point133
  · exact block2point134
  · exact block2point135
  · exact block2point136
  · exact block2point137

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual1Checks
