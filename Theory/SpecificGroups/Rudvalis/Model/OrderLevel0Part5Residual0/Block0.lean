module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Reduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Point0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point4
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point5
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point6
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point7
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point8
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point9
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point10
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point11
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point12
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point13
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point14
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point15
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point16
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point17
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point18
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point19
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point20
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point21
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0Point22
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-5 residuals 0 through 22

The 23 exact transition certificates form the first interval of residual batch 0.
Each transition is checked on all 4060 points by the packed evaluator; transition
0 reuses `Point0`. Source: `Part5Residual.target` and the interval definition in
`OrderLevel0Part5Residual0.Reduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual0Checks

public theorem block0 : block 0 := by
  intro s
  fin_cases s
  · exact point0
  · exact block0Point1
  · exact block0Point2
  · exact block0Point3
  · exact block0Point4
  · exact block0Point5
  · exact block0Point6
  · exact block0Point7
  · exact block0Point8
  · exact block0Point9
  · exact block0Point10
  · exact block0Point11
  · exact block0Point12
  · exact block0Point13
  · exact block0Point14
  · exact block0Point15
  · exact block0Point16
  · exact block0Point17
  · exact block0Point18
  · exact block0Point19
  · exact block0Point20
  · exact block0Point21
  · exact block0Point22

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual0Checks
