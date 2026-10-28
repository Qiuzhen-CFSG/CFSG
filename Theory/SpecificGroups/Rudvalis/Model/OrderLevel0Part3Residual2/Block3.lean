module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point187
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point188
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point189
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point190
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point191
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point192
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point193
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point194
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point195
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point196
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point197
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point198
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point199
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point200
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point201
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point202
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point203
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual group 2: block 3

The separately certified forward-generator identities cover exactly residual
indices 187 through 203. This module assembles them into `block 3`.
Source: `Part3Residual.target` in `OrderLevel0Part3ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2

public theorem block3 : block 3 := by
  intro s
  fin_cases s
  · exact point187
  · exact point188
  · exact point189
  · exact point190
  · exact point191
  · exact point192
  · exact point193
  · exact point194
  · exact point195
  · exact point196
  · exact point197
  · exact point198
  · exact point199
  · exact point200
  · exact point201
  · exact point202
  · exact point203

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2
