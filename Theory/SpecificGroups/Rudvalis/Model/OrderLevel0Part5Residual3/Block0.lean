module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Assembly
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point207
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point208
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point209
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point210
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point211
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point212
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point213
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point214
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point215
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point216
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point217
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point218
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point219
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point220
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point221
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point222
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0Certificate.Point223
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-5 residuals 207 through 223

Assemble the seventeen prescribed transition identities. Each supporting
certificate checks the exact source words against certified subword tables and
checks their actions on all 4060 points. Source: `Part5Residual.target` and the
ATLAS witnesses documented in `OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks

public theorem checked0 : block 0 := by
  intro s
  fin_cases s
  · exact Block0Certificate.point207
  · exact Block0Certificate.point208
  · exact Block0Certificate.point209
  · exact Block0Certificate.point210
  · exact Block0Certificate.point211
  · exact Block0Certificate.point212
  · exact Block0Certificate.point213
  · exact Block0Certificate.point214
  · exact Block0Certificate.point215
  · exact Block0Certificate.point216
  · exact Block0Certificate.point217
  · exact Block0Certificate.point218
  · exact Block0Certificate.point219
  · exact Block0Certificate.point220
  · exact Block0Certificate.point221
  · exact Block0Certificate.point222
  · exact Block0Certificate.point223

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
