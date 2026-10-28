module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2Blocks
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point138
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point139
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point140
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point141
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point142
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point143
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point144
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point145
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point146
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point147
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point148
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point149
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point150
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point151
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point152
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point153
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point154
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point155
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point156
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point157
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point158
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point159
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0.Point160
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-5 residual group 2, block 0

Assemble the kernel-checked transition identities for residual indices 138–160.
Each supporting module checks all 4060 points of its prescribed transition.
Source: `OrderLevel0Data` and `Part5Residual.target`, with ATLAS witnesses
as documented in `OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual2

public theorem checked0 : block 0 := by
  intro s
  fin_cases s
  · exact point138
  · exact point139
  · exact point140
  · exact point141
  · exact point142
  · exact point143
  · exact point144
  · exact point145
  · exact point146
  · exact point147
  · exact point148
  · exact point149
  · exact point150
  · exact point151
  · exact point152
  · exact point153
  · exact point154
  · exact point155
  · exact point156
  · exact point157
  · exact point158
  · exact point159
  · exact point160

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual2
