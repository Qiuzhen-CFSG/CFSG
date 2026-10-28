module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2Blocks
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point149
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point136
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point137
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point138
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point139
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point140
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point141
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point142
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point143
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point144
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point145
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point146
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point147
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point148
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point150
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point151
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point152
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual group 2: block 0

Certify residual indices 136 through 152 using the prescribed forward-generator
identities. Each identity is checked on 203 slices of 20 points, then assembled
by `Part6Nat.ofSlices` in a separate transition module. Source: `OrderLevel0Data` and `Part3Residual.target`;
witness provenance is documented in `OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2

public theorem block0 : block 0 := by
  intro s
  fin_cases s
  · exact point136
  · exact point137
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

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2
