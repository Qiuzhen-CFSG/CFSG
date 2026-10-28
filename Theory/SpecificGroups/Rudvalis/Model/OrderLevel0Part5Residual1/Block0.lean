module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point69
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point70
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point71
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point72
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point73
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point74
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point75
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point76
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point77
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point78
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point79
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point80
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point81
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point82
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point83
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point84
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point85
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point86
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point87
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point88
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point89
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point90
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1.Block0Point91
import Mathlib.Tactic.FinCases

/-!
# Cached point checks for Rudvalis residuals 69–91

Assemble all 203 twenty-point slices for each of the 23 residuals in block 0.
The supporting modules check the Boolean identities by kernel reduction.
Source: the words and exact transitions in the sibling `Words` module.
The residual assembly owner supplies the independent cache certificates.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual1Checks

public theorem checked0 : block 0 := by
  intro s
  fin_cases s
  · exact block0_point69
  · exact block0_point70
  · exact block0_point71
  · exact block0_point72
  · exact block0_point73
  · exact block0_point74
  · exact block0_point75
  · exact block0_point76
  · exact block0_point77
  · exact block0_point78
  · exact block0_point79
  · exact block0_point80
  · exact block0_point81
  · exact block0_point82
  · exact block0_point83
  · exact block0_point84
  · exact block0_point85
  · exact block0_point86
  · exact block0_point87
  · exact block0_point88
  · exact block0_point89
  · exact block0_point90
  · exact block0_point91

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual1Checks
