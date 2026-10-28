module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block4
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block5
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block6
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block7
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block8
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block9
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block10
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block11
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block12
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block13
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block14
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block15
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block16
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block17
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block18
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block19
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block20
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block21
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block22
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block23
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block24
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block25
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block26
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block27
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block28
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block29
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block30
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block31
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1Block32
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-0 residual certificate, interval 65–129

The 65 transition identities are certified in bounded compilation units.
Enumeration of the residual index proves exactly `residualBatch 1`.
Source: the ATLAS-derived `OrderLevel0Data` and `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual

/-- The second group of residual transitions in the part-0 order certificate. -/
public theorem residuals1 : residualBatch 1 := by
  intro s hs
  fin_cases s
  · exact Residual1.point65
  · exact Residual1.point66
  · exact Residual1.point67
  · exact Residual1.point68
  · exact Residual1.point69
  · exact Residual1.point70
  · exact Residual1.point71
  · exact Residual1.point72
  · exact Residual1.point73
  · exact Residual1.point74
  · exact Residual1.point75
  · exact Residual1.point76
  · exact Residual1.point77
  · exact Residual1.point78
  · exact Residual1.point79
  · exact Residual1.point80
  · exact Residual1.point81
  · exact Residual1.point82
  · exact Residual1.point83
  · exact Residual1.point84
  · exact Residual1.point85
  · exact Residual1.point86
  · exact Residual1.point87
  · exact Residual1.point88
  · exact Residual1.point89
  · exact Residual1.point90
  · exact Residual1.point91
  · exact Residual1.point92
  · exact Residual1.point93
  · exact Residual1.point94
  · exact Residual1.point95
  · exact Residual1.point96
  · exact Residual1.point97
  · exact Residual1.point98
  · exact Residual1.point99
  · exact Residual1.point100
  · exact Residual1.point101
  · exact Residual1.point102
  · exact Residual1.point103
  · exact Residual1.point104
  · exact Residual1.point105
  · exact Residual1.point106
  · exact Residual1.point107
  · exact Residual1.point108
  · exact Residual1.point109
  · exact Residual1.point110
  · exact Residual1.point111
  · exact Residual1.point112
  · exact Residual1.point113
  · exact Residual1.point114
  · exact Residual1.point115
  · exact Residual1.point116
  · exact Residual1.point117
  · exact Residual1.point118
  · exact Residual1.point119
  · exact Residual1.point120
  · exact Residual1.point121
  · exact Residual1.point122
  · exact Residual1.point123
  · exact Residual1.point124
  · exact Residual1.point125
  · exact Residual1.point126
  · exact Residual1.point127
  · exact Residual1.point128
  · exact Residual1.point129

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual
