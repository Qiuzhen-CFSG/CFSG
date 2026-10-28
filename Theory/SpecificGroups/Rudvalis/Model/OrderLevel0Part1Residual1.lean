module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual1.Points0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual1.Points1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual1.Points2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual1.Points3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual1.Points4
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual1.Points5
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual1.Points6
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual1.Points7
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-1 residual certificate, indices 71–141

The certified composition tables establish all 71 original transitions.
Enumerating the prescribed residual indices gives exactly `residualBatch 1`.
Source: `OrderLevel0Data` and `Part1Residual.target`; table certification
reuses `OrderLevel0Part6Block2` and checks each additional composition.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part1Residual

/-- The second residual batch in the part-1 order certificate. -/
public theorem residuals1 : residualBatch 1 := by
  intro s hs
  fin_cases s
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
  · exact Residual1.point130
  · exact Residual1.point131
  · exact Residual1.point132
  · exact Residual1.point133
  · exact Residual1.point134
  · exact Residual1.point135
  · exact Residual1.point136
  · exact Residual1.point137
  · exact Residual1.point138
  · exact Residual1.point139
  · exact Residual1.point140
  · exact Residual1.point141

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual
