module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Slices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-1 residual group 0: independently checked transitions

Check the original permutation identities on 29 slices of 140 points and
assemble them with `ofPointSlices`. Separate declarations bound kernel memory.
Source: `OrderLevel0Data` and `OrderLevel0Part1ResidualReduction.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point70Slice0 : pointSliceCheck 1 1980 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice1 : pointSliceCheck 1 1980 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice2 : pointSliceCheck 1 1980 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice3 : pointSliceCheck 1 1980 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice4 : pointSliceCheck 1 1980 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice5 : pointSliceCheck 1 1980 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice6 : pointSliceCheck 1 1980 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice7 : pointSliceCheck 1 1980 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice8 : pointSliceCheck 1 1980 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice9 : pointSliceCheck 1 1980 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice10 : pointSliceCheck 1 1980 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice11 : pointSliceCheck 1 1980 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice12 : pointSliceCheck 1 1980 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice13 : pointSliceCheck 1 1980 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice14 : pointSliceCheck 1 1980 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice15 : pointSliceCheck 1 1980 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice16 : pointSliceCheck 1 1980 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice17 : pointSliceCheck 1 1980 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice18 : pointSliceCheck 1 1980 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice19 : pointSliceCheck 1 1980 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice20 : pointSliceCheck 1 1980 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice21 : pointSliceCheck 1 1980 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice22 : pointSliceCheck 1 1980 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice23 : pointSliceCheck 1 1980 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice24 : pointSliceCheck 1 1980 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice25 : pointSliceCheck 1 1980 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice26 : pointSliceCheck 1 1980 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice27 : pointSliceCheck 1 1980 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice28 : pointSliceCheck 1 1980 28 := by
  decide +kernel

public theorem point70 : residualCheck 70 := by
  apply ofPointSlices 1 1980
  intro c
  fin_cases c
  · exact point70Slice0
  · exact point70Slice1
  · exact point70Slice2
  · exact point70Slice3
  · exact point70Slice4
  · exact point70Slice5
  · exact point70Slice6
  · exact point70Slice7
  · exact point70Slice8
  · exact point70Slice9
  · exact point70Slice10
  · exact point70Slice11
  · exact point70Slice12
  · exact point70Slice13
  · exact point70Slice14
  · exact point70Slice15
  · exact point70Slice16
  · exact point70Slice17
  · exact point70Slice18
  · exact point70Slice19
  · exact point70Slice20
  · exact point70Slice21
  · exact point70Slice22
  · exact point70Slice23
  · exact point70Slice24
  · exact point70Slice25
  · exact point70Slice26
  · exact point70Slice27
  · exact point70Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
