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
private theorem point35Slice0 : pointSliceCheck 0 1565 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice1 : pointSliceCheck 0 1565 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice2 : pointSliceCheck 0 1565 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice3 : pointSliceCheck 0 1565 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice4 : pointSliceCheck 0 1565 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice5 : pointSliceCheck 0 1565 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice6 : pointSliceCheck 0 1565 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice7 : pointSliceCheck 0 1565 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice8 : pointSliceCheck 0 1565 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice9 : pointSliceCheck 0 1565 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice10 : pointSliceCheck 0 1565 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice11 : pointSliceCheck 0 1565 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice12 : pointSliceCheck 0 1565 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice13 : pointSliceCheck 0 1565 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice14 : pointSliceCheck 0 1565 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice15 : pointSliceCheck 0 1565 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice16 : pointSliceCheck 0 1565 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice17 : pointSliceCheck 0 1565 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice18 : pointSliceCheck 0 1565 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice19 : pointSliceCheck 0 1565 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice20 : pointSliceCheck 0 1565 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice21 : pointSliceCheck 0 1565 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice22 : pointSliceCheck 0 1565 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice23 : pointSliceCheck 0 1565 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice24 : pointSliceCheck 0 1565 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice25 : pointSliceCheck 0 1565 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice26 : pointSliceCheck 0 1565 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice27 : pointSliceCheck 0 1565 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice28 : pointSliceCheck 0 1565 28 := by
  decide +kernel

public theorem point35 : residualCheck 35 := by
  apply ofPointSlices 0 1565
  intro c
  fin_cases c
  · exact point35Slice0
  · exact point35Slice1
  · exact point35Slice2
  · exact point35Slice3
  · exact point35Slice4
  · exact point35Slice5
  · exact point35Slice6
  · exact point35Slice7
  · exact point35Slice8
  · exact point35Slice9
  · exact point35Slice10
  · exact point35Slice11
  · exact point35Slice12
  · exact point35Slice13
  · exact point35Slice14
  · exact point35Slice15
  · exact point35Slice16
  · exact point35Slice17
  · exact point35Slice18
  · exact point35Slice19
  · exact point35Slice20
  · exact point35Slice21
  · exact point35Slice22
  · exact point35Slice23
  · exact point35Slice24
  · exact point35Slice25
  · exact point35Slice26
  · exact point35Slice27
  · exact point35Slice28

set_option maxHeartbeats 1600000 in
private theorem point36Slice0 : pointSliceCheck 0 1568 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice1 : pointSliceCheck 0 1568 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice2 : pointSliceCheck 0 1568 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice3 : pointSliceCheck 0 1568 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice4 : pointSliceCheck 0 1568 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice5 : pointSliceCheck 0 1568 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice6 : pointSliceCheck 0 1568 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice7 : pointSliceCheck 0 1568 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice8 : pointSliceCheck 0 1568 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice9 : pointSliceCheck 0 1568 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice10 : pointSliceCheck 0 1568 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice11 : pointSliceCheck 0 1568 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice12 : pointSliceCheck 0 1568 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice13 : pointSliceCheck 0 1568 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice14 : pointSliceCheck 0 1568 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice15 : pointSliceCheck 0 1568 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice16 : pointSliceCheck 0 1568 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice17 : pointSliceCheck 0 1568 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice18 : pointSliceCheck 0 1568 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice19 : pointSliceCheck 0 1568 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice20 : pointSliceCheck 0 1568 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice21 : pointSliceCheck 0 1568 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice22 : pointSliceCheck 0 1568 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice23 : pointSliceCheck 0 1568 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice24 : pointSliceCheck 0 1568 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice25 : pointSliceCheck 0 1568 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice26 : pointSliceCheck 0 1568 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice27 : pointSliceCheck 0 1568 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice28 : pointSliceCheck 0 1568 28 := by
  decide +kernel

public theorem point36 : residualCheck 36 := by
  apply ofPointSlices 0 1568
  intro c
  fin_cases c
  · exact point36Slice0
  · exact point36Slice1
  · exact point36Slice2
  · exact point36Slice3
  · exact point36Slice4
  · exact point36Slice5
  · exact point36Slice6
  · exact point36Slice7
  · exact point36Slice8
  · exact point36Slice9
  · exact point36Slice10
  · exact point36Slice11
  · exact point36Slice12
  · exact point36Slice13
  · exact point36Slice14
  · exact point36Slice15
  · exact point36Slice16
  · exact point36Slice17
  · exact point36Slice18
  · exact point36Slice19
  · exact point36Slice20
  · exact point36Slice21
  · exact point36Slice22
  · exact point36Slice23
  · exact point36Slice24
  · exact point36Slice25
  · exact point36Slice26
  · exact point36Slice27
  · exact point36Slice28

set_option maxHeartbeats 1600000 in
private theorem point37Slice0 : pointSliceCheck 0 1571 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice1 : pointSliceCheck 0 1571 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice2 : pointSliceCheck 0 1571 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice3 : pointSliceCheck 0 1571 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice4 : pointSliceCheck 0 1571 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice5 : pointSliceCheck 0 1571 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice6 : pointSliceCheck 0 1571 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice7 : pointSliceCheck 0 1571 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice8 : pointSliceCheck 0 1571 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice9 : pointSliceCheck 0 1571 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice10 : pointSliceCheck 0 1571 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice11 : pointSliceCheck 0 1571 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice12 : pointSliceCheck 0 1571 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice13 : pointSliceCheck 0 1571 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice14 : pointSliceCheck 0 1571 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice15 : pointSliceCheck 0 1571 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice16 : pointSliceCheck 0 1571 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice17 : pointSliceCheck 0 1571 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice18 : pointSliceCheck 0 1571 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice19 : pointSliceCheck 0 1571 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice20 : pointSliceCheck 0 1571 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice21 : pointSliceCheck 0 1571 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice22 : pointSliceCheck 0 1571 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice23 : pointSliceCheck 0 1571 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice24 : pointSliceCheck 0 1571 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice25 : pointSliceCheck 0 1571 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice26 : pointSliceCheck 0 1571 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice27 : pointSliceCheck 0 1571 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice28 : pointSliceCheck 0 1571 28 := by
  decide +kernel

public theorem point37 : residualCheck 37 := by
  apply ofPointSlices 0 1571
  intro c
  fin_cases c
  · exact point37Slice0
  · exact point37Slice1
  · exact point37Slice2
  · exact point37Slice3
  · exact point37Slice4
  · exact point37Slice5
  · exact point37Slice6
  · exact point37Slice7
  · exact point37Slice8
  · exact point37Slice9
  · exact point37Slice10
  · exact point37Slice11
  · exact point37Slice12
  · exact point37Slice13
  · exact point37Slice14
  · exact point37Slice15
  · exact point37Slice16
  · exact point37Slice17
  · exact point37Slice18
  · exact point37Slice19
  · exact point37Slice20
  · exact point37Slice21
  · exact point37Slice22
  · exact point37Slice23
  · exact point37Slice24
  · exact point37Slice25
  · exact point37Slice26
  · exact point37Slice27
  · exact point37Slice28

set_option maxHeartbeats 1600000 in
private theorem point38Slice0 : pointSliceCheck 1 1560 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice1 : pointSliceCheck 1 1560 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice2 : pointSliceCheck 1 1560 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice3 : pointSliceCheck 1 1560 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice4 : pointSliceCheck 1 1560 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice5 : pointSliceCheck 1 1560 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice6 : pointSliceCheck 1 1560 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice7 : pointSliceCheck 1 1560 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice8 : pointSliceCheck 1 1560 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice9 : pointSliceCheck 1 1560 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice10 : pointSliceCheck 1 1560 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice11 : pointSliceCheck 1 1560 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice12 : pointSliceCheck 1 1560 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice13 : pointSliceCheck 1 1560 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice14 : pointSliceCheck 1 1560 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice15 : pointSliceCheck 1 1560 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice16 : pointSliceCheck 1 1560 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice17 : pointSliceCheck 1 1560 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice18 : pointSliceCheck 1 1560 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice19 : pointSliceCheck 1 1560 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice20 : pointSliceCheck 1 1560 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice21 : pointSliceCheck 1 1560 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice22 : pointSliceCheck 1 1560 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice23 : pointSliceCheck 1 1560 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice24 : pointSliceCheck 1 1560 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice25 : pointSliceCheck 1 1560 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice26 : pointSliceCheck 1 1560 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice27 : pointSliceCheck 1 1560 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice28 : pointSliceCheck 1 1560 28 := by
  decide +kernel

public theorem point38 : residualCheck 38 := by
  apply ofPointSlices 1 1560
  intro c
  fin_cases c
  · exact point38Slice0
  · exact point38Slice1
  · exact point38Slice2
  · exact point38Slice3
  · exact point38Slice4
  · exact point38Slice5
  · exact point38Slice6
  · exact point38Slice7
  · exact point38Slice8
  · exact point38Slice9
  · exact point38Slice10
  · exact point38Slice11
  · exact point38Slice12
  · exact point38Slice13
  · exact point38Slice14
  · exact point38Slice15
  · exact point38Slice16
  · exact point38Slice17
  · exact point38Slice18
  · exact point38Slice19
  · exact point38Slice20
  · exact point38Slice21
  · exact point38Slice22
  · exact point38Slice23
  · exact point38Slice24
  · exact point38Slice25
  · exact point38Slice26
  · exact point38Slice27
  · exact point38Slice28

set_option maxHeartbeats 1600000 in
private theorem point39Slice0 : pointSliceCheck 1 1564 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice1 : pointSliceCheck 1 1564 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice2 : pointSliceCheck 1 1564 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice3 : pointSliceCheck 1 1564 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice4 : pointSliceCheck 1 1564 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice5 : pointSliceCheck 1 1564 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice6 : pointSliceCheck 1 1564 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice7 : pointSliceCheck 1 1564 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice8 : pointSliceCheck 1 1564 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice9 : pointSliceCheck 1 1564 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice10 : pointSliceCheck 1 1564 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice11 : pointSliceCheck 1 1564 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice12 : pointSliceCheck 1 1564 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice13 : pointSliceCheck 1 1564 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice14 : pointSliceCheck 1 1564 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice15 : pointSliceCheck 1 1564 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice16 : pointSliceCheck 1 1564 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice17 : pointSliceCheck 1 1564 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice18 : pointSliceCheck 1 1564 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice19 : pointSliceCheck 1 1564 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice20 : pointSliceCheck 1 1564 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice21 : pointSliceCheck 1 1564 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice22 : pointSliceCheck 1 1564 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice23 : pointSliceCheck 1 1564 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice24 : pointSliceCheck 1 1564 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice25 : pointSliceCheck 1 1564 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice26 : pointSliceCheck 1 1564 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice27 : pointSliceCheck 1 1564 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice28 : pointSliceCheck 1 1564 28 := by
  decide +kernel

public theorem point39 : residualCheck 39 := by
  apply ofPointSlices 1 1564
  intro c
  fin_cases c
  · exact point39Slice0
  · exact point39Slice1
  · exact point39Slice2
  · exact point39Slice3
  · exact point39Slice4
  · exact point39Slice5
  · exact point39Slice6
  · exact point39Slice7
  · exact point39Slice8
  · exact point39Slice9
  · exact point39Slice10
  · exact point39Slice11
  · exact point39Slice12
  · exact point39Slice13
  · exact point39Slice14
  · exact point39Slice15
  · exact point39Slice16
  · exact point39Slice17
  · exact point39Slice18
  · exact point39Slice19
  · exact point39Slice20
  · exact point39Slice21
  · exact point39Slice22
  · exact point39Slice23
  · exact point39Slice24
  · exact point39Slice25
  · exact point39Slice26
  · exact point39Slice27
  · exact point39Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
