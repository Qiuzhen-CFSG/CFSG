module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-0 residual group 0, transitions 35–39

The prescribed permutation identities are checked on 29 slices of 140 points
and then assembled by `ofPointSlices`. Separate slice declarations bound kernel
reduction memory. Source: the witnesses in `OrderLevel0Data` and the exact
transition enumeration `Part0Residual.target` in `OrderLevel0Part0ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point35Slice0 : pointSliceCheck 1 1405 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice1 : pointSliceCheck 1 1405 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice2 : pointSliceCheck 1 1405 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice3 : pointSliceCheck 1 1405 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice4 : pointSliceCheck 1 1405 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice5 : pointSliceCheck 1 1405 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice6 : pointSliceCheck 1 1405 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice7 : pointSliceCheck 1 1405 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice8 : pointSliceCheck 1 1405 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice9 : pointSliceCheck 1 1405 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice10 : pointSliceCheck 1 1405 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice11 : pointSliceCheck 1 1405 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice12 : pointSliceCheck 1 1405 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice13 : pointSliceCheck 1 1405 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice14 : pointSliceCheck 1 1405 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice15 : pointSliceCheck 1 1405 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice16 : pointSliceCheck 1 1405 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice17 : pointSliceCheck 1 1405 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice18 : pointSliceCheck 1 1405 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice19 : pointSliceCheck 1 1405 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice20 : pointSliceCheck 1 1405 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice21 : pointSliceCheck 1 1405 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice22 : pointSliceCheck 1 1405 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice23 : pointSliceCheck 1 1405 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice24 : pointSliceCheck 1 1405 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice25 : pointSliceCheck 1 1405 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice26 : pointSliceCheck 1 1405 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice27 : pointSliceCheck 1 1405 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point35Slice28 : pointSliceCheck 1 1405 28 := by
  decide +kernel

public theorem point35 : residualCheck 35 := by
  apply ofPointSlices 1 1405
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
private theorem point36Slice0 : pointSliceCheck 1 1416 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice1 : pointSliceCheck 1 1416 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice2 : pointSliceCheck 1 1416 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice3 : pointSliceCheck 1 1416 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice4 : pointSliceCheck 1 1416 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice5 : pointSliceCheck 1 1416 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice6 : pointSliceCheck 1 1416 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice7 : pointSliceCheck 1 1416 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice8 : pointSliceCheck 1 1416 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice9 : pointSliceCheck 1 1416 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice10 : pointSliceCheck 1 1416 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice11 : pointSliceCheck 1 1416 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice12 : pointSliceCheck 1 1416 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice13 : pointSliceCheck 1 1416 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice14 : pointSliceCheck 1 1416 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice15 : pointSliceCheck 1 1416 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice16 : pointSliceCheck 1 1416 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice17 : pointSliceCheck 1 1416 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice18 : pointSliceCheck 1 1416 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice19 : pointSliceCheck 1 1416 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice20 : pointSliceCheck 1 1416 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice21 : pointSliceCheck 1 1416 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice22 : pointSliceCheck 1 1416 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice23 : pointSliceCheck 1 1416 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice24 : pointSliceCheck 1 1416 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice25 : pointSliceCheck 1 1416 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice26 : pointSliceCheck 1 1416 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice27 : pointSliceCheck 1 1416 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point36Slice28 : pointSliceCheck 1 1416 28 := by
  decide +kernel

public theorem point36 : residualCheck 36 := by
  apply ofPointSlices 1 1416
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
private theorem point37Slice0 : pointSliceCheck 0 1550 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice1 : pointSliceCheck 0 1550 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice2 : pointSliceCheck 0 1550 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice3 : pointSliceCheck 0 1550 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice4 : pointSliceCheck 0 1550 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice5 : pointSliceCheck 0 1550 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice6 : pointSliceCheck 0 1550 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice7 : pointSliceCheck 0 1550 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice8 : pointSliceCheck 0 1550 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice9 : pointSliceCheck 0 1550 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice10 : pointSliceCheck 0 1550 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice11 : pointSliceCheck 0 1550 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice12 : pointSliceCheck 0 1550 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice13 : pointSliceCheck 0 1550 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice14 : pointSliceCheck 0 1550 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice15 : pointSliceCheck 0 1550 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice16 : pointSliceCheck 0 1550 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice17 : pointSliceCheck 0 1550 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice18 : pointSliceCheck 0 1550 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice19 : pointSliceCheck 0 1550 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice20 : pointSliceCheck 0 1550 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice21 : pointSliceCheck 0 1550 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice22 : pointSliceCheck 0 1550 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice23 : pointSliceCheck 0 1550 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice24 : pointSliceCheck 0 1550 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice25 : pointSliceCheck 0 1550 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice26 : pointSliceCheck 0 1550 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice27 : pointSliceCheck 0 1550 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point37Slice28 : pointSliceCheck 0 1550 28 := by
  decide +kernel

public theorem point37 : residualCheck 37 := by
  apply ofPointSlices 0 1550
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
private theorem point38Slice0 : pointSliceCheck 1 1540 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice1 : pointSliceCheck 1 1540 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice2 : pointSliceCheck 1 1540 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice3 : pointSliceCheck 1 1540 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice4 : pointSliceCheck 1 1540 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice5 : pointSliceCheck 1 1540 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice6 : pointSliceCheck 1 1540 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice7 : pointSliceCheck 1 1540 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice8 : pointSliceCheck 1 1540 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice9 : pointSliceCheck 1 1540 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice10 : pointSliceCheck 1 1540 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice11 : pointSliceCheck 1 1540 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice12 : pointSliceCheck 1 1540 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice13 : pointSliceCheck 1 1540 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice14 : pointSliceCheck 1 1540 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice15 : pointSliceCheck 1 1540 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice16 : pointSliceCheck 1 1540 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice17 : pointSliceCheck 1 1540 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice18 : pointSliceCheck 1 1540 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice19 : pointSliceCheck 1 1540 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice20 : pointSliceCheck 1 1540 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice21 : pointSliceCheck 1 1540 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice22 : pointSliceCheck 1 1540 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice23 : pointSliceCheck 1 1540 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice24 : pointSliceCheck 1 1540 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice25 : pointSliceCheck 1 1540 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice26 : pointSliceCheck 1 1540 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice27 : pointSliceCheck 1 1540 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point38Slice28 : pointSliceCheck 1 1540 28 := by
  decide +kernel

public theorem point38 : residualCheck 38 := by
  apply ofPointSlices 1 1540
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
private theorem point39Slice0 : pointSliceCheck 1 1547 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice1 : pointSliceCheck 1 1547 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice2 : pointSliceCheck 1 1547 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice3 : pointSliceCheck 1 1547 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice4 : pointSliceCheck 1 1547 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice5 : pointSliceCheck 1 1547 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice6 : pointSliceCheck 1 1547 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice7 : pointSliceCheck 1 1547 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice8 : pointSliceCheck 1 1547 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice9 : pointSliceCheck 1 1547 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice10 : pointSliceCheck 1 1547 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice11 : pointSliceCheck 1 1547 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice12 : pointSliceCheck 1 1547 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice13 : pointSliceCheck 1 1547 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice14 : pointSliceCheck 1 1547 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice15 : pointSliceCheck 1 1547 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice16 : pointSliceCheck 1 1547 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice17 : pointSliceCheck 1 1547 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice18 : pointSliceCheck 1 1547 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice19 : pointSliceCheck 1 1547 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice20 : pointSliceCheck 1 1547 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice21 : pointSliceCheck 1 1547 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice22 : pointSliceCheck 1 1547 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice23 : pointSliceCheck 1 1547 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice24 : pointSliceCheck 1 1547 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice25 : pointSliceCheck 1 1547 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice26 : pointSliceCheck 1 1547 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice27 : pointSliceCheck 1 1547 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point39Slice28 : pointSliceCheck 1 1547 28 := by
  decide +kernel

public theorem point39 : residualCheck 39 := by
  apply ofPointSlices 1 1547
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

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
