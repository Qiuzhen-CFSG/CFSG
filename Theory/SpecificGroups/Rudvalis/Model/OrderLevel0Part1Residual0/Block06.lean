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
private theorem point30Slice0 : pointSliceCheck 0 1437 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice1 : pointSliceCheck 0 1437 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice2 : pointSliceCheck 0 1437 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice3 : pointSliceCheck 0 1437 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice4 : pointSliceCheck 0 1437 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice5 : pointSliceCheck 0 1437 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice6 : pointSliceCheck 0 1437 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice7 : pointSliceCheck 0 1437 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice8 : pointSliceCheck 0 1437 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice9 : pointSliceCheck 0 1437 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice10 : pointSliceCheck 0 1437 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice11 : pointSliceCheck 0 1437 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice12 : pointSliceCheck 0 1437 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice13 : pointSliceCheck 0 1437 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice14 : pointSliceCheck 0 1437 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice15 : pointSliceCheck 0 1437 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice16 : pointSliceCheck 0 1437 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice17 : pointSliceCheck 0 1437 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice18 : pointSliceCheck 0 1437 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice19 : pointSliceCheck 0 1437 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice20 : pointSliceCheck 0 1437 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice21 : pointSliceCheck 0 1437 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice22 : pointSliceCheck 0 1437 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice23 : pointSliceCheck 0 1437 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice24 : pointSliceCheck 0 1437 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice25 : pointSliceCheck 0 1437 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice26 : pointSliceCheck 0 1437 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice27 : pointSliceCheck 0 1437 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point30Slice28 : pointSliceCheck 0 1437 28 := by
  decide +kernel

public theorem point30 : residualCheck 30 := by
  apply ofPointSlices 0 1437
  intro c
  fin_cases c
  · exact point30Slice0
  · exact point30Slice1
  · exact point30Slice2
  · exact point30Slice3
  · exact point30Slice4
  · exact point30Slice5
  · exact point30Slice6
  · exact point30Slice7
  · exact point30Slice8
  · exact point30Slice9
  · exact point30Slice10
  · exact point30Slice11
  · exact point30Slice12
  · exact point30Slice13
  · exact point30Slice14
  · exact point30Slice15
  · exact point30Slice16
  · exact point30Slice17
  · exact point30Slice18
  · exact point30Slice19
  · exact point30Slice20
  · exact point30Slice21
  · exact point30Slice22
  · exact point30Slice23
  · exact point30Slice24
  · exact point30Slice25
  · exact point30Slice26
  · exact point30Slice27
  · exact point30Slice28

set_option maxHeartbeats 1600000 in
private theorem point31Slice0 : pointSliceCheck 0 1439 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice1 : pointSliceCheck 0 1439 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice2 : pointSliceCheck 0 1439 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice3 : pointSliceCheck 0 1439 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice4 : pointSliceCheck 0 1439 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice5 : pointSliceCheck 0 1439 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice6 : pointSliceCheck 0 1439 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice7 : pointSliceCheck 0 1439 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice8 : pointSliceCheck 0 1439 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice9 : pointSliceCheck 0 1439 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice10 : pointSliceCheck 0 1439 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice11 : pointSliceCheck 0 1439 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice12 : pointSliceCheck 0 1439 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice13 : pointSliceCheck 0 1439 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice14 : pointSliceCheck 0 1439 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice15 : pointSliceCheck 0 1439 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice16 : pointSliceCheck 0 1439 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice17 : pointSliceCheck 0 1439 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice18 : pointSliceCheck 0 1439 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice19 : pointSliceCheck 0 1439 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice20 : pointSliceCheck 0 1439 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice21 : pointSliceCheck 0 1439 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice22 : pointSliceCheck 0 1439 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice23 : pointSliceCheck 0 1439 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice24 : pointSliceCheck 0 1439 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice25 : pointSliceCheck 0 1439 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice26 : pointSliceCheck 0 1439 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice27 : pointSliceCheck 0 1439 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point31Slice28 : pointSliceCheck 0 1439 28 := by
  decide +kernel

public theorem point31 : residualCheck 31 := by
  apply ofPointSlices 0 1439
  intro c
  fin_cases c
  · exact point31Slice0
  · exact point31Slice1
  · exact point31Slice2
  · exact point31Slice3
  · exact point31Slice4
  · exact point31Slice5
  · exact point31Slice6
  · exact point31Slice7
  · exact point31Slice8
  · exact point31Slice9
  · exact point31Slice10
  · exact point31Slice11
  · exact point31Slice12
  · exact point31Slice13
  · exact point31Slice14
  · exact point31Slice15
  · exact point31Slice16
  · exact point31Slice17
  · exact point31Slice18
  · exact point31Slice19
  · exact point31Slice20
  · exact point31Slice21
  · exact point31Slice22
  · exact point31Slice23
  · exact point31Slice24
  · exact point31Slice25
  · exact point31Slice26
  · exact point31Slice27
  · exact point31Slice28

set_option maxHeartbeats 1600000 in
private theorem point32Slice0 : pointSliceCheck 1 1426 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice1 : pointSliceCheck 1 1426 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice2 : pointSliceCheck 1 1426 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice3 : pointSliceCheck 1 1426 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice4 : pointSliceCheck 1 1426 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice5 : pointSliceCheck 1 1426 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice6 : pointSliceCheck 1 1426 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice7 : pointSliceCheck 1 1426 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice8 : pointSliceCheck 1 1426 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice9 : pointSliceCheck 1 1426 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice10 : pointSliceCheck 1 1426 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice11 : pointSliceCheck 1 1426 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice12 : pointSliceCheck 1 1426 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice13 : pointSliceCheck 1 1426 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice14 : pointSliceCheck 1 1426 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice15 : pointSliceCheck 1 1426 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice16 : pointSliceCheck 1 1426 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice17 : pointSliceCheck 1 1426 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice18 : pointSliceCheck 1 1426 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice19 : pointSliceCheck 1 1426 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice20 : pointSliceCheck 1 1426 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice21 : pointSliceCheck 1 1426 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice22 : pointSliceCheck 1 1426 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice23 : pointSliceCheck 1 1426 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice24 : pointSliceCheck 1 1426 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice25 : pointSliceCheck 1 1426 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice26 : pointSliceCheck 1 1426 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice27 : pointSliceCheck 1 1426 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point32Slice28 : pointSliceCheck 1 1426 28 := by
  decide +kernel

public theorem point32 : residualCheck 32 := by
  apply ofPointSlices 1 1426
  intro c
  fin_cases c
  · exact point32Slice0
  · exact point32Slice1
  · exact point32Slice2
  · exact point32Slice3
  · exact point32Slice4
  · exact point32Slice5
  · exact point32Slice6
  · exact point32Slice7
  · exact point32Slice8
  · exact point32Slice9
  · exact point32Slice10
  · exact point32Slice11
  · exact point32Slice12
  · exact point32Slice13
  · exact point32Slice14
  · exact point32Slice15
  · exact point32Slice16
  · exact point32Slice17
  · exact point32Slice18
  · exact point32Slice19
  · exact point32Slice20
  · exact point32Slice21
  · exact point32Slice22
  · exact point32Slice23
  · exact point32Slice24
  · exact point32Slice25
  · exact point32Slice26
  · exact point32Slice27
  · exact point32Slice28

set_option maxHeartbeats 1600000 in
private theorem point33Slice0 : pointSliceCheck 1 1432 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice1 : pointSliceCheck 1 1432 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice2 : pointSliceCheck 1 1432 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice3 : pointSliceCheck 1 1432 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice4 : pointSliceCheck 1 1432 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice5 : pointSliceCheck 1 1432 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice6 : pointSliceCheck 1 1432 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice7 : pointSliceCheck 1 1432 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice8 : pointSliceCheck 1 1432 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice9 : pointSliceCheck 1 1432 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice10 : pointSliceCheck 1 1432 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice11 : pointSliceCheck 1 1432 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice12 : pointSliceCheck 1 1432 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice13 : pointSliceCheck 1 1432 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice14 : pointSliceCheck 1 1432 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice15 : pointSliceCheck 1 1432 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice16 : pointSliceCheck 1 1432 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice17 : pointSliceCheck 1 1432 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice18 : pointSliceCheck 1 1432 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice19 : pointSliceCheck 1 1432 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice20 : pointSliceCheck 1 1432 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice21 : pointSliceCheck 1 1432 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice22 : pointSliceCheck 1 1432 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice23 : pointSliceCheck 1 1432 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice24 : pointSliceCheck 1 1432 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice25 : pointSliceCheck 1 1432 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice26 : pointSliceCheck 1 1432 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice27 : pointSliceCheck 1 1432 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point33Slice28 : pointSliceCheck 1 1432 28 := by
  decide +kernel

public theorem point33 : residualCheck 33 := by
  apply ofPointSlices 1 1432
  intro c
  fin_cases c
  · exact point33Slice0
  · exact point33Slice1
  · exact point33Slice2
  · exact point33Slice3
  · exact point33Slice4
  · exact point33Slice5
  · exact point33Slice6
  · exact point33Slice7
  · exact point33Slice8
  · exact point33Slice9
  · exact point33Slice10
  · exact point33Slice11
  · exact point33Slice12
  · exact point33Slice13
  · exact point33Slice14
  · exact point33Slice15
  · exact point33Slice16
  · exact point33Slice17
  · exact point33Slice18
  · exact point33Slice19
  · exact point33Slice20
  · exact point33Slice21
  · exact point33Slice22
  · exact point33Slice23
  · exact point33Slice24
  · exact point33Slice25
  · exact point33Slice26
  · exact point33Slice27
  · exact point33Slice28

set_option maxHeartbeats 1600000 in
private theorem point34Slice0 : pointSliceCheck 0 1560 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice1 : pointSliceCheck 0 1560 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice2 : pointSliceCheck 0 1560 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice3 : pointSliceCheck 0 1560 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice4 : pointSliceCheck 0 1560 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice5 : pointSliceCheck 0 1560 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice6 : pointSliceCheck 0 1560 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice7 : pointSliceCheck 0 1560 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice8 : pointSliceCheck 0 1560 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice9 : pointSliceCheck 0 1560 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice10 : pointSliceCheck 0 1560 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice11 : pointSliceCheck 0 1560 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice12 : pointSliceCheck 0 1560 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice13 : pointSliceCheck 0 1560 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice14 : pointSliceCheck 0 1560 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice15 : pointSliceCheck 0 1560 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice16 : pointSliceCheck 0 1560 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice17 : pointSliceCheck 0 1560 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice18 : pointSliceCheck 0 1560 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice19 : pointSliceCheck 0 1560 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice20 : pointSliceCheck 0 1560 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice21 : pointSliceCheck 0 1560 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice22 : pointSliceCheck 0 1560 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice23 : pointSliceCheck 0 1560 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice24 : pointSliceCheck 0 1560 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice25 : pointSliceCheck 0 1560 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice26 : pointSliceCheck 0 1560 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice27 : pointSliceCheck 0 1560 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point34Slice28 : pointSliceCheck 0 1560 28 := by
  decide +kernel

public theorem point34 : residualCheck 34 := by
  apply ofPointSlices 0 1560
  intro c
  fin_cases c
  · exact point34Slice0
  · exact point34Slice1
  · exact point34Slice2
  · exact point34Slice3
  · exact point34Slice4
  · exact point34Slice5
  · exact point34Slice6
  · exact point34Slice7
  · exact point34Slice8
  · exact point34Slice9
  · exact point34Slice10
  · exact point34Slice11
  · exact point34Slice12
  · exact point34Slice13
  · exact point34Slice14
  · exact point34Slice15
  · exact point34Slice16
  · exact point34Slice17
  · exact point34Slice18
  · exact point34Slice19
  · exact point34Slice20
  · exact point34Slice21
  · exact point34Slice22
  · exact point34Slice23
  · exact point34Slice24
  · exact point34Slice25
  · exact point34Slice26
  · exact point34Slice27
  · exact point34Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
