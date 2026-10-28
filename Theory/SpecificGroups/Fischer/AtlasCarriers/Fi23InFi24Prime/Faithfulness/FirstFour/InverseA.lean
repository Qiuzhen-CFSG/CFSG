module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.InverseCheck

/-!
# Kernel certificate for the packed A inverse law

Each leaf checks 4096 points; 75 leaves cover all ambient labels. Joining
already checked leaves avoids repeating their reductions. These are checks
of the numerical permutation model, not comparisons with `WordSetup`.
Source: ATLAS F24G1-p306936B0, GLS3 Table 5.3v; `source/generate_model.py`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
open Certificate

private theorem blockA0 : checkPow squareTest 0 12 = true := by
  decide +kernel

private theorem blockA1 : checkPow squareTest 4096 12 = true := by
  decide +kernel

private theorem blockA2 : checkPow squareTest 8192 12 = true := by
  decide +kernel

private theorem blockA3 : checkPow squareTest 12288 12 = true := by
  decide +kernel

private theorem blockA4 : checkPow squareTest 16384 12 = true := by
  decide +kernel

private theorem blockA5 : checkPow squareTest 20480 12 = true := by
  decide +kernel

private theorem blockA6 : checkPow squareTest 24576 12 = true := by
  decide +kernel

private theorem blockA7 : checkPow squareTest 28672 12 = true := by
  decide +kernel

private theorem blockA8 : checkPow squareTest 32768 12 = true := by
  decide +kernel

private theorem blockA9 : checkPow squareTest 36864 12 = true := by
  decide +kernel

private theorem blockA10 : checkPow squareTest 40960 12 = true := by
  decide +kernel

private theorem blockA11 : checkPow squareTest 45056 12 = true := by
  decide +kernel

private theorem blockA12 : checkPow squareTest 49152 12 = true := by
  decide +kernel

private theorem blockA13 : checkPow squareTest 53248 12 = true := by
  decide +kernel

private theorem blockA14 : checkPow squareTest 57344 12 = true := by
  decide +kernel

private theorem blockA15 : checkPow squareTest 61440 12 = true := by
  decide +kernel

private theorem blockA16 : checkPow squareTest 65536 12 = true := by
  decide +kernel

private theorem blockA17 : checkPow squareTest 69632 12 = true := by
  decide +kernel

private theorem blockA18 : checkPow squareTest 73728 12 = true := by
  decide +kernel

private theorem blockA19 : checkPow squareTest 77824 12 = true := by
  decide +kernel

private theorem blockA20 : checkPow squareTest 81920 12 = true := by
  decide +kernel

private theorem blockA21 : checkPow squareTest 86016 12 = true := by
  decide +kernel

private theorem blockA22 : checkPow squareTest 90112 12 = true := by
  decide +kernel

private theorem blockA23 : checkPow squareTest 94208 12 = true := by
  decide +kernel

private theorem blockA24 : checkPow squareTest 98304 12 = true := by
  decide +kernel

private theorem blockA25 : checkPow squareTest 102400 12 = true := by
  decide +kernel

private theorem blockA26 : checkPow squareTest 106496 12 = true := by
  decide +kernel

private theorem blockA27 : checkPow squareTest 110592 12 = true := by
  decide +kernel

private theorem blockA28 : checkPow squareTest 114688 12 = true := by
  decide +kernel

private theorem blockA29 : checkPow squareTest 118784 12 = true := by
  decide +kernel

private theorem blockA30 : checkPow squareTest 122880 12 = true := by
  decide +kernel

private theorem blockA31 : checkPow squareTest 126976 12 = true := by
  decide +kernel

private theorem blockA32 : checkPow squareTest 131072 12 = true := by
  decide +kernel

private theorem blockA33 : checkPow squareTest 135168 12 = true := by
  decide +kernel

private theorem blockA34 : checkPow squareTest 139264 12 = true := by
  decide +kernel

private theorem blockA35 : checkPow squareTest 143360 12 = true := by
  decide +kernel

private theorem blockA36 : checkPow squareTest 147456 12 = true := by
  decide +kernel

private theorem blockA37 : checkPow squareTest 151552 12 = true := by
  decide +kernel

private theorem blockA38 : checkPow squareTest 155648 12 = true := by
  decide +kernel

private theorem blockA39 : checkPow squareTest 159744 12 = true := by
  decide +kernel

private theorem blockA40 : checkPow squareTest 163840 12 = true := by
  decide +kernel

private theorem blockA41 : checkPow squareTest 167936 12 = true := by
  decide +kernel

private theorem blockA42 : checkPow squareTest 172032 12 = true := by
  decide +kernel

private theorem blockA43 : checkPow squareTest 176128 12 = true := by
  decide +kernel

private theorem blockA44 : checkPow squareTest 180224 12 = true := by
  decide +kernel

private theorem blockA45 : checkPow squareTest 184320 12 = true := by
  decide +kernel

private theorem blockA46 : checkPow squareTest 188416 12 = true := by
  decide +kernel

private theorem blockA47 : checkPow squareTest 192512 12 = true := by
  decide +kernel

private theorem blockA48 : checkPow squareTest 196608 12 = true := by
  decide +kernel

private theorem blockA49 : checkPow squareTest 200704 12 = true := by
  decide +kernel

private theorem blockA50 : checkPow squareTest 204800 12 = true := by
  decide +kernel

private theorem blockA51 : checkPow squareTest 208896 12 = true := by
  decide +kernel

private theorem blockA52 : checkPow squareTest 212992 12 = true := by
  decide +kernel

private theorem blockA53 : checkPow squareTest 217088 12 = true := by
  decide +kernel

private theorem blockA54 : checkPow squareTest 221184 12 = true := by
  decide +kernel

private theorem blockA55 : checkPow squareTest 225280 12 = true := by
  decide +kernel

private theorem blockA56 : checkPow squareTest 229376 12 = true := by
  decide +kernel

private theorem blockA57 : checkPow squareTest 233472 12 = true := by
  decide +kernel

private theorem blockA58 : checkPow squareTest 237568 12 = true := by
  decide +kernel

private theorem blockA59 : checkPow squareTest 241664 12 = true := by
  decide +kernel

private theorem blockA60 : checkPow squareTest 245760 12 = true := by
  decide +kernel

private theorem blockA61 : checkPow squareTest 249856 12 = true := by
  decide +kernel

private theorem blockA62 : checkPow squareTest 253952 12 = true := by
  decide +kernel

private theorem blockA63 : checkPow squareTest 258048 12 = true := by
  decide +kernel

private theorem blockA64 : checkPow squareTest 262144 12 = true := by
  decide +kernel

private theorem blockA65 : checkPow squareTest 266240 12 = true := by
  decide +kernel

private theorem blockA66 : checkPow squareTest 270336 12 = true := by
  decide +kernel

private theorem blockA67 : checkPow squareTest 274432 12 = true := by
  decide +kernel

private theorem blockA68 : checkPow squareTest 278528 12 = true := by
  decide +kernel

private theorem blockA69 : checkPow squareTest 282624 12 = true := by
  decide +kernel

private theorem blockA70 : checkPow squareTest 286720 12 = true := by
  decide +kernel

private theorem blockA71 : checkPow squareTest 290816 12 = true := by
  decide +kernel

private theorem blockA72 : checkPow squareTest 294912 12 = true := by
  decide +kernel

private theorem blockA73 : checkPow squareTest 299008 12 = true := by
  decide +kernel

private theorem blockA74 : checkPow squareTest 303104 12 = true := by
  decide +kernel

private theorem intervalA0 : checkPow squareTest 0 18 = true :=
  (checkPow_join squareTest 17 0 (checkPow_join squareTest 16 0 (checkPow_join squareTest 15 0 (checkPow_join squareTest 14 0 (checkPow_join squareTest 13 0 (checkPow_join squareTest 12 0 blockA0 blockA1) (checkPow_join squareTest 12 8192 blockA2 blockA3)) (checkPow_join squareTest 13 16384 (checkPow_join squareTest 12 16384 blockA4 blockA5) (checkPow_join squareTest 12 24576 blockA6 blockA7))) (checkPow_join squareTest 14 32768 (checkPow_join squareTest 13 32768 (checkPow_join squareTest 12 32768 blockA8 blockA9) (checkPow_join squareTest 12 40960 blockA10 blockA11)) (checkPow_join squareTest 13 49152 (checkPow_join squareTest 12 49152 blockA12 blockA13) (checkPow_join squareTest 12 57344 blockA14 blockA15)))) (checkPow_join squareTest 15 65536 (checkPow_join squareTest 14 65536 (checkPow_join squareTest 13 65536 (checkPow_join squareTest 12 65536 blockA16 blockA17) (checkPow_join squareTest 12 73728 blockA18 blockA19)) (checkPow_join squareTest 13 81920 (checkPow_join squareTest 12 81920 blockA20 blockA21) (checkPow_join squareTest 12 90112 blockA22 blockA23))) (checkPow_join squareTest 14 98304 (checkPow_join squareTest 13 98304 (checkPow_join squareTest 12 98304 blockA24 blockA25) (checkPow_join squareTest 12 106496 blockA26 blockA27)) (checkPow_join squareTest 13 114688 (checkPow_join squareTest 12 114688 blockA28 blockA29) (checkPow_join squareTest 12 122880 blockA30 blockA31))))) (checkPow_join squareTest 16 131072 (checkPow_join squareTest 15 131072 (checkPow_join squareTest 14 131072 (checkPow_join squareTest 13 131072 (checkPow_join squareTest 12 131072 blockA32 blockA33) (checkPow_join squareTest 12 139264 blockA34 blockA35)) (checkPow_join squareTest 13 147456 (checkPow_join squareTest 12 147456 blockA36 blockA37) (checkPow_join squareTest 12 155648 blockA38 blockA39))) (checkPow_join squareTest 14 163840 (checkPow_join squareTest 13 163840 (checkPow_join squareTest 12 163840 blockA40 blockA41) (checkPow_join squareTest 12 172032 blockA42 blockA43)) (checkPow_join squareTest 13 180224 (checkPow_join squareTest 12 180224 blockA44 blockA45) (checkPow_join squareTest 12 188416 blockA46 blockA47)))) (checkPow_join squareTest 15 196608 (checkPow_join squareTest 14 196608 (checkPow_join squareTest 13 196608 (checkPow_join squareTest 12 196608 blockA48 blockA49) (checkPow_join squareTest 12 204800 blockA50 blockA51)) (checkPow_join squareTest 13 212992 (checkPow_join squareTest 12 212992 blockA52 blockA53) (checkPow_join squareTest 12 221184 blockA54 blockA55))) (checkPow_join squareTest 14 229376 (checkPow_join squareTest 13 229376 (checkPow_join squareTest 12 229376 blockA56 blockA57) (checkPow_join squareTest 12 237568 blockA58 blockA59)) (checkPow_join squareTest 13 245760 (checkPow_join squareTest 12 245760 blockA60 blockA61) (checkPow_join squareTest 12 253952 blockA62 blockA63))))))

private theorem intervalA1 : checkPow squareTest 262144 15 = true :=
  (checkPow_join squareTest 14 262144 (checkPow_join squareTest 13 262144 (checkPow_join squareTest 12 262144 blockA64 blockA65) (checkPow_join squareTest 12 270336 blockA66 blockA67)) (checkPow_join squareTest 13 278528 (checkPow_join squareTest 12 278528 blockA68 blockA69) (checkPow_join squareTest 12 286720 blockA70 blockA71)))

private theorem intervalA2 : checkPow squareTest 294912 13 = true :=
  (checkPow_join squareTest 12 294912 blockA72 blockA73)

private theorem intervalA3 : checkPow squareTest 303104 12 = true :=
  blockA74

/-- The packed A table has its asserted inverse on every ambient letter. -/
theorem imageA_involutive : Function.Involutive imageA :=
  imageA_involutive_of_checks (covered_checks squareTest
    intervalA0 intervalA1 intervalA2 intervalA3)

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
