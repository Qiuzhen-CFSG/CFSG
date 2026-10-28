module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.InverseCheck

/-!
# Kernel certificate for the packed B inverse law

Each leaf checks 4096 points; 75 leaves cover all ambient labels. Joining
already checked leaves avoids repeating their reductions. These are checks
of the numerical permutation model, not comparisons with `WordSetup`.
Source: ATLAS F24G1-p306936B0, GLS3 Table 5.3v; `source/generate_model.py`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
open Certificate

private theorem blockB0 : checkPow cubeTest 0 12 = true := by
  decide +kernel

private theorem blockB1 : checkPow cubeTest 4096 12 = true := by
  decide +kernel

private theorem blockB2 : checkPow cubeTest 8192 12 = true := by
  decide +kernel

private theorem blockB3 : checkPow cubeTest 12288 12 = true := by
  decide +kernel

private theorem blockB4 : checkPow cubeTest 16384 12 = true := by
  decide +kernel

private theorem blockB5 : checkPow cubeTest 20480 12 = true := by
  decide +kernel

private theorem blockB6 : checkPow cubeTest 24576 12 = true := by
  decide +kernel

private theorem blockB7 : checkPow cubeTest 28672 12 = true := by
  decide +kernel

private theorem blockB8 : checkPow cubeTest 32768 12 = true := by
  decide +kernel

private theorem blockB9 : checkPow cubeTest 36864 12 = true := by
  decide +kernel

private theorem blockB10 : checkPow cubeTest 40960 12 = true := by
  decide +kernel

private theorem blockB11 : checkPow cubeTest 45056 12 = true := by
  decide +kernel

private theorem blockB12 : checkPow cubeTest 49152 12 = true := by
  decide +kernel

private theorem blockB13 : checkPow cubeTest 53248 12 = true := by
  decide +kernel

private theorem blockB14 : checkPow cubeTest 57344 12 = true := by
  decide +kernel

private theorem blockB15 : checkPow cubeTest 61440 12 = true := by
  decide +kernel

private theorem blockB16 : checkPow cubeTest 65536 12 = true := by
  decide +kernel

private theorem blockB17 : checkPow cubeTest 69632 12 = true := by
  decide +kernel

private theorem blockB18 : checkPow cubeTest 73728 12 = true := by
  decide +kernel

private theorem blockB19 : checkPow cubeTest 77824 12 = true := by
  decide +kernel

private theorem blockB20 : checkPow cubeTest 81920 12 = true := by
  decide +kernel

private theorem blockB21 : checkPow cubeTest 86016 12 = true := by
  decide +kernel

private theorem blockB22 : checkPow cubeTest 90112 12 = true := by
  decide +kernel

private theorem blockB23 : checkPow cubeTest 94208 12 = true := by
  decide +kernel

private theorem blockB24 : checkPow cubeTest 98304 12 = true := by
  decide +kernel

private theorem blockB25 : checkPow cubeTest 102400 12 = true := by
  decide +kernel

private theorem blockB26 : checkPow cubeTest 106496 12 = true := by
  decide +kernel

private theorem blockB27 : checkPow cubeTest 110592 12 = true := by
  decide +kernel

private theorem blockB28 : checkPow cubeTest 114688 12 = true := by
  decide +kernel

private theorem blockB29 : checkPow cubeTest 118784 12 = true := by
  decide +kernel

private theorem blockB30 : checkPow cubeTest 122880 12 = true := by
  decide +kernel

private theorem blockB31 : checkPow cubeTest 126976 12 = true := by
  decide +kernel

private theorem blockB32 : checkPow cubeTest 131072 12 = true := by
  decide +kernel

private theorem blockB33 : checkPow cubeTest 135168 12 = true := by
  decide +kernel

private theorem blockB34 : checkPow cubeTest 139264 12 = true := by
  decide +kernel

private theorem blockB35 : checkPow cubeTest 143360 12 = true := by
  decide +kernel

private theorem blockB36 : checkPow cubeTest 147456 12 = true := by
  decide +kernel

private theorem blockB37 : checkPow cubeTest 151552 12 = true := by
  decide +kernel

private theorem blockB38 : checkPow cubeTest 155648 12 = true := by
  decide +kernel

private theorem blockB39 : checkPow cubeTest 159744 12 = true := by
  decide +kernel

private theorem blockB40 : checkPow cubeTest 163840 12 = true := by
  decide +kernel

private theorem blockB41 : checkPow cubeTest 167936 12 = true := by
  decide +kernel

private theorem blockB42 : checkPow cubeTest 172032 12 = true := by
  decide +kernel

private theorem blockB43 : checkPow cubeTest 176128 12 = true := by
  decide +kernel

private theorem blockB44 : checkPow cubeTest 180224 12 = true := by
  decide +kernel

private theorem blockB45 : checkPow cubeTest 184320 12 = true := by
  decide +kernel

private theorem blockB46 : checkPow cubeTest 188416 12 = true := by
  decide +kernel

private theorem blockB47 : checkPow cubeTest 192512 12 = true := by
  decide +kernel

private theorem blockB48 : checkPow cubeTest 196608 12 = true := by
  decide +kernel

private theorem blockB49 : checkPow cubeTest 200704 12 = true := by
  decide +kernel

private theorem blockB50 : checkPow cubeTest 204800 12 = true := by
  decide +kernel

private theorem blockB51 : checkPow cubeTest 208896 12 = true := by
  decide +kernel

private theorem blockB52 : checkPow cubeTest 212992 12 = true := by
  decide +kernel

private theorem blockB53 : checkPow cubeTest 217088 12 = true := by
  decide +kernel

private theorem blockB54 : checkPow cubeTest 221184 12 = true := by
  decide +kernel

private theorem blockB55 : checkPow cubeTest 225280 12 = true := by
  decide +kernel

private theorem blockB56 : checkPow cubeTest 229376 12 = true := by
  decide +kernel

private theorem blockB57 : checkPow cubeTest 233472 12 = true := by
  decide +kernel

private theorem blockB58 : checkPow cubeTest 237568 12 = true := by
  decide +kernel

private theorem blockB59 : checkPow cubeTest 241664 12 = true := by
  decide +kernel

private theorem blockB60 : checkPow cubeTest 245760 12 = true := by
  decide +kernel

private theorem blockB61 : checkPow cubeTest 249856 12 = true := by
  decide +kernel

private theorem blockB62 : checkPow cubeTest 253952 12 = true := by
  decide +kernel

private theorem blockB63 : checkPow cubeTest 258048 12 = true := by
  decide +kernel

private theorem blockB64 : checkPow cubeTest 262144 12 = true := by
  decide +kernel

private theorem blockB65 : checkPow cubeTest 266240 12 = true := by
  decide +kernel

private theorem blockB66 : checkPow cubeTest 270336 12 = true := by
  decide +kernel

private theorem blockB67 : checkPow cubeTest 274432 12 = true := by
  decide +kernel

private theorem blockB68 : checkPow cubeTest 278528 12 = true := by
  decide +kernel

private theorem blockB69 : checkPow cubeTest 282624 12 = true := by
  decide +kernel

private theorem blockB70 : checkPow cubeTest 286720 12 = true := by
  decide +kernel

private theorem blockB71 : checkPow cubeTest 290816 12 = true := by
  decide +kernel

private theorem blockB72 : checkPow cubeTest 294912 12 = true := by
  decide +kernel

private theorem blockB73 : checkPow cubeTest 299008 12 = true := by
  decide +kernel

private theorem blockB74 : checkPow cubeTest 303104 12 = true := by
  decide +kernel

private theorem intervalB0 : checkPow cubeTest 0 18 = true :=
  (checkPow_join cubeTest 17 0 (checkPow_join cubeTest 16 0 (checkPow_join cubeTest 15 0 (checkPow_join cubeTest 14 0 (checkPow_join cubeTest 13 0 (checkPow_join cubeTest 12 0 blockB0 blockB1) (checkPow_join cubeTest 12 8192 blockB2 blockB3)) (checkPow_join cubeTest 13 16384 (checkPow_join cubeTest 12 16384 blockB4 blockB5) (checkPow_join cubeTest 12 24576 blockB6 blockB7))) (checkPow_join cubeTest 14 32768 (checkPow_join cubeTest 13 32768 (checkPow_join cubeTest 12 32768 blockB8 blockB9) (checkPow_join cubeTest 12 40960 blockB10 blockB11)) (checkPow_join cubeTest 13 49152 (checkPow_join cubeTest 12 49152 blockB12 blockB13) (checkPow_join cubeTest 12 57344 blockB14 blockB15)))) (checkPow_join cubeTest 15 65536 (checkPow_join cubeTest 14 65536 (checkPow_join cubeTest 13 65536 (checkPow_join cubeTest 12 65536 blockB16 blockB17) (checkPow_join cubeTest 12 73728 blockB18 blockB19)) (checkPow_join cubeTest 13 81920 (checkPow_join cubeTest 12 81920 blockB20 blockB21) (checkPow_join cubeTest 12 90112 blockB22 blockB23))) (checkPow_join cubeTest 14 98304 (checkPow_join cubeTest 13 98304 (checkPow_join cubeTest 12 98304 blockB24 blockB25) (checkPow_join cubeTest 12 106496 blockB26 blockB27)) (checkPow_join cubeTest 13 114688 (checkPow_join cubeTest 12 114688 blockB28 blockB29) (checkPow_join cubeTest 12 122880 blockB30 blockB31))))) (checkPow_join cubeTest 16 131072 (checkPow_join cubeTest 15 131072 (checkPow_join cubeTest 14 131072 (checkPow_join cubeTest 13 131072 (checkPow_join cubeTest 12 131072 blockB32 blockB33) (checkPow_join cubeTest 12 139264 blockB34 blockB35)) (checkPow_join cubeTest 13 147456 (checkPow_join cubeTest 12 147456 blockB36 blockB37) (checkPow_join cubeTest 12 155648 blockB38 blockB39))) (checkPow_join cubeTest 14 163840 (checkPow_join cubeTest 13 163840 (checkPow_join cubeTest 12 163840 blockB40 blockB41) (checkPow_join cubeTest 12 172032 blockB42 blockB43)) (checkPow_join cubeTest 13 180224 (checkPow_join cubeTest 12 180224 blockB44 blockB45) (checkPow_join cubeTest 12 188416 blockB46 blockB47)))) (checkPow_join cubeTest 15 196608 (checkPow_join cubeTest 14 196608 (checkPow_join cubeTest 13 196608 (checkPow_join cubeTest 12 196608 blockB48 blockB49) (checkPow_join cubeTest 12 204800 blockB50 blockB51)) (checkPow_join cubeTest 13 212992 (checkPow_join cubeTest 12 212992 blockB52 blockB53) (checkPow_join cubeTest 12 221184 blockB54 blockB55))) (checkPow_join cubeTest 14 229376 (checkPow_join cubeTest 13 229376 (checkPow_join cubeTest 12 229376 blockB56 blockB57) (checkPow_join cubeTest 12 237568 blockB58 blockB59)) (checkPow_join cubeTest 13 245760 (checkPow_join cubeTest 12 245760 blockB60 blockB61) (checkPow_join cubeTest 12 253952 blockB62 blockB63))))))

private theorem intervalB1 : checkPow cubeTest 262144 15 = true :=
  (checkPow_join cubeTest 14 262144 (checkPow_join cubeTest 13 262144 (checkPow_join cubeTest 12 262144 blockB64 blockB65) (checkPow_join cubeTest 12 270336 blockB66 blockB67)) (checkPow_join cubeTest 13 278528 (checkPow_join cubeTest 12 278528 blockB68 blockB69) (checkPow_join cubeTest 12 286720 blockB70 blockB71)))

private theorem intervalB2 : checkPow cubeTest 294912 13 = true :=
  (checkPow_join cubeTest 12 294912 blockB72 blockB73)

private theorem intervalB3 : checkPow cubeTest 303104 12 = true :=
  blockB74

/-- The packed B table has its asserted inverse on every ambient letter. -/
theorem imageB_cube : ∀ i, imageB (imageB (imageB i)) = i :=
  imageB_cube_of_checks (covered_checks cubeTest
    intervalB0 intervalB1 intervalB2 intervalB3)

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
