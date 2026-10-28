module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.OrbitActions.Words
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.OrbitActions.DataBase

/-!
# Kernel certificates for shared intermediate actions

Each leaf checks 1024 indices. Already proved leaves are joined without
recomputing them. The resulting action identities apply to the actual ambient
permutations; intermediate tables carry no assumed group structure.
Source: ATLAS F24G1-p306936B0; reproduce with `source/generate.py`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.OrbitActions
open Certificate

private theorem check0_0 : checkPow (baseTest rawA Data.t0) 0 10 = true := by
  decide +kernel

private theorem check0_1 : checkPow (baseTest rawA Data.t0) 1024 10 = true := by
  decide +kernel

private theorem check0_2 : checkPow (baseTest rawA Data.t0) 2048 10 = true := by
  decide +kernel

private theorem check0_3 : checkPow (baseTest rawA Data.t0) 3072 10 = true := by
  decide +kernel

private theorem check0_4 : checkPow (baseTest rawA Data.t0) 4096 10 = true := by
  decide +kernel

private theorem check0_5 : checkPow (baseTest rawA Data.t0) 5120 10 = true := by
  decide +kernel

private theorem check0_6 : checkPow (baseTest rawA Data.t0) 6144 10 = true := by
  decide +kernel

private theorem check0_7 : checkPow (baseTest rawA Data.t0) 7168 10 = true := by
  decide +kernel

private theorem check0_8 : checkPow (baseTest rawA Data.t0) 8192 10 = true := by
  decide +kernel

private theorem check0_9 : checkPow (baseTest rawA Data.t0) 9216 10 = true := by
  decide +kernel

private theorem check0_10 : checkPow (baseTest rawA Data.t0) 10240 10 = true := by
  decide +kernel

private theorem check0_11 : checkPow (baseTest rawA Data.t0) 11264 10 = true := by
  decide +kernel

private theorem check0_12 : checkPow (baseTest rawA Data.t0) 12288 10 = true := by
  decide +kernel

private theorem check0_13 : checkPow (baseTest rawA Data.t0) 13312 10 = true := by
  decide +kernel

private theorem check0_14 : checkPow (baseTest rawA Data.t0) 14336 10 = true := by
  decide +kernel

private theorem check0_15 : checkPow (baseTest rawA Data.t0) 15360 10 = true := by
  decide +kernel

private theorem check0_16 : checkPow (baseTest rawA Data.t0) 16384 10 = true := by
  decide +kernel

private theorem check0_17 : checkPow (baseTest rawA Data.t0) 17408 10 = true := by
  decide +kernel

private theorem check0_18 : checkPow (baseTest rawA Data.t0) 18432 10 = true := by
  decide +kernel

private theorem check0_19 : checkPow (baseTest rawA Data.t0) 19456 10 = true := by
  decide +kernel

private theorem check0_20 : checkPow (baseTest rawA Data.t0) 20480 10 = true := by
  decide +kernel

private theorem check0_21 : checkPow (baseTest rawA Data.t0) 21504 10 = true := by
  decide +kernel

private theorem check0_22 : checkPow (baseTest rawA Data.t0) 22528 10 = true := by
  decide +kernel

private theorem check0_23 : checkPow (baseTest rawA Data.t0) 23552 10 = true := by
  decide +kernel

private theorem check0_24 : checkPow (baseTest rawA Data.t0) 24576 10 = true := by
  decide +kernel

private theorem check0_25 : checkPow (baseTest rawA Data.t0) 25600 10 = true := by
  decide +kernel

private theorem check0_26 : checkPow (baseTest rawA Data.t0) 26624 10 = true := by
  decide +kernel

private theorem check0_27 : checkPow (baseTest rawA Data.t0) 27648 10 = true := by
  decide +kernel

private theorem check0_28 : checkPow (baseTest rawA Data.t0) 28672 10 = true := by
  decide +kernel

private theorem check0_29 : checkPow (baseTest rawA Data.t0) 29696 10 = true := by
  decide +kernel

private theorem check0_30 : checkPow (baseTest rawA Data.t0) 30720 10 = true := by
  decide +kernel

private theorem check0_31 : checkPow (baseTest rawA Data.t0) 31744 10 = true := by
  decide +kernel

private theorem checked0 : checkPow (baseTest rawA Data.t0) 0 15 = true :=
  (checkPow_join (baseTest rawA Data.t0) 14 0 (checkPow_join (baseTest rawA Data.t0) 13 0 (checkPow_join (baseTest rawA Data.t0) 12 0 (checkPow_join (baseTest rawA Data.t0) 11 0 (checkPow_join (baseTest rawA Data.t0) 10 0 check0_0 check0_1) (checkPow_join (baseTest rawA Data.t0) 10 2048 check0_2 check0_3)) (checkPow_join (baseTest rawA Data.t0) 11 4096 (checkPow_join (baseTest rawA Data.t0) 10 4096 check0_4 check0_5) (checkPow_join (baseTest rawA Data.t0) 10 6144 check0_6 check0_7))) (checkPow_join (baseTest rawA Data.t0) 12 8192 (checkPow_join (baseTest rawA Data.t0) 11 8192 (checkPow_join (baseTest rawA Data.t0) 10 8192 check0_8 check0_9) (checkPow_join (baseTest rawA Data.t0) 10 10240 check0_10 check0_11)) (checkPow_join (baseTest rawA Data.t0) 11 12288 (checkPow_join (baseTest rawA Data.t0) 10 12288 check0_12 check0_13) (checkPow_join (baseTest rawA Data.t0) 10 14336 check0_14 check0_15)))) (checkPow_join (baseTest rawA Data.t0) 13 16384 (checkPow_join (baseTest rawA Data.t0) 12 16384 (checkPow_join (baseTest rawA Data.t0) 11 16384 (checkPow_join (baseTest rawA Data.t0) 10 16384 check0_16 check0_17) (checkPow_join (baseTest rawA Data.t0) 10 18432 check0_18 check0_19)) (checkPow_join (baseTest rawA Data.t0) 11 20480 (checkPow_join (baseTest rawA Data.t0) 10 20480 check0_20 check0_21) (checkPow_join (baseTest rawA Data.t0) 10 22528 check0_22 check0_23))) (checkPow_join (baseTest rawA Data.t0) 12 24576 (checkPow_join (baseTest rawA Data.t0) 11 24576 (checkPow_join (baseTest rawA Data.t0) 10 24576 check0_24 check0_25) (checkPow_join (baseTest rawA Data.t0) 10 26624 check0_26 check0_27)) (checkPow_join (baseTest rawA Data.t0) 11 28672 (checkPow_join (baseTest rawA Data.t0) 10 28672 check0_28 check0_29) (checkPow_join (baseTest rawA Data.t0) 10 30720 check0_30 check0_31)))))

theorem support0 : Supports p0 Data.t0 :=
  base_support p0 rawA Data.t0 (fun _ => rfl) (checked _ checked0)

private theorem check1_0 : checkPow (baseTest rawB Data.t1) 0 10 = true := by
  decide +kernel

private theorem check1_1 : checkPow (baseTest rawB Data.t1) 1024 10 = true := by
  decide +kernel

private theorem check1_2 : checkPow (baseTest rawB Data.t1) 2048 10 = true := by
  decide +kernel

private theorem check1_3 : checkPow (baseTest rawB Data.t1) 3072 10 = true := by
  decide +kernel

private theorem check1_4 : checkPow (baseTest rawB Data.t1) 4096 10 = true := by
  decide +kernel

private theorem check1_5 : checkPow (baseTest rawB Data.t1) 5120 10 = true := by
  decide +kernel

private theorem check1_6 : checkPow (baseTest rawB Data.t1) 6144 10 = true := by
  decide +kernel

private theorem check1_7 : checkPow (baseTest rawB Data.t1) 7168 10 = true := by
  decide +kernel

private theorem check1_8 : checkPow (baseTest rawB Data.t1) 8192 10 = true := by
  decide +kernel

private theorem check1_9 : checkPow (baseTest rawB Data.t1) 9216 10 = true := by
  decide +kernel

private theorem check1_10 : checkPow (baseTest rawB Data.t1) 10240 10 = true := by
  decide +kernel

private theorem check1_11 : checkPow (baseTest rawB Data.t1) 11264 10 = true := by
  decide +kernel

private theorem check1_12 : checkPow (baseTest rawB Data.t1) 12288 10 = true := by
  decide +kernel

private theorem check1_13 : checkPow (baseTest rawB Data.t1) 13312 10 = true := by
  decide +kernel

private theorem check1_14 : checkPow (baseTest rawB Data.t1) 14336 10 = true := by
  decide +kernel

private theorem check1_15 : checkPow (baseTest rawB Data.t1) 15360 10 = true := by
  decide +kernel

private theorem check1_16 : checkPow (baseTest rawB Data.t1) 16384 10 = true := by
  decide +kernel

private theorem check1_17 : checkPow (baseTest rawB Data.t1) 17408 10 = true := by
  decide +kernel

private theorem check1_18 : checkPow (baseTest rawB Data.t1) 18432 10 = true := by
  decide +kernel

private theorem check1_19 : checkPow (baseTest rawB Data.t1) 19456 10 = true := by
  decide +kernel

private theorem check1_20 : checkPow (baseTest rawB Data.t1) 20480 10 = true := by
  decide +kernel

private theorem check1_21 : checkPow (baseTest rawB Data.t1) 21504 10 = true := by
  decide +kernel

private theorem check1_22 : checkPow (baseTest rawB Data.t1) 22528 10 = true := by
  decide +kernel

private theorem check1_23 : checkPow (baseTest rawB Data.t1) 23552 10 = true := by
  decide +kernel

private theorem check1_24 : checkPow (baseTest rawB Data.t1) 24576 10 = true := by
  decide +kernel

private theorem check1_25 : checkPow (baseTest rawB Data.t1) 25600 10 = true := by
  decide +kernel

private theorem check1_26 : checkPow (baseTest rawB Data.t1) 26624 10 = true := by
  decide +kernel

private theorem check1_27 : checkPow (baseTest rawB Data.t1) 27648 10 = true := by
  decide +kernel

private theorem check1_28 : checkPow (baseTest rawB Data.t1) 28672 10 = true := by
  decide +kernel

private theorem check1_29 : checkPow (baseTest rawB Data.t1) 29696 10 = true := by
  decide +kernel

private theorem check1_30 : checkPow (baseTest rawB Data.t1) 30720 10 = true := by
  decide +kernel

private theorem check1_31 : checkPow (baseTest rawB Data.t1) 31744 10 = true := by
  decide +kernel

private theorem checked1 : checkPow (baseTest rawB Data.t1) 0 15 = true :=
  (checkPow_join (baseTest rawB Data.t1) 14 0 (checkPow_join (baseTest rawB Data.t1) 13 0 (checkPow_join (baseTest rawB Data.t1) 12 0 (checkPow_join (baseTest rawB Data.t1) 11 0 (checkPow_join (baseTest rawB Data.t1) 10 0 check1_0 check1_1) (checkPow_join (baseTest rawB Data.t1) 10 2048 check1_2 check1_3)) (checkPow_join (baseTest rawB Data.t1) 11 4096 (checkPow_join (baseTest rawB Data.t1) 10 4096 check1_4 check1_5) (checkPow_join (baseTest rawB Data.t1) 10 6144 check1_6 check1_7))) (checkPow_join (baseTest rawB Data.t1) 12 8192 (checkPow_join (baseTest rawB Data.t1) 11 8192 (checkPow_join (baseTest rawB Data.t1) 10 8192 check1_8 check1_9) (checkPow_join (baseTest rawB Data.t1) 10 10240 check1_10 check1_11)) (checkPow_join (baseTest rawB Data.t1) 11 12288 (checkPow_join (baseTest rawB Data.t1) 10 12288 check1_12 check1_13) (checkPow_join (baseTest rawB Data.t1) 10 14336 check1_14 check1_15)))) (checkPow_join (baseTest rawB Data.t1) 13 16384 (checkPow_join (baseTest rawB Data.t1) 12 16384 (checkPow_join (baseTest rawB Data.t1) 11 16384 (checkPow_join (baseTest rawB Data.t1) 10 16384 check1_16 check1_17) (checkPow_join (baseTest rawB Data.t1) 10 18432 check1_18 check1_19)) (checkPow_join (baseTest rawB Data.t1) 11 20480 (checkPow_join (baseTest rawB Data.t1) 10 20480 check1_20 check1_21) (checkPow_join (baseTest rawB Data.t1) 10 22528 check1_22 check1_23))) (checkPow_join (baseTest rawB Data.t1) 12 24576 (checkPow_join (baseTest rawB Data.t1) 11 24576 (checkPow_join (baseTest rawB Data.t1) 10 24576 check1_24 check1_25) (checkPow_join (baseTest rawB Data.t1) 10 26624 check1_26 check1_27)) (checkPow_join (baseTest rawB Data.t1) 11 28672 (checkPow_join (baseTest rawB Data.t1) 10 28672 check1_28 check1_29) (checkPow_join (baseTest rawB Data.t1) 10 30720 check1_30 check1_31)))))

theorem support1 : Supports p1 Data.t1 :=
  base_support p1 rawB Data.t1 (fun _ => rfl) (checked _ checked1)

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.OrbitActions
