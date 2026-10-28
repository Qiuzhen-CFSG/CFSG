module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.OrbitActions.ChecksBase
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.OrbitActions.DataShort

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

-- Synchronous leaves release each kernel-reduction cache before the next block.
set_option Elab.async false

private theorem check2_0 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 0 10 = true := by
  decide +kernel

private theorem check2_1 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 1024 10 = true := by
  decide +kernel

private theorem check2_2 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 2048 10 = true := by
  decide +kernel

private theorem check2_3 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 3072 10 = true := by
  decide +kernel

private theorem check2_4 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 4096 10 = true := by
  decide +kernel

private theorem check2_5 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 5120 10 = true := by
  decide +kernel

private theorem check2_6 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 6144 10 = true := by
  decide +kernel

private theorem check2_7 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 7168 10 = true := by
  decide +kernel

private theorem check2_8 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 8192 10 = true := by
  decide +kernel

private theorem check2_9 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 9216 10 = true := by
  decide +kernel

private theorem check2_10 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 10240 10 = true := by
  decide +kernel

private theorem check2_11 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 11264 10 = true := by
  decide +kernel

private theorem check2_12 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 12288 10 = true := by
  decide +kernel

private theorem check2_13 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 13312 10 = true := by
  decide +kernel

private theorem check2_14 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 14336 10 = true := by
  decide +kernel

private theorem check2_15 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 15360 10 = true := by
  decide +kernel

private theorem check2_16 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 16384 10 = true := by
  decide +kernel

private theorem check2_17 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 17408 10 = true := by
  decide +kernel

private theorem check2_18 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 18432 10 = true := by
  decide +kernel

private theorem check2_19 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 19456 10 = true := by
  decide +kernel

private theorem check2_20 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 20480 10 = true := by
  decide +kernel

private theorem check2_21 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 21504 10 = true := by
  decide +kernel

private theorem check2_22 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 22528 10 = true := by
  decide +kernel

private theorem check2_23 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 23552 10 = true := by
  decide +kernel

private theorem check2_24 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 24576 10 = true := by
  decide +kernel

private theorem check2_25 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 25600 10 = true := by
  decide +kernel

private theorem check2_26 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 26624 10 = true := by
  decide +kernel

private theorem check2_27 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 27648 10 = true := by
  decide +kernel

private theorem check2_28 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 28672 10 = true := by
  decide +kernel

private theorem check2_29 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 29696 10 = true := by
  decide +kernel

private theorem check2_30 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 30720 10 = true := by
  decide +kernel

private theorem check2_31 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 31744 10 = true := by
  decide +kernel

private theorem checked2 : checkPow (mulTest Data.t2 Data.t1 Data.t0) 0 15 = true :=
  (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 14 0 (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 13 0 (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 12 0 (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 11 0 (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 0 check2_0 check2_1) (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 2048 check2_2 check2_3)) (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 11 4096 (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 4096 check2_4 check2_5) (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 6144 check2_6 check2_7))) (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 12 8192 (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 11 8192 (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 8192 check2_8 check2_9) (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 10240 check2_10 check2_11)) (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 11 12288 (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 12288 check2_12 check2_13) (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 14336 check2_14 check2_15)))) (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 13 16384 (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 12 16384 (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 11 16384 (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 16384 check2_16 check2_17) (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 18432 check2_18 check2_19)) (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 11 20480 (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 20480 check2_20 check2_21) (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 22528 check2_22 check2_23))) (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 12 24576 (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 11 24576 (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 24576 check2_24 check2_25) (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 26624 check2_26 check2_27)) (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 11 28672 (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 28672 check2_28 check2_29) (checkPow_join (mulTest Data.t2 Data.t1 Data.t0) 10 30720 check2_30 check2_31)))))

theorem support2 : Supports p2 Data.t2 :=
  mul_support p1 p0 Data.t2 Data.t1 Data.t0
    support1 support0 (checked _ checked2)

private theorem check3_0 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 0 10 = true := by
  decide +kernel

private theorem check3_1 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 1024 10 = true := by
  decide +kernel

private theorem check3_2 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 2048 10 = true := by
  decide +kernel

private theorem check3_3 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 3072 10 = true := by
  decide +kernel

private theorem check3_4 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 4096 10 = true := by
  decide +kernel

private theorem check3_5 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 5120 10 = true := by
  decide +kernel

private theorem check3_6 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 6144 10 = true := by
  decide +kernel

private theorem check3_7 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 7168 10 = true := by
  decide +kernel

private theorem check3_8 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 8192 10 = true := by
  decide +kernel

private theorem check3_9 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 9216 10 = true := by
  decide +kernel

private theorem check3_10 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 10240 10 = true := by
  decide +kernel

private theorem check3_11 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 11264 10 = true := by
  decide +kernel

private theorem check3_12 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 12288 10 = true := by
  decide +kernel

private theorem check3_13 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 13312 10 = true := by
  decide +kernel

private theorem check3_14 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 14336 10 = true := by
  decide +kernel

private theorem check3_15 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 15360 10 = true := by
  decide +kernel

private theorem check3_16 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 16384 10 = true := by
  decide +kernel

private theorem check3_17 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 17408 10 = true := by
  decide +kernel

private theorem check3_18 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 18432 10 = true := by
  decide +kernel

private theorem check3_19 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 19456 10 = true := by
  decide +kernel

private theorem check3_20 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 20480 10 = true := by
  decide +kernel

private theorem check3_21 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 21504 10 = true := by
  decide +kernel

private theorem check3_22 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 22528 10 = true := by
  decide +kernel

private theorem check3_23 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 23552 10 = true := by
  decide +kernel

private theorem check3_24 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 24576 10 = true := by
  decide +kernel

private theorem check3_25 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 25600 10 = true := by
  decide +kernel

private theorem check3_26 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 26624 10 = true := by
  decide +kernel

private theorem check3_27 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 27648 10 = true := by
  decide +kernel

private theorem check3_28 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 28672 10 = true := by
  decide +kernel

private theorem check3_29 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 29696 10 = true := by
  decide +kernel

private theorem check3_30 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 30720 10 = true := by
  decide +kernel

private theorem check3_31 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 31744 10 = true := by
  decide +kernel

private theorem checked3 : checkPow (mulTest Data.t3 Data.t2 Data.t2) 0 15 = true :=
  (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 14 0 (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 13 0 (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 12 0 (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 11 0 (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 0 check3_0 check3_1) (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 2048 check3_2 check3_3)) (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 11 4096 (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 4096 check3_4 check3_5) (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 6144 check3_6 check3_7))) (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 12 8192 (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 11 8192 (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 8192 check3_8 check3_9) (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 10240 check3_10 check3_11)) (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 11 12288 (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 12288 check3_12 check3_13) (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 14336 check3_14 check3_15)))) (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 13 16384 (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 12 16384 (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 11 16384 (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 16384 check3_16 check3_17) (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 18432 check3_18 check3_19)) (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 11 20480 (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 20480 check3_20 check3_21) (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 22528 check3_22 check3_23))) (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 12 24576 (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 11 24576 (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 24576 check3_24 check3_25) (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 26624 check3_26 check3_27)) (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 11 28672 (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 28672 check3_28 check3_29) (checkPow_join (mulTest Data.t3 Data.t2 Data.t2) 10 30720 check3_30 check3_31)))))

theorem support3 : Supports p3 Data.t3 :=
  mul_support p2 p2 Data.t3 Data.t2 Data.t2
    support2 support2 (checked _ checked3)

private theorem check4_0 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 0 10 = true := by
  decide +kernel

private theorem check4_1 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 1024 10 = true := by
  decide +kernel

private theorem check4_2 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 2048 10 = true := by
  decide +kernel

private theorem check4_3 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 3072 10 = true := by
  decide +kernel

private theorem check4_4 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 4096 10 = true := by
  decide +kernel

private theorem check4_5 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 5120 10 = true := by
  decide +kernel

private theorem check4_6 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 6144 10 = true := by
  decide +kernel

private theorem check4_7 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 7168 10 = true := by
  decide +kernel

private theorem check4_8 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 8192 10 = true := by
  decide +kernel

private theorem check4_9 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 9216 10 = true := by
  decide +kernel

private theorem check4_10 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 10240 10 = true := by
  decide +kernel

private theorem check4_11 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 11264 10 = true := by
  decide +kernel

private theorem check4_12 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 12288 10 = true := by
  decide +kernel

private theorem check4_13 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 13312 10 = true := by
  decide +kernel

private theorem check4_14 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 14336 10 = true := by
  decide +kernel

private theorem check4_15 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 15360 10 = true := by
  decide +kernel

private theorem check4_16 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 16384 10 = true := by
  decide +kernel

private theorem check4_17 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 17408 10 = true := by
  decide +kernel

private theorem check4_18 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 18432 10 = true := by
  decide +kernel

private theorem check4_19 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 19456 10 = true := by
  decide +kernel

private theorem check4_20 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 20480 10 = true := by
  decide +kernel

private theorem check4_21 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 21504 10 = true := by
  decide +kernel

private theorem check4_22 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 22528 10 = true := by
  decide +kernel

private theorem check4_23 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 23552 10 = true := by
  decide +kernel

private theorem check4_24 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 24576 10 = true := by
  decide +kernel

private theorem check4_25 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 25600 10 = true := by
  decide +kernel

private theorem check4_26 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 26624 10 = true := by
  decide +kernel

private theorem check4_27 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 27648 10 = true := by
  decide +kernel

private theorem check4_28 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 28672 10 = true := by
  decide +kernel

private theorem check4_29 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 29696 10 = true := by
  decide +kernel

private theorem check4_30 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 30720 10 = true := by
  decide +kernel

private theorem check4_31 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 31744 10 = true := by
  decide +kernel

private theorem checked4 : checkPow (mulTest Data.t4 Data.t1 Data.t2) 0 15 = true :=
  (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 14 0 (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 13 0 (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 12 0 (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 11 0 (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 0 check4_0 check4_1) (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 2048 check4_2 check4_3)) (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 11 4096 (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 4096 check4_4 check4_5) (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 6144 check4_6 check4_7))) (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 12 8192 (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 11 8192 (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 8192 check4_8 check4_9) (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 10240 check4_10 check4_11)) (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 11 12288 (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 12288 check4_12 check4_13) (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 14336 check4_14 check4_15)))) (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 13 16384 (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 12 16384 (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 11 16384 (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 16384 check4_16 check4_17) (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 18432 check4_18 check4_19)) (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 11 20480 (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 20480 check4_20 check4_21) (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 22528 check4_22 check4_23))) (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 12 24576 (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 11 24576 (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 24576 check4_24 check4_25) (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 26624 check4_26 check4_27)) (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 11 28672 (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 28672 check4_28 check4_29) (checkPow_join (mulTest Data.t4 Data.t1 Data.t2) 10 30720 check4_30 check4_31)))))

theorem support4 : Supports p4 Data.t4 :=
  mul_support p1 p2 Data.t4 Data.t1 Data.t2
    support1 support2 (checked _ checked4)

private theorem check5_0 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 0 10 = true := by
  decide +kernel

private theorem check5_1 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 1024 10 = true := by
  decide +kernel

private theorem check5_2 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 2048 10 = true := by
  decide +kernel

private theorem check5_3 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 3072 10 = true := by
  decide +kernel

private theorem check5_4 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 4096 10 = true := by
  decide +kernel

private theorem check5_5 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 5120 10 = true := by
  decide +kernel

private theorem check5_6 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 6144 10 = true := by
  decide +kernel

private theorem check5_7 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 7168 10 = true := by
  decide +kernel

private theorem check5_8 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 8192 10 = true := by
  decide +kernel

private theorem check5_9 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 9216 10 = true := by
  decide +kernel

private theorem check5_10 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 10240 10 = true := by
  decide +kernel

private theorem check5_11 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 11264 10 = true := by
  decide +kernel

private theorem check5_12 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 12288 10 = true := by
  decide +kernel

private theorem check5_13 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 13312 10 = true := by
  decide +kernel

private theorem check5_14 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 14336 10 = true := by
  decide +kernel

private theorem check5_15 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 15360 10 = true := by
  decide +kernel

private theorem check5_16 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 16384 10 = true := by
  decide +kernel

private theorem check5_17 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 17408 10 = true := by
  decide +kernel

private theorem check5_18 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 18432 10 = true := by
  decide +kernel

private theorem check5_19 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 19456 10 = true := by
  decide +kernel

private theorem check5_20 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 20480 10 = true := by
  decide +kernel

private theorem check5_21 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 21504 10 = true := by
  decide +kernel

private theorem check5_22 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 22528 10 = true := by
  decide +kernel

private theorem check5_23 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 23552 10 = true := by
  decide +kernel

private theorem check5_24 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 24576 10 = true := by
  decide +kernel

private theorem check5_25 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 25600 10 = true := by
  decide +kernel

private theorem check5_26 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 26624 10 = true := by
  decide +kernel

private theorem check5_27 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 27648 10 = true := by
  decide +kernel

private theorem check5_28 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 28672 10 = true := by
  decide +kernel

private theorem check5_29 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 29696 10 = true := by
  decide +kernel

private theorem check5_30 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 30720 10 = true := by
  decide +kernel

private theorem check5_31 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 31744 10 = true := by
  decide +kernel

private theorem checked5 : checkPow (mulTest Data.t5 Data.t1 Data.t3) 0 15 = true :=
  (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 14 0 (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 13 0 (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 12 0 (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 11 0 (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 0 check5_0 check5_1) (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 2048 check5_2 check5_3)) (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 11 4096 (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 4096 check5_4 check5_5) (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 6144 check5_6 check5_7))) (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 12 8192 (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 11 8192 (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 8192 check5_8 check5_9) (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 10240 check5_10 check5_11)) (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 11 12288 (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 12288 check5_12 check5_13) (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 14336 check5_14 check5_15)))) (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 13 16384 (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 12 16384 (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 11 16384 (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 16384 check5_16 check5_17) (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 18432 check5_18 check5_19)) (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 11 20480 (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 20480 check5_20 check5_21) (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 22528 check5_22 check5_23))) (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 12 24576 (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 11 24576 (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 24576 check5_24 check5_25) (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 26624 check5_26 check5_27)) (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 11 28672 (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 28672 check5_28 check5_29) (checkPow_join (mulTest Data.t5 Data.t1 Data.t3) 10 30720 check5_30 check5_31)))))

theorem support5 : Supports p5 Data.t5 :=
  mul_support p1 p3 Data.t5 Data.t1 Data.t3
    support1 support3 (checked _ checked5)

private theorem check6_0 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 0 10 = true := by
  decide +kernel

private theorem check6_1 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 1024 10 = true := by
  decide +kernel

private theorem check6_2 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 2048 10 = true := by
  decide +kernel

private theorem check6_3 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 3072 10 = true := by
  decide +kernel

private theorem check6_4 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 4096 10 = true := by
  decide +kernel

private theorem check6_5 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 5120 10 = true := by
  decide +kernel

private theorem check6_6 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 6144 10 = true := by
  decide +kernel

private theorem check6_7 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 7168 10 = true := by
  decide +kernel

private theorem check6_8 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 8192 10 = true := by
  decide +kernel

private theorem check6_9 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 9216 10 = true := by
  decide +kernel

private theorem check6_10 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 10240 10 = true := by
  decide +kernel

private theorem check6_11 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 11264 10 = true := by
  decide +kernel

private theorem check6_12 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 12288 10 = true := by
  decide +kernel

private theorem check6_13 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 13312 10 = true := by
  decide +kernel

private theorem check6_14 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 14336 10 = true := by
  decide +kernel

private theorem check6_15 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 15360 10 = true := by
  decide +kernel

private theorem check6_16 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 16384 10 = true := by
  decide +kernel

private theorem check6_17 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 17408 10 = true := by
  decide +kernel

private theorem check6_18 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 18432 10 = true := by
  decide +kernel

private theorem check6_19 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 19456 10 = true := by
  decide +kernel

private theorem check6_20 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 20480 10 = true := by
  decide +kernel

private theorem check6_21 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 21504 10 = true := by
  decide +kernel

private theorem check6_22 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 22528 10 = true := by
  decide +kernel

private theorem check6_23 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 23552 10 = true := by
  decide +kernel

private theorem check6_24 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 24576 10 = true := by
  decide +kernel

private theorem check6_25 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 25600 10 = true := by
  decide +kernel

private theorem check6_26 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 26624 10 = true := by
  decide +kernel

private theorem check6_27 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 27648 10 = true := by
  decide +kernel

private theorem check6_28 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 28672 10 = true := by
  decide +kernel

private theorem check6_29 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 29696 10 = true := by
  decide +kernel

private theorem check6_30 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 30720 10 = true := by
  decide +kernel

private theorem check6_31 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 31744 10 = true := by
  decide +kernel

private theorem checked6 : checkPow (mulTest Data.t6 Data.t4 Data.t5) 0 15 = true :=
  (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 14 0 (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 13 0 (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 12 0 (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 11 0 (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 0 check6_0 check6_1) (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 2048 check6_2 check6_3)) (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 11 4096 (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 4096 check6_4 check6_5) (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 6144 check6_6 check6_7))) (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 12 8192 (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 11 8192 (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 8192 check6_8 check6_9) (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 10240 check6_10 check6_11)) (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 11 12288 (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 12288 check6_12 check6_13) (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 14336 check6_14 check6_15)))) (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 13 16384 (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 12 16384 (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 11 16384 (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 16384 check6_16 check6_17) (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 18432 check6_18 check6_19)) (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 11 20480 (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 20480 check6_20 check6_21) (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 22528 check6_22 check6_23))) (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 12 24576 (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 11 24576 (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 24576 check6_24 check6_25) (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 26624 check6_26 check6_27)) (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 11 28672 (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 28672 check6_28 check6_29) (checkPow_join (mulTest Data.t6 Data.t4 Data.t5) 10 30720 check6_30 check6_31)))))

theorem support6 : Supports p6 Data.t6 :=
  mul_support p4 p5 Data.t6 Data.t4 Data.t5
    support4 support5 (checked _ checked6)

private theorem check7_0 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 0 10 = true := by
  decide +kernel

private theorem check7_1 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 1024 10 = true := by
  decide +kernel

private theorem check7_2 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 2048 10 = true := by
  decide +kernel

private theorem check7_3 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 3072 10 = true := by
  decide +kernel

private theorem check7_4 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 4096 10 = true := by
  decide +kernel

private theorem check7_5 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 5120 10 = true := by
  decide +kernel

private theorem check7_6 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 6144 10 = true := by
  decide +kernel

private theorem check7_7 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 7168 10 = true := by
  decide +kernel

private theorem check7_8 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 8192 10 = true := by
  decide +kernel

private theorem check7_9 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 9216 10 = true := by
  decide +kernel

private theorem check7_10 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 10240 10 = true := by
  decide +kernel

private theorem check7_11 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 11264 10 = true := by
  decide +kernel

private theorem check7_12 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 12288 10 = true := by
  decide +kernel

private theorem check7_13 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 13312 10 = true := by
  decide +kernel

private theorem check7_14 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 14336 10 = true := by
  decide +kernel

private theorem check7_15 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 15360 10 = true := by
  decide +kernel

private theorem check7_16 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 16384 10 = true := by
  decide +kernel

private theorem check7_17 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 17408 10 = true := by
  decide +kernel

private theorem check7_18 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 18432 10 = true := by
  decide +kernel

private theorem check7_19 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 19456 10 = true := by
  decide +kernel

private theorem check7_20 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 20480 10 = true := by
  decide +kernel

private theorem check7_21 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 21504 10 = true := by
  decide +kernel

private theorem check7_22 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 22528 10 = true := by
  decide +kernel

private theorem check7_23 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 23552 10 = true := by
  decide +kernel

private theorem check7_24 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 24576 10 = true := by
  decide +kernel

private theorem check7_25 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 25600 10 = true := by
  decide +kernel

private theorem check7_26 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 26624 10 = true := by
  decide +kernel

private theorem check7_27 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 27648 10 = true := by
  decide +kernel

private theorem check7_28 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 28672 10 = true := by
  decide +kernel

private theorem check7_29 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 29696 10 = true := by
  decide +kernel

private theorem check7_30 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 30720 10 = true := by
  decide +kernel

private theorem check7_31 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 31744 10 = true := by
  decide +kernel

private theorem checked7 : checkPow (mulTest Data.t7 Data.t6 Data.t3) 0 15 = true :=
  (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 14 0 (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 13 0 (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 12 0 (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 11 0 (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 0 check7_0 check7_1) (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 2048 check7_2 check7_3)) (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 11 4096 (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 4096 check7_4 check7_5) (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 6144 check7_6 check7_7))) (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 12 8192 (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 11 8192 (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 8192 check7_8 check7_9) (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 10240 check7_10 check7_11)) (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 11 12288 (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 12288 check7_12 check7_13) (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 14336 check7_14 check7_15)))) (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 13 16384 (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 12 16384 (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 11 16384 (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 16384 check7_16 check7_17) (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 18432 check7_18 check7_19)) (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 11 20480 (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 20480 check7_20 check7_21) (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 22528 check7_22 check7_23))) (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 12 24576 (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 11 24576 (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 24576 check7_24 check7_25) (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 26624 check7_26 check7_27)) (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 11 28672 (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 28672 check7_28 check7_29) (checkPow_join (mulTest Data.t7 Data.t6 Data.t3) 10 30720 check7_30 check7_31)))))

theorem support7 : Supports p7 Data.t7 :=
  mul_support p6 p3 Data.t7 Data.t6 Data.t3
    support6 support3 (checked _ checked7)

private theorem check8_0 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 0 10 = true := by
  decide +kernel

private theorem check8_1 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 1024 10 = true := by
  decide +kernel

private theorem check8_2 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 2048 10 = true := by
  decide +kernel

private theorem check8_3 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 3072 10 = true := by
  decide +kernel

private theorem check8_4 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 4096 10 = true := by
  decide +kernel

private theorem check8_5 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 5120 10 = true := by
  decide +kernel

private theorem check8_6 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 6144 10 = true := by
  decide +kernel

private theorem check8_7 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 7168 10 = true := by
  decide +kernel

private theorem check8_8 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 8192 10 = true := by
  decide +kernel

private theorem check8_9 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 9216 10 = true := by
  decide +kernel

private theorem check8_10 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 10240 10 = true := by
  decide +kernel

private theorem check8_11 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 11264 10 = true := by
  decide +kernel

private theorem check8_12 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 12288 10 = true := by
  decide +kernel

private theorem check8_13 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 13312 10 = true := by
  decide +kernel

private theorem check8_14 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 14336 10 = true := by
  decide +kernel

private theorem check8_15 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 15360 10 = true := by
  decide +kernel

private theorem check8_16 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 16384 10 = true := by
  decide +kernel

private theorem check8_17 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 17408 10 = true := by
  decide +kernel

private theorem check8_18 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 18432 10 = true := by
  decide +kernel

private theorem check8_19 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 19456 10 = true := by
  decide +kernel

private theorem check8_20 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 20480 10 = true := by
  decide +kernel

private theorem check8_21 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 21504 10 = true := by
  decide +kernel

private theorem check8_22 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 22528 10 = true := by
  decide +kernel

private theorem check8_23 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 23552 10 = true := by
  decide +kernel

private theorem check8_24 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 24576 10 = true := by
  decide +kernel

private theorem check8_25 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 25600 10 = true := by
  decide +kernel

private theorem check8_26 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 26624 10 = true := by
  decide +kernel

private theorem check8_27 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 27648 10 = true := by
  decide +kernel

private theorem check8_28 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 28672 10 = true := by
  decide +kernel

private theorem check8_29 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 29696 10 = true := by
  decide +kernel

private theorem check8_30 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 30720 10 = true := by
  decide +kernel

private theorem check8_31 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 31744 10 = true := by
  decide +kernel

private theorem checked8 : checkPow (mulTest Data.t8 Data.t4 Data.t7) 0 15 = true :=
  (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 14 0 (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 13 0 (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 12 0 (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 11 0 (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 0 check8_0 check8_1) (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 2048 check8_2 check8_3)) (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 11 4096 (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 4096 check8_4 check8_5) (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 6144 check8_6 check8_7))) (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 12 8192 (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 11 8192 (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 8192 check8_8 check8_9) (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 10240 check8_10 check8_11)) (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 11 12288 (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 12288 check8_12 check8_13) (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 14336 check8_14 check8_15)))) (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 13 16384 (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 12 16384 (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 11 16384 (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 16384 check8_16 check8_17) (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 18432 check8_18 check8_19)) (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 11 20480 (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 20480 check8_20 check8_21) (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 22528 check8_22 check8_23))) (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 12 24576 (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 11 24576 (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 24576 check8_24 check8_25) (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 26624 check8_26 check8_27)) (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 11 28672 (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 28672 check8_28 check8_29) (checkPow_join (mulTest Data.t8 Data.t4 Data.t7) 10 30720 check8_30 check8_31)))))

theorem support8 : Supports p8 Data.t8 :=
  mul_support p4 p7 Data.t8 Data.t4 Data.t7
    support4 support7 (checked _ checked8)

private theorem check9_0 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 0 10 = true := by
  decide +kernel

private theorem check9_1 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 1024 10 = true := by
  decide +kernel

private theorem check9_2 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 2048 10 = true := by
  decide +kernel

private theorem check9_3 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 3072 10 = true := by
  decide +kernel

private theorem check9_4 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 4096 10 = true := by
  decide +kernel

private theorem check9_5 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 5120 10 = true := by
  decide +kernel

private theorem check9_6 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 6144 10 = true := by
  decide +kernel

private theorem check9_7 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 7168 10 = true := by
  decide +kernel

private theorem check9_8 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 8192 10 = true := by
  decide +kernel

private theorem check9_9 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 9216 10 = true := by
  decide +kernel

private theorem check9_10 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 10240 10 = true := by
  decide +kernel

private theorem check9_11 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 11264 10 = true := by
  decide +kernel

private theorem check9_12 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 12288 10 = true := by
  decide +kernel

private theorem check9_13 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 13312 10 = true := by
  decide +kernel

private theorem check9_14 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 14336 10 = true := by
  decide +kernel

private theorem check9_15 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 15360 10 = true := by
  decide +kernel

private theorem check9_16 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 16384 10 = true := by
  decide +kernel

private theorem check9_17 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 17408 10 = true := by
  decide +kernel

private theorem check9_18 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 18432 10 = true := by
  decide +kernel

private theorem check9_19 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 19456 10 = true := by
  decide +kernel

private theorem check9_20 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 20480 10 = true := by
  decide +kernel

private theorem check9_21 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 21504 10 = true := by
  decide +kernel

private theorem check9_22 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 22528 10 = true := by
  decide +kernel

private theorem check9_23 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 23552 10 = true := by
  decide +kernel

private theorem check9_24 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 24576 10 = true := by
  decide +kernel

private theorem check9_25 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 25600 10 = true := by
  decide +kernel

private theorem check9_26 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 26624 10 = true := by
  decide +kernel

private theorem check9_27 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 27648 10 = true := by
  decide +kernel

private theorem check9_28 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 28672 10 = true := by
  decide +kernel

private theorem check9_29 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 29696 10 = true := by
  decide +kernel

private theorem check9_30 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 30720 10 = true := by
  decide +kernel

private theorem check9_31 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 31744 10 = true := by
  decide +kernel

private theorem checked9 : checkPow (mulTest Data.t9 Data.t3 Data.t3) 0 15 = true :=
  (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 14 0 (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 13 0 (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 12 0 (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 11 0 (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 0 check9_0 check9_1) (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 2048 check9_2 check9_3)) (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 11 4096 (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 4096 check9_4 check9_5) (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 6144 check9_6 check9_7))) (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 12 8192 (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 11 8192 (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 8192 check9_8 check9_9) (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 10240 check9_10 check9_11)) (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 11 12288 (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 12288 check9_12 check9_13) (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 14336 check9_14 check9_15)))) (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 13 16384 (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 12 16384 (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 11 16384 (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 16384 check9_16 check9_17) (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 18432 check9_18 check9_19)) (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 11 20480 (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 20480 check9_20 check9_21) (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 22528 check9_22 check9_23))) (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 12 24576 (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 11 24576 (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 24576 check9_24 check9_25) (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 26624 check9_26 check9_27)) (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 11 28672 (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 28672 check9_28 check9_29) (checkPow_join (mulTest Data.t9 Data.t3 Data.t3) 10 30720 check9_30 check9_31)))))

theorem support9 : Supports p9 Data.t9 :=
  mul_support p3 p3 Data.t9 Data.t3 Data.t3
    support3 support3 (checked _ checked9)

private theorem check10_0 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 0 10 = true := by
  decide +kernel

private theorem check10_1 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 1024 10 = true := by
  decide +kernel

private theorem check10_2 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 2048 10 = true := by
  decide +kernel

private theorem check10_3 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 3072 10 = true := by
  decide +kernel

private theorem check10_4 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 4096 10 = true := by
  decide +kernel

private theorem check10_5 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 5120 10 = true := by
  decide +kernel

private theorem check10_6 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 6144 10 = true := by
  decide +kernel

private theorem check10_7 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 7168 10 = true := by
  decide +kernel

private theorem check10_8 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 8192 10 = true := by
  decide +kernel

private theorem check10_9 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 9216 10 = true := by
  decide +kernel

private theorem check10_10 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 10240 10 = true := by
  decide +kernel

private theorem check10_11 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 11264 10 = true := by
  decide +kernel

private theorem check10_12 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 12288 10 = true := by
  decide +kernel

private theorem check10_13 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 13312 10 = true := by
  decide +kernel

private theorem check10_14 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 14336 10 = true := by
  decide +kernel

private theorem check10_15 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 15360 10 = true := by
  decide +kernel

private theorem check10_16 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 16384 10 = true := by
  decide +kernel

private theorem check10_17 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 17408 10 = true := by
  decide +kernel

private theorem check10_18 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 18432 10 = true := by
  decide +kernel

private theorem check10_19 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 19456 10 = true := by
  decide +kernel

private theorem check10_20 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 20480 10 = true := by
  decide +kernel

private theorem check10_21 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 21504 10 = true := by
  decide +kernel

private theorem check10_22 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 22528 10 = true := by
  decide +kernel

private theorem check10_23 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 23552 10 = true := by
  decide +kernel

private theorem check10_24 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 24576 10 = true := by
  decide +kernel

private theorem check10_25 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 25600 10 = true := by
  decide +kernel

private theorem check10_26 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 26624 10 = true := by
  decide +kernel

private theorem check10_27 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 27648 10 = true := by
  decide +kernel

private theorem check10_28 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 28672 10 = true := by
  decide +kernel

private theorem check10_29 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 29696 10 = true := by
  decide +kernel

private theorem check10_30 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 30720 10 = true := by
  decide +kernel

private theorem check10_31 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 31744 10 = true := by
  decide +kernel

private theorem checked10 : checkPow (mulTest Data.t10 Data.t0 Data.t3) 0 15 = true :=
  (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 14 0 (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 13 0 (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 12 0 (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 11 0 (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 0 check10_0 check10_1) (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 2048 check10_2 check10_3)) (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 11 4096 (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 4096 check10_4 check10_5) (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 6144 check10_6 check10_7))) (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 12 8192 (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 11 8192 (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 8192 check10_8 check10_9) (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 10240 check10_10 check10_11)) (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 11 12288 (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 12288 check10_12 check10_13) (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 14336 check10_14 check10_15)))) (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 13 16384 (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 12 16384 (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 11 16384 (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 16384 check10_16 check10_17) (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 18432 check10_18 check10_19)) (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 11 20480 (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 20480 check10_20 check10_21) (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 22528 check10_22 check10_23))) (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 12 24576 (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 11 24576 (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 24576 check10_24 check10_25) (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 26624 check10_26 check10_27)) (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 11 28672 (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 28672 check10_28 check10_29) (checkPow_join (mulTest Data.t10 Data.t0 Data.t3) 10 30720 check10_30 check10_31)))))

theorem support10 : Supports p10 Data.t10 :=
  mul_support p0 p3 Data.t10 Data.t0 Data.t3
    support0 support3 (checked _ checked10)

private theorem check11_0 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 0 10 = true := by
  decide +kernel

private theorem check11_1 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 1024 10 = true := by
  decide +kernel

private theorem check11_2 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 2048 10 = true := by
  decide +kernel

private theorem check11_3 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 3072 10 = true := by
  decide +kernel

private theorem check11_4 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 4096 10 = true := by
  decide +kernel

private theorem check11_5 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 5120 10 = true := by
  decide +kernel

private theorem check11_6 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 6144 10 = true := by
  decide +kernel

private theorem check11_7 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 7168 10 = true := by
  decide +kernel

private theorem check11_8 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 8192 10 = true := by
  decide +kernel

private theorem check11_9 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 9216 10 = true := by
  decide +kernel

private theorem check11_10 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 10240 10 = true := by
  decide +kernel

private theorem check11_11 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 11264 10 = true := by
  decide +kernel

private theorem check11_12 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 12288 10 = true := by
  decide +kernel

private theorem check11_13 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 13312 10 = true := by
  decide +kernel

private theorem check11_14 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 14336 10 = true := by
  decide +kernel

private theorem check11_15 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 15360 10 = true := by
  decide +kernel

private theorem check11_16 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 16384 10 = true := by
  decide +kernel

private theorem check11_17 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 17408 10 = true := by
  decide +kernel

private theorem check11_18 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 18432 10 = true := by
  decide +kernel

private theorem check11_19 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 19456 10 = true := by
  decide +kernel

private theorem check11_20 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 20480 10 = true := by
  decide +kernel

private theorem check11_21 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 21504 10 = true := by
  decide +kernel

private theorem check11_22 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 22528 10 = true := by
  decide +kernel

private theorem check11_23 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 23552 10 = true := by
  decide +kernel

private theorem check11_24 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 24576 10 = true := by
  decide +kernel

private theorem check11_25 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 25600 10 = true := by
  decide +kernel

private theorem check11_26 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 26624 10 = true := by
  decide +kernel

private theorem check11_27 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 27648 10 = true := by
  decide +kernel

private theorem check11_28 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 28672 10 = true := by
  decide +kernel

private theorem check11_29 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 29696 10 = true := by
  decide +kernel

private theorem check11_30 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 30720 10 = true := by
  decide +kernel

private theorem check11_31 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 31744 10 = true := by
  decide +kernel

private theorem checked11 : checkPow (mulTest Data.t11 Data.t10 Data.t6) 0 15 = true :=
  (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 14 0 (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 13 0 (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 12 0 (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 11 0 (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 0 check11_0 check11_1) (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 2048 check11_2 check11_3)) (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 11 4096 (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 4096 check11_4 check11_5) (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 6144 check11_6 check11_7))) (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 12 8192 (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 11 8192 (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 8192 check11_8 check11_9) (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 10240 check11_10 check11_11)) (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 11 12288 (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 12288 check11_12 check11_13) (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 14336 check11_14 check11_15)))) (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 13 16384 (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 12 16384 (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 11 16384 (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 16384 check11_16 check11_17) (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 18432 check11_18 check11_19)) (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 11 20480 (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 20480 check11_20 check11_21) (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 22528 check11_22 check11_23))) (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 12 24576 (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 11 24576 (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 24576 check11_24 check11_25) (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 26624 check11_26 check11_27)) (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 11 28672 (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 28672 check11_28 check11_29) (checkPow_join (mulTest Data.t11 Data.t10 Data.t6) 10 30720 check11_30 check11_31)))))

theorem support11 : Supports p11 Data.t11 :=
  mul_support p10 p6 Data.t11 Data.t10 Data.t6
    support10 support6 (checked _ checked11)

private theorem check12_0 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 0 10 = true := by
  decide +kernel

private theorem check12_1 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 1024 10 = true := by
  decide +kernel

private theorem check12_2 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 2048 10 = true := by
  decide +kernel

private theorem check12_3 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 3072 10 = true := by
  decide +kernel

private theorem check12_4 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 4096 10 = true := by
  decide +kernel

private theorem check12_5 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 5120 10 = true := by
  decide +kernel

private theorem check12_6 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 6144 10 = true := by
  decide +kernel

private theorem check12_7 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 7168 10 = true := by
  decide +kernel

private theorem check12_8 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 8192 10 = true := by
  decide +kernel

private theorem check12_9 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 9216 10 = true := by
  decide +kernel

private theorem check12_10 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 10240 10 = true := by
  decide +kernel

private theorem check12_11 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 11264 10 = true := by
  decide +kernel

private theorem check12_12 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 12288 10 = true := by
  decide +kernel

private theorem check12_13 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 13312 10 = true := by
  decide +kernel

private theorem check12_14 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 14336 10 = true := by
  decide +kernel

private theorem check12_15 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 15360 10 = true := by
  decide +kernel

private theorem check12_16 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 16384 10 = true := by
  decide +kernel

private theorem check12_17 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 17408 10 = true := by
  decide +kernel

private theorem check12_18 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 18432 10 = true := by
  decide +kernel

private theorem check12_19 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 19456 10 = true := by
  decide +kernel

private theorem check12_20 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 20480 10 = true := by
  decide +kernel

private theorem check12_21 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 21504 10 = true := by
  decide +kernel

private theorem check12_22 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 22528 10 = true := by
  decide +kernel

private theorem check12_23 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 23552 10 = true := by
  decide +kernel

private theorem check12_24 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 24576 10 = true := by
  decide +kernel

private theorem check12_25 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 25600 10 = true := by
  decide +kernel

private theorem check12_26 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 26624 10 = true := by
  decide +kernel

private theorem check12_27 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 27648 10 = true := by
  decide +kernel

private theorem check12_28 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 28672 10 = true := by
  decide +kernel

private theorem check12_29 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 29696 10 = true := by
  decide +kernel

private theorem check12_30 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 30720 10 = true := by
  decide +kernel

private theorem check12_31 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 31744 10 = true := by
  decide +kernel

private theorem checked12 : checkPow (mulTest Data.t12 Data.t11 Data.t2) 0 15 = true :=
  (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 14 0 (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 13 0 (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 12 0 (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 11 0 (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 0 check12_0 check12_1) (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 2048 check12_2 check12_3)) (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 11 4096 (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 4096 check12_4 check12_5) (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 6144 check12_6 check12_7))) (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 12 8192 (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 11 8192 (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 8192 check12_8 check12_9) (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 10240 check12_10 check12_11)) (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 11 12288 (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 12288 check12_12 check12_13) (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 14336 check12_14 check12_15)))) (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 13 16384 (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 12 16384 (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 11 16384 (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 16384 check12_16 check12_17) (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 18432 check12_18 check12_19)) (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 11 20480 (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 20480 check12_20 check12_21) (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 22528 check12_22 check12_23))) (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 12 24576 (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 11 24576 (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 24576 check12_24 check12_25) (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 26624 check12_26 check12_27)) (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 11 28672 (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 28672 check12_28 check12_29) (checkPow_join (mulTest Data.t12 Data.t11 Data.t2) 10 30720 check12_30 check12_31)))))

theorem support12 : Supports p12 Data.t12 :=
  mul_support p11 p2 Data.t12 Data.t11 Data.t2
    support11 support2 (checked _ checked12)

private theorem check13_0 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 0 10 = true := by
  decide +kernel

private theorem check13_1 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 1024 10 = true := by
  decide +kernel

private theorem check13_2 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 2048 10 = true := by
  decide +kernel

private theorem check13_3 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 3072 10 = true := by
  decide +kernel

private theorem check13_4 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 4096 10 = true := by
  decide +kernel

private theorem check13_5 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 5120 10 = true := by
  decide +kernel

private theorem check13_6 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 6144 10 = true := by
  decide +kernel

private theorem check13_7 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 7168 10 = true := by
  decide +kernel

private theorem check13_8 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 8192 10 = true := by
  decide +kernel

private theorem check13_9 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 9216 10 = true := by
  decide +kernel

private theorem check13_10 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 10240 10 = true := by
  decide +kernel

private theorem check13_11 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 11264 10 = true := by
  decide +kernel

private theorem check13_12 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 12288 10 = true := by
  decide +kernel

private theorem check13_13 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 13312 10 = true := by
  decide +kernel

private theorem check13_14 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 14336 10 = true := by
  decide +kernel

private theorem check13_15 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 15360 10 = true := by
  decide +kernel

private theorem check13_16 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 16384 10 = true := by
  decide +kernel

private theorem check13_17 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 17408 10 = true := by
  decide +kernel

private theorem check13_18 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 18432 10 = true := by
  decide +kernel

private theorem check13_19 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 19456 10 = true := by
  decide +kernel

private theorem check13_20 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 20480 10 = true := by
  decide +kernel

private theorem check13_21 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 21504 10 = true := by
  decide +kernel

private theorem check13_22 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 22528 10 = true := by
  decide +kernel

private theorem check13_23 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 23552 10 = true := by
  decide +kernel

private theorem check13_24 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 24576 10 = true := by
  decide +kernel

private theorem check13_25 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 25600 10 = true := by
  decide +kernel

private theorem check13_26 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 26624 10 = true := by
  decide +kernel

private theorem check13_27 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 27648 10 = true := by
  decide +kernel

private theorem check13_28 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 28672 10 = true := by
  decide +kernel

private theorem check13_29 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 29696 10 = true := by
  decide +kernel

private theorem check13_30 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 30720 10 = true := by
  decide +kernel

private theorem check13_31 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 31744 10 = true := by
  decide +kernel

private theorem checked13 : checkPow (mulTest Data.t13 Data.t12 Data.t8) 0 15 = true :=
  (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 14 0 (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 13 0 (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 12 0 (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 11 0 (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 0 check13_0 check13_1) (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 2048 check13_2 check13_3)) (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 11 4096 (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 4096 check13_4 check13_5) (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 6144 check13_6 check13_7))) (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 12 8192 (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 11 8192 (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 8192 check13_8 check13_9) (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 10240 check13_10 check13_11)) (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 11 12288 (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 12288 check13_12 check13_13) (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 14336 check13_14 check13_15)))) (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 13 16384 (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 12 16384 (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 11 16384 (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 16384 check13_16 check13_17) (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 18432 check13_18 check13_19)) (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 11 20480 (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 20480 check13_20 check13_21) (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 22528 check13_22 check13_23))) (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 12 24576 (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 11 24576 (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 24576 check13_24 check13_25) (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 26624 check13_26 check13_27)) (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 11 28672 (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 28672 check13_28 check13_29) (checkPow_join (mulTest Data.t13 Data.t12 Data.t8) 10 30720 check13_30 check13_31)))))

theorem support13 : Supports p13 Data.t13 :=
  mul_support p12 p8 Data.t13 Data.t12 Data.t8
    support12 support8 (checked _ checked13)

private theorem check14_0 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 0 10 = true := by
  decide +kernel

private theorem check14_1 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 1024 10 = true := by
  decide +kernel

private theorem check14_2 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 2048 10 = true := by
  decide +kernel

private theorem check14_3 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 3072 10 = true := by
  decide +kernel

private theorem check14_4 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 4096 10 = true := by
  decide +kernel

private theorem check14_5 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 5120 10 = true := by
  decide +kernel

private theorem check14_6 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 6144 10 = true := by
  decide +kernel

private theorem check14_7 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 7168 10 = true := by
  decide +kernel

private theorem check14_8 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 8192 10 = true := by
  decide +kernel

private theorem check14_9 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 9216 10 = true := by
  decide +kernel

private theorem check14_10 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 10240 10 = true := by
  decide +kernel

private theorem check14_11 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 11264 10 = true := by
  decide +kernel

private theorem check14_12 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 12288 10 = true := by
  decide +kernel

private theorem check14_13 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 13312 10 = true := by
  decide +kernel

private theorem check14_14 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 14336 10 = true := by
  decide +kernel

private theorem check14_15 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 15360 10 = true := by
  decide +kernel

private theorem check14_16 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 16384 10 = true := by
  decide +kernel

private theorem check14_17 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 17408 10 = true := by
  decide +kernel

private theorem check14_18 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 18432 10 = true := by
  decide +kernel

private theorem check14_19 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 19456 10 = true := by
  decide +kernel

private theorem check14_20 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 20480 10 = true := by
  decide +kernel

private theorem check14_21 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 21504 10 = true := by
  decide +kernel

private theorem check14_22 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 22528 10 = true := by
  decide +kernel

private theorem check14_23 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 23552 10 = true := by
  decide +kernel

private theorem check14_24 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 24576 10 = true := by
  decide +kernel

private theorem check14_25 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 25600 10 = true := by
  decide +kernel

private theorem check14_26 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 26624 10 = true := by
  decide +kernel

private theorem check14_27 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 27648 10 = true := by
  decide +kernel

private theorem check14_28 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 28672 10 = true := by
  decide +kernel

private theorem check14_29 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 29696 10 = true := by
  decide +kernel

private theorem check14_30 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 30720 10 = true := by
  decide +kernel

private theorem check14_31 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 31744 10 = true := by
  decide +kernel

private theorem checked14 : checkPow (mulTest Data.t14 Data.t13 Data.t2) 0 15 = true :=
  (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 14 0 (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 13 0 (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 12 0 (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 11 0 (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 0 check14_0 check14_1) (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 2048 check14_2 check14_3)) (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 11 4096 (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 4096 check14_4 check14_5) (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 6144 check14_6 check14_7))) (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 12 8192 (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 11 8192 (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 8192 check14_8 check14_9) (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 10240 check14_10 check14_11)) (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 11 12288 (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 12288 check14_12 check14_13) (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 14336 check14_14 check14_15)))) (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 13 16384 (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 12 16384 (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 11 16384 (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 16384 check14_16 check14_17) (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 18432 check14_18 check14_19)) (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 11 20480 (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 20480 check14_20 check14_21) (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 22528 check14_22 check14_23))) (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 12 24576 (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 11 24576 (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 24576 check14_24 check14_25) (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 26624 check14_26 check14_27)) (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 11 28672 (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 28672 check14_28 check14_29) (checkPow_join (mulTest Data.t14 Data.t13 Data.t2) 10 30720 check14_30 check14_31)))))

theorem support14 : Supports p14 Data.t14 :=
  mul_support p13 p2 Data.t14 Data.t13 Data.t2
    support13 support2 (checked _ checked14)

private theorem check15_0 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 0 10 = true := by
  decide +kernel

private theorem check15_1 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 1024 10 = true := by
  decide +kernel

private theorem check15_2 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 2048 10 = true := by
  decide +kernel

private theorem check15_3 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 3072 10 = true := by
  decide +kernel

private theorem check15_4 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 4096 10 = true := by
  decide +kernel

private theorem check15_5 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 5120 10 = true := by
  decide +kernel

private theorem check15_6 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 6144 10 = true := by
  decide +kernel

private theorem check15_7 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 7168 10 = true := by
  decide +kernel

private theorem check15_8 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 8192 10 = true := by
  decide +kernel

private theorem check15_9 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 9216 10 = true := by
  decide +kernel

private theorem check15_10 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 10240 10 = true := by
  decide +kernel

private theorem check15_11 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 11264 10 = true := by
  decide +kernel

private theorem check15_12 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 12288 10 = true := by
  decide +kernel

private theorem check15_13 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 13312 10 = true := by
  decide +kernel

private theorem check15_14 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 14336 10 = true := by
  decide +kernel

private theorem check15_15 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 15360 10 = true := by
  decide +kernel

private theorem check15_16 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 16384 10 = true := by
  decide +kernel

private theorem check15_17 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 17408 10 = true := by
  decide +kernel

private theorem check15_18 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 18432 10 = true := by
  decide +kernel

private theorem check15_19 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 19456 10 = true := by
  decide +kernel

private theorem check15_20 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 20480 10 = true := by
  decide +kernel

private theorem check15_21 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 21504 10 = true := by
  decide +kernel

private theorem check15_22 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 22528 10 = true := by
  decide +kernel

private theorem check15_23 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 23552 10 = true := by
  decide +kernel

private theorem check15_24 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 24576 10 = true := by
  decide +kernel

private theorem check15_25 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 25600 10 = true := by
  decide +kernel

private theorem check15_26 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 26624 10 = true := by
  decide +kernel

private theorem check15_27 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 27648 10 = true := by
  decide +kernel

private theorem check15_28 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 28672 10 = true := by
  decide +kernel

private theorem check15_29 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 29696 10 = true := by
  decide +kernel

private theorem check15_30 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 30720 10 = true := by
  decide +kernel

private theorem check15_31 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 31744 10 = true := by
  decide +kernel

private theorem checked15 : checkPow (mulTest Data.t15 Data.t14 Data.t4) 0 15 = true :=
  (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 14 0 (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 13 0 (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 12 0 (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 11 0 (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 0 check15_0 check15_1) (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 2048 check15_2 check15_3)) (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 11 4096 (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 4096 check15_4 check15_5) (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 6144 check15_6 check15_7))) (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 12 8192 (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 11 8192 (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 8192 check15_8 check15_9) (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 10240 check15_10 check15_11)) (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 11 12288 (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 12288 check15_12 check15_13) (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 14336 check15_14 check15_15)))) (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 13 16384 (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 12 16384 (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 11 16384 (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 16384 check15_16 check15_17) (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 18432 check15_18 check15_19)) (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 11 20480 (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 20480 check15_20 check15_21) (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 22528 check15_22 check15_23))) (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 12 24576 (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 11 24576 (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 24576 check15_24 check15_25) (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 26624 check15_26 check15_27)) (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 11 28672 (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 28672 check15_28 check15_29) (checkPow_join (mulTest Data.t15 Data.t14 Data.t4) 10 30720 check15_30 check15_31)))))

theorem support15 : Supports p15 Data.t15 :=
  mul_support p14 p4 Data.t15 Data.t14 Data.t4
    support14 support4 (checked _ checked15)

private theorem check16_0 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 0 10 = true := by
  decide +kernel

private theorem check16_1 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 1024 10 = true := by
  decide +kernel

private theorem check16_2 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 2048 10 = true := by
  decide +kernel

private theorem check16_3 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 3072 10 = true := by
  decide +kernel

private theorem check16_4 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 4096 10 = true := by
  decide +kernel

private theorem check16_5 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 5120 10 = true := by
  decide +kernel

private theorem check16_6 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 6144 10 = true := by
  decide +kernel

private theorem check16_7 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 7168 10 = true := by
  decide +kernel

private theorem check16_8 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 8192 10 = true := by
  decide +kernel

private theorem check16_9 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 9216 10 = true := by
  decide +kernel

private theorem check16_10 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 10240 10 = true := by
  decide +kernel

private theorem check16_11 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 11264 10 = true := by
  decide +kernel

private theorem check16_12 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 12288 10 = true := by
  decide +kernel

private theorem check16_13 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 13312 10 = true := by
  decide +kernel

private theorem check16_14 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 14336 10 = true := by
  decide +kernel

private theorem check16_15 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 15360 10 = true := by
  decide +kernel

private theorem check16_16 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 16384 10 = true := by
  decide +kernel

private theorem check16_17 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 17408 10 = true := by
  decide +kernel

private theorem check16_18 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 18432 10 = true := by
  decide +kernel

private theorem check16_19 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 19456 10 = true := by
  decide +kernel

private theorem check16_20 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 20480 10 = true := by
  decide +kernel

private theorem check16_21 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 21504 10 = true := by
  decide +kernel

private theorem check16_22 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 22528 10 = true := by
  decide +kernel

private theorem check16_23 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 23552 10 = true := by
  decide +kernel

private theorem check16_24 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 24576 10 = true := by
  decide +kernel

private theorem check16_25 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 25600 10 = true := by
  decide +kernel

private theorem check16_26 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 26624 10 = true := by
  decide +kernel

private theorem check16_27 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 27648 10 = true := by
  decide +kernel

private theorem check16_28 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 28672 10 = true := by
  decide +kernel

private theorem check16_29 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 29696 10 = true := by
  decide +kernel

private theorem check16_30 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 30720 10 = true := by
  decide +kernel

private theorem check16_31 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 31744 10 = true := by
  decide +kernel

private theorem checked16 : checkPow (mulTest Data.t16 Data.t5 Data.t8) 0 15 = true :=
  (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 14 0 (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 13 0 (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 12 0 (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 11 0 (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 0 check16_0 check16_1) (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 2048 check16_2 check16_3)) (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 11 4096 (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 4096 check16_4 check16_5) (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 6144 check16_6 check16_7))) (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 12 8192 (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 11 8192 (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 8192 check16_8 check16_9) (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 10240 check16_10 check16_11)) (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 11 12288 (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 12288 check16_12 check16_13) (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 14336 check16_14 check16_15)))) (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 13 16384 (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 12 16384 (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 11 16384 (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 16384 check16_16 check16_17) (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 18432 check16_18 check16_19)) (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 11 20480 (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 20480 check16_20 check16_21) (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 22528 check16_22 check16_23))) (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 12 24576 (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 11 24576 (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 24576 check16_24 check16_25) (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 26624 check16_26 check16_27)) (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 11 28672 (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 28672 check16_28 check16_29) (checkPow_join (mulTest Data.t16 Data.t5 Data.t8) 10 30720 check16_30 check16_31)))))

theorem support16 : Supports p16 Data.t16 :=
  mul_support p5 p8 Data.t16 Data.t5 Data.t8
    support5 support8 (checked _ checked16)

private theorem check17_0 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 0 10 = true := by
  decide +kernel

private theorem check17_1 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 1024 10 = true := by
  decide +kernel

private theorem check17_2 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 2048 10 = true := by
  decide +kernel

private theorem check17_3 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 3072 10 = true := by
  decide +kernel

private theorem check17_4 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 4096 10 = true := by
  decide +kernel

private theorem check17_5 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 5120 10 = true := by
  decide +kernel

private theorem check17_6 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 6144 10 = true := by
  decide +kernel

private theorem check17_7 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 7168 10 = true := by
  decide +kernel

private theorem check17_8 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 8192 10 = true := by
  decide +kernel

private theorem check17_9 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 9216 10 = true := by
  decide +kernel

private theorem check17_10 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 10240 10 = true := by
  decide +kernel

private theorem check17_11 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 11264 10 = true := by
  decide +kernel

private theorem check17_12 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 12288 10 = true := by
  decide +kernel

private theorem check17_13 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 13312 10 = true := by
  decide +kernel

private theorem check17_14 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 14336 10 = true := by
  decide +kernel

private theorem check17_15 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 15360 10 = true := by
  decide +kernel

private theorem check17_16 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 16384 10 = true := by
  decide +kernel

private theorem check17_17 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 17408 10 = true := by
  decide +kernel

private theorem check17_18 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 18432 10 = true := by
  decide +kernel

private theorem check17_19 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 19456 10 = true := by
  decide +kernel

private theorem check17_20 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 20480 10 = true := by
  decide +kernel

private theorem check17_21 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 21504 10 = true := by
  decide +kernel

private theorem check17_22 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 22528 10 = true := by
  decide +kernel

private theorem check17_23 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 23552 10 = true := by
  decide +kernel

private theorem check17_24 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 24576 10 = true := by
  decide +kernel

private theorem check17_25 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 25600 10 = true := by
  decide +kernel

private theorem check17_26 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 26624 10 = true := by
  decide +kernel

private theorem check17_27 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 27648 10 = true := by
  decide +kernel

private theorem check17_28 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 28672 10 = true := by
  decide +kernel

private theorem check17_29 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 29696 10 = true := by
  decide +kernel

private theorem check17_30 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 30720 10 = true := by
  decide +kernel

private theorem check17_31 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 31744 10 = true := by
  decide +kernel

private theorem checked17 : checkPow (mulTest Data.t17 Data.t16 Data.t9) 0 15 = true :=
  (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 14 0 (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 13 0 (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 12 0 (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 11 0 (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 0 check17_0 check17_1) (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 2048 check17_2 check17_3)) (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 11 4096 (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 4096 check17_4 check17_5) (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 6144 check17_6 check17_7))) (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 12 8192 (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 11 8192 (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 8192 check17_8 check17_9) (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 10240 check17_10 check17_11)) (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 11 12288 (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 12288 check17_12 check17_13) (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 14336 check17_14 check17_15)))) (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 13 16384 (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 12 16384 (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 11 16384 (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 16384 check17_16 check17_17) (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 18432 check17_18 check17_19)) (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 11 20480 (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 20480 check17_20 check17_21) (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 22528 check17_22 check17_23))) (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 12 24576 (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 11 24576 (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 24576 check17_24 check17_25) (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 26624 check17_26 check17_27)) (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 11 28672 (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 28672 check17_28 check17_29) (checkPow_join (mulTest Data.t17 Data.t16 Data.t9) 10 30720 check17_30 check17_31)))))

theorem support17 : Supports p17 Data.t17 :=
  mul_support p16 p9 Data.t17 Data.t16 Data.t9
    support16 support9 (checked _ checked17)

private theorem check18_0 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 0 10 = true := by
  decide +kernel

private theorem check18_1 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 1024 10 = true := by
  decide +kernel

private theorem check18_2 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 2048 10 = true := by
  decide +kernel

private theorem check18_3 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 3072 10 = true := by
  decide +kernel

private theorem check18_4 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 4096 10 = true := by
  decide +kernel

private theorem check18_5 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 5120 10 = true := by
  decide +kernel

private theorem check18_6 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 6144 10 = true := by
  decide +kernel

private theorem check18_7 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 7168 10 = true := by
  decide +kernel

private theorem check18_8 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 8192 10 = true := by
  decide +kernel

private theorem check18_9 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 9216 10 = true := by
  decide +kernel

private theorem check18_10 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 10240 10 = true := by
  decide +kernel

private theorem check18_11 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 11264 10 = true := by
  decide +kernel

private theorem check18_12 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 12288 10 = true := by
  decide +kernel

private theorem check18_13 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 13312 10 = true := by
  decide +kernel

private theorem check18_14 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 14336 10 = true := by
  decide +kernel

private theorem check18_15 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 15360 10 = true := by
  decide +kernel

private theorem check18_16 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 16384 10 = true := by
  decide +kernel

private theorem check18_17 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 17408 10 = true := by
  decide +kernel

private theorem check18_18 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 18432 10 = true := by
  decide +kernel

private theorem check18_19 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 19456 10 = true := by
  decide +kernel

private theorem check18_20 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 20480 10 = true := by
  decide +kernel

private theorem check18_21 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 21504 10 = true := by
  decide +kernel

private theorem check18_22 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 22528 10 = true := by
  decide +kernel

private theorem check18_23 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 23552 10 = true := by
  decide +kernel

private theorem check18_24 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 24576 10 = true := by
  decide +kernel

private theorem check18_25 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 25600 10 = true := by
  decide +kernel

private theorem check18_26 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 26624 10 = true := by
  decide +kernel

private theorem check18_27 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 27648 10 = true := by
  decide +kernel

private theorem check18_28 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 28672 10 = true := by
  decide +kernel

private theorem check18_29 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 29696 10 = true := by
  decide +kernel

private theorem check18_30 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 30720 10 = true := by
  decide +kernel

private theorem check18_31 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 31744 10 = true := by
  decide +kernel

private theorem checked18 : checkPow (mulTest Data.t18 Data.t17 Data.t4) 0 15 = true :=
  (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 14 0 (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 13 0 (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 12 0 (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 11 0 (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 0 check18_0 check18_1) (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 2048 check18_2 check18_3)) (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 11 4096 (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 4096 check18_4 check18_5) (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 6144 check18_6 check18_7))) (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 12 8192 (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 11 8192 (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 8192 check18_8 check18_9) (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 10240 check18_10 check18_11)) (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 11 12288 (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 12288 check18_12 check18_13) (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 14336 check18_14 check18_15)))) (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 13 16384 (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 12 16384 (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 11 16384 (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 16384 check18_16 check18_17) (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 18432 check18_18 check18_19)) (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 11 20480 (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 20480 check18_20 check18_21) (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 22528 check18_22 check18_23))) (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 12 24576 (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 11 24576 (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 24576 check18_24 check18_25) (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 26624 check18_26 check18_27)) (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 11 28672 (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 28672 check18_28 check18_29) (checkPow_join (mulTest Data.t18 Data.t17 Data.t4) 10 30720 check18_30 check18_31)))))

theorem support18 : Supports p18 Data.t18 :=
  mul_support p17 p4 Data.t18 Data.t17 Data.t4
    support17 support4 (checked _ checked18)

private theorem check19_0 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 0 10 = true := by
  decide +kernel

private theorem check19_1 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 1024 10 = true := by
  decide +kernel

private theorem check19_2 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 2048 10 = true := by
  decide +kernel

private theorem check19_3 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 3072 10 = true := by
  decide +kernel

private theorem check19_4 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 4096 10 = true := by
  decide +kernel

private theorem check19_5 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 5120 10 = true := by
  decide +kernel

private theorem check19_6 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 6144 10 = true := by
  decide +kernel

private theorem check19_7 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 7168 10 = true := by
  decide +kernel

private theorem check19_8 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 8192 10 = true := by
  decide +kernel

private theorem check19_9 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 9216 10 = true := by
  decide +kernel

private theorem check19_10 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 10240 10 = true := by
  decide +kernel

private theorem check19_11 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 11264 10 = true := by
  decide +kernel

private theorem check19_12 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 12288 10 = true := by
  decide +kernel

private theorem check19_13 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 13312 10 = true := by
  decide +kernel

private theorem check19_14 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 14336 10 = true := by
  decide +kernel

private theorem check19_15 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 15360 10 = true := by
  decide +kernel

private theorem check19_16 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 16384 10 = true := by
  decide +kernel

private theorem check19_17 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 17408 10 = true := by
  decide +kernel

private theorem check19_18 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 18432 10 = true := by
  decide +kernel

private theorem check19_19 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 19456 10 = true := by
  decide +kernel

private theorem check19_20 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 20480 10 = true := by
  decide +kernel

private theorem check19_21 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 21504 10 = true := by
  decide +kernel

private theorem check19_22 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 22528 10 = true := by
  decide +kernel

private theorem check19_23 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 23552 10 = true := by
  decide +kernel

private theorem check19_24 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 24576 10 = true := by
  decide +kernel

private theorem check19_25 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 25600 10 = true := by
  decide +kernel

private theorem check19_26 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 26624 10 = true := by
  decide +kernel

private theorem check19_27 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 27648 10 = true := by
  decide +kernel

private theorem check19_28 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 28672 10 = true := by
  decide +kernel

private theorem check19_29 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 29696 10 = true := by
  decide +kernel

private theorem check19_30 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 30720 10 = true := by
  decide +kernel

private theorem check19_31 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 31744 10 = true := by
  decide +kernel

private theorem checked19 : checkPow (mulTest Data.t19 Data.t18 Data.t4) 0 15 = true :=
  (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 14 0 (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 13 0 (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 12 0 (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 11 0 (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 0 check19_0 check19_1) (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 2048 check19_2 check19_3)) (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 11 4096 (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 4096 check19_4 check19_5) (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 6144 check19_6 check19_7))) (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 12 8192 (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 11 8192 (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 8192 check19_8 check19_9) (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 10240 check19_10 check19_11)) (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 11 12288 (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 12288 check19_12 check19_13) (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 14336 check19_14 check19_15)))) (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 13 16384 (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 12 16384 (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 11 16384 (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 16384 check19_16 check19_17) (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 18432 check19_18 check19_19)) (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 11 20480 (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 20480 check19_20 check19_21) (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 22528 check19_22 check19_23))) (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 12 24576 (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 11 24576 (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 24576 check19_24 check19_25) (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 26624 check19_26 check19_27)) (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 11 28672 (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 28672 check19_28 check19_29) (checkPow_join (mulTest Data.t19 Data.t18 Data.t4) 10 30720 check19_30 check19_31)))))

theorem support19 : Supports p19 Data.t19 :=
  mul_support p18 p4 Data.t19 Data.t18 Data.t4
    support18 support4 (checked _ checked19)

private theorem check20_0 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 0 10 = true := by
  decide +kernel

private theorem check20_1 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 1024 10 = true := by
  decide +kernel

private theorem check20_2 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 2048 10 = true := by
  decide +kernel

private theorem check20_3 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 3072 10 = true := by
  decide +kernel

private theorem check20_4 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 4096 10 = true := by
  decide +kernel

private theorem check20_5 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 5120 10 = true := by
  decide +kernel

private theorem check20_6 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 6144 10 = true := by
  decide +kernel

private theorem check20_7 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 7168 10 = true := by
  decide +kernel

private theorem check20_8 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 8192 10 = true := by
  decide +kernel

private theorem check20_9 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 9216 10 = true := by
  decide +kernel

private theorem check20_10 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 10240 10 = true := by
  decide +kernel

private theorem check20_11 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 11264 10 = true := by
  decide +kernel

private theorem check20_12 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 12288 10 = true := by
  decide +kernel

private theorem check20_13 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 13312 10 = true := by
  decide +kernel

private theorem check20_14 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 14336 10 = true := by
  decide +kernel

private theorem check20_15 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 15360 10 = true := by
  decide +kernel

private theorem check20_16 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 16384 10 = true := by
  decide +kernel

private theorem check20_17 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 17408 10 = true := by
  decide +kernel

private theorem check20_18 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 18432 10 = true := by
  decide +kernel

private theorem check20_19 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 19456 10 = true := by
  decide +kernel

private theorem check20_20 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 20480 10 = true := by
  decide +kernel

private theorem check20_21 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 21504 10 = true := by
  decide +kernel

private theorem check20_22 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 22528 10 = true := by
  decide +kernel

private theorem check20_23 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 23552 10 = true := by
  decide +kernel

private theorem check20_24 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 24576 10 = true := by
  decide +kernel

private theorem check20_25 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 25600 10 = true := by
  decide +kernel

private theorem check20_26 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 26624 10 = true := by
  decide +kernel

private theorem check20_27 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 27648 10 = true := by
  decide +kernel

private theorem check20_28 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 28672 10 = true := by
  decide +kernel

private theorem check20_29 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 29696 10 = true := by
  decide +kernel

private theorem check20_30 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 30720 10 = true := by
  decide +kernel

private theorem check20_31 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 31744 10 = true := by
  decide +kernel

private theorem checked20 : checkPow (mulTest Data.t20 Data.t0 Data.t8) 0 15 = true :=
  (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 14 0 (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 13 0 (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 12 0 (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 11 0 (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 0 check20_0 check20_1) (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 2048 check20_2 check20_3)) (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 11 4096 (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 4096 check20_4 check20_5) (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 6144 check20_6 check20_7))) (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 12 8192 (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 11 8192 (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 8192 check20_8 check20_9) (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 10240 check20_10 check20_11)) (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 11 12288 (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 12288 check20_12 check20_13) (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 14336 check20_14 check20_15)))) (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 13 16384 (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 12 16384 (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 11 16384 (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 16384 check20_16 check20_17) (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 18432 check20_18 check20_19)) (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 11 20480 (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 20480 check20_20 check20_21) (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 22528 check20_22 check20_23))) (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 12 24576 (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 11 24576 (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 24576 check20_24 check20_25) (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 26624 check20_26 check20_27)) (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 11 28672 (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 28672 check20_28 check20_29) (checkPow_join (mulTest Data.t20 Data.t0 Data.t8) 10 30720 check20_30 check20_31)))))

theorem support20 : Supports p20 Data.t20 :=
  mul_support p0 p8 Data.t20 Data.t0 Data.t8
    support0 support8 (checked _ checked20)

private theorem check21_0 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 0 10 = true := by
  decide +kernel

private theorem check21_1 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 1024 10 = true := by
  decide +kernel

private theorem check21_2 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 2048 10 = true := by
  decide +kernel

private theorem check21_3 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 3072 10 = true := by
  decide +kernel

private theorem check21_4 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 4096 10 = true := by
  decide +kernel

private theorem check21_5 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 5120 10 = true := by
  decide +kernel

private theorem check21_6 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 6144 10 = true := by
  decide +kernel

private theorem check21_7 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 7168 10 = true := by
  decide +kernel

private theorem check21_8 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 8192 10 = true := by
  decide +kernel

private theorem check21_9 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 9216 10 = true := by
  decide +kernel

private theorem check21_10 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 10240 10 = true := by
  decide +kernel

private theorem check21_11 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 11264 10 = true := by
  decide +kernel

private theorem check21_12 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 12288 10 = true := by
  decide +kernel

private theorem check21_13 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 13312 10 = true := by
  decide +kernel

private theorem check21_14 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 14336 10 = true := by
  decide +kernel

private theorem check21_15 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 15360 10 = true := by
  decide +kernel

private theorem check21_16 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 16384 10 = true := by
  decide +kernel

private theorem check21_17 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 17408 10 = true := by
  decide +kernel

private theorem check21_18 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 18432 10 = true := by
  decide +kernel

private theorem check21_19 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 19456 10 = true := by
  decide +kernel

private theorem check21_20 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 20480 10 = true := by
  decide +kernel

private theorem check21_21 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 21504 10 = true := by
  decide +kernel

private theorem check21_22 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 22528 10 = true := by
  decide +kernel

private theorem check21_23 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 23552 10 = true := by
  decide +kernel

private theorem check21_24 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 24576 10 = true := by
  decide +kernel

private theorem check21_25 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 25600 10 = true := by
  decide +kernel

private theorem check21_26 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 26624 10 = true := by
  decide +kernel

private theorem check21_27 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 27648 10 = true := by
  decide +kernel

private theorem check21_28 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 28672 10 = true := by
  decide +kernel

private theorem check21_29 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 29696 10 = true := by
  decide +kernel

private theorem check21_30 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 30720 10 = true := by
  decide +kernel

private theorem check21_31 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 31744 10 = true := by
  decide +kernel

private theorem checked21 : checkPow (mulTest Data.t21 Data.t20 Data.t5) 0 15 = true :=
  (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 14 0 (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 13 0 (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 12 0 (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 11 0 (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 0 check21_0 check21_1) (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 2048 check21_2 check21_3)) (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 11 4096 (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 4096 check21_4 check21_5) (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 6144 check21_6 check21_7))) (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 12 8192 (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 11 8192 (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 8192 check21_8 check21_9) (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 10240 check21_10 check21_11)) (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 11 12288 (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 12288 check21_12 check21_13) (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 14336 check21_14 check21_15)))) (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 13 16384 (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 12 16384 (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 11 16384 (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 16384 check21_16 check21_17) (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 18432 check21_18 check21_19)) (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 11 20480 (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 20480 check21_20 check21_21) (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 22528 check21_22 check21_23))) (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 12 24576 (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 11 24576 (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 24576 check21_24 check21_25) (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 26624 check21_26 check21_27)) (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 11 28672 (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 28672 check21_28 check21_29) (checkPow_join (mulTest Data.t21 Data.t20 Data.t5) 10 30720 check21_30 check21_31)))))

theorem support21 : Supports p21 Data.t21 :=
  mul_support p20 p5 Data.t21 Data.t20 Data.t5
    support20 support5 (checked _ checked21)

private theorem check22_0 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 0 10 = true := by
  decide +kernel

private theorem check22_1 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 1024 10 = true := by
  decide +kernel

private theorem check22_2 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 2048 10 = true := by
  decide +kernel

private theorem check22_3 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 3072 10 = true := by
  decide +kernel

private theorem check22_4 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 4096 10 = true := by
  decide +kernel

private theorem check22_5 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 5120 10 = true := by
  decide +kernel

private theorem check22_6 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 6144 10 = true := by
  decide +kernel

private theorem check22_7 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 7168 10 = true := by
  decide +kernel

private theorem check22_8 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 8192 10 = true := by
  decide +kernel

private theorem check22_9 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 9216 10 = true := by
  decide +kernel

private theorem check22_10 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 10240 10 = true := by
  decide +kernel

private theorem check22_11 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 11264 10 = true := by
  decide +kernel

private theorem check22_12 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 12288 10 = true := by
  decide +kernel

private theorem check22_13 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 13312 10 = true := by
  decide +kernel

private theorem check22_14 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 14336 10 = true := by
  decide +kernel

private theorem check22_15 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 15360 10 = true := by
  decide +kernel

private theorem check22_16 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 16384 10 = true := by
  decide +kernel

private theorem check22_17 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 17408 10 = true := by
  decide +kernel

private theorem check22_18 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 18432 10 = true := by
  decide +kernel

private theorem check22_19 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 19456 10 = true := by
  decide +kernel

private theorem check22_20 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 20480 10 = true := by
  decide +kernel

private theorem check22_21 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 21504 10 = true := by
  decide +kernel

private theorem check22_22 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 22528 10 = true := by
  decide +kernel

private theorem check22_23 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 23552 10 = true := by
  decide +kernel

private theorem check22_24 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 24576 10 = true := by
  decide +kernel

private theorem check22_25 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 25600 10 = true := by
  decide +kernel

private theorem check22_26 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 26624 10 = true := by
  decide +kernel

private theorem check22_27 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 27648 10 = true := by
  decide +kernel

private theorem check22_28 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 28672 10 = true := by
  decide +kernel

private theorem check22_29 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 29696 10 = true := by
  decide +kernel

private theorem check22_30 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 30720 10 = true := by
  decide +kernel

private theorem check22_31 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 31744 10 = true := by
  decide +kernel

private theorem checked22 : checkPow (mulTest Data.t22 Data.t21 Data.t9) 0 15 = true :=
  (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 14 0 (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 13 0 (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 12 0 (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 11 0 (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 0 check22_0 check22_1) (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 2048 check22_2 check22_3)) (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 11 4096 (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 4096 check22_4 check22_5) (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 6144 check22_6 check22_7))) (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 12 8192 (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 11 8192 (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 8192 check22_8 check22_9) (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 10240 check22_10 check22_11)) (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 11 12288 (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 12288 check22_12 check22_13) (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 14336 check22_14 check22_15)))) (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 13 16384 (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 12 16384 (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 11 16384 (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 16384 check22_16 check22_17) (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 18432 check22_18 check22_19)) (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 11 20480 (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 20480 check22_20 check22_21) (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 22528 check22_22 check22_23))) (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 12 24576 (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 11 24576 (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 24576 check22_24 check22_25) (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 26624 check22_26 check22_27)) (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 11 28672 (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 28672 check22_28 check22_29) (checkPow_join (mulTest Data.t22 Data.t21 Data.t9) 10 30720 check22_30 check22_31)))))

theorem support22 : Supports p22 Data.t22 :=
  mul_support p21 p9 Data.t22 Data.t21 Data.t9
    support21 support9 (checked _ checked22)

private theorem check23_0 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 0 10 = true := by
  decide +kernel

private theorem check23_1 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 1024 10 = true := by
  decide +kernel

private theorem check23_2 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 2048 10 = true := by
  decide +kernel

private theorem check23_3 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 3072 10 = true := by
  decide +kernel

private theorem check23_4 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 4096 10 = true := by
  decide +kernel

private theorem check23_5 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 5120 10 = true := by
  decide +kernel

private theorem check23_6 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 6144 10 = true := by
  decide +kernel

private theorem check23_7 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 7168 10 = true := by
  decide +kernel

private theorem check23_8 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 8192 10 = true := by
  decide +kernel

private theorem check23_9 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 9216 10 = true := by
  decide +kernel

private theorem check23_10 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 10240 10 = true := by
  decide +kernel

private theorem check23_11 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 11264 10 = true := by
  decide +kernel

private theorem check23_12 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 12288 10 = true := by
  decide +kernel

private theorem check23_13 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 13312 10 = true := by
  decide +kernel

private theorem check23_14 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 14336 10 = true := by
  decide +kernel

private theorem check23_15 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 15360 10 = true := by
  decide +kernel

private theorem check23_16 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 16384 10 = true := by
  decide +kernel

private theorem check23_17 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 17408 10 = true := by
  decide +kernel

private theorem check23_18 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 18432 10 = true := by
  decide +kernel

private theorem check23_19 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 19456 10 = true := by
  decide +kernel

private theorem check23_20 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 20480 10 = true := by
  decide +kernel

private theorem check23_21 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 21504 10 = true := by
  decide +kernel

private theorem check23_22 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 22528 10 = true := by
  decide +kernel

private theorem check23_23 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 23552 10 = true := by
  decide +kernel

private theorem check23_24 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 24576 10 = true := by
  decide +kernel

private theorem check23_25 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 25600 10 = true := by
  decide +kernel

private theorem check23_26 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 26624 10 = true := by
  decide +kernel

private theorem check23_27 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 27648 10 = true := by
  decide +kernel

private theorem check23_28 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 28672 10 = true := by
  decide +kernel

private theorem check23_29 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 29696 10 = true := by
  decide +kernel

private theorem check23_30 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 30720 10 = true := by
  decide +kernel

private theorem check23_31 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 31744 10 = true := by
  decide +kernel

private theorem checked23 : checkPow (mulTest Data.t23 Data.t22 Data.t2) 0 15 = true :=
  (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 14 0 (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 13 0 (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 12 0 (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 11 0 (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 0 check23_0 check23_1) (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 2048 check23_2 check23_3)) (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 11 4096 (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 4096 check23_4 check23_5) (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 6144 check23_6 check23_7))) (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 12 8192 (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 11 8192 (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 8192 check23_8 check23_9) (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 10240 check23_10 check23_11)) (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 11 12288 (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 12288 check23_12 check23_13) (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 14336 check23_14 check23_15)))) (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 13 16384 (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 12 16384 (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 11 16384 (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 16384 check23_16 check23_17) (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 18432 check23_18 check23_19)) (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 11 20480 (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 20480 check23_20 check23_21) (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 22528 check23_22 check23_23))) (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 12 24576 (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 11 24576 (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 24576 check23_24 check23_25) (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 26624 check23_26 check23_27)) (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 11 28672 (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 28672 check23_28 check23_29) (checkPow_join (mulTest Data.t23 Data.t22 Data.t2) 10 30720 check23_30 check23_31)))))

theorem support23 : Supports p23 Data.t23 :=
  mul_support p22 p2 Data.t23 Data.t22 Data.t2
    support22 support2 (checked _ checked23)

private theorem check24_0 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 0 10 = true := by
  decide +kernel

private theorem check24_1 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 1024 10 = true := by
  decide +kernel

private theorem check24_2 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 2048 10 = true := by
  decide +kernel

private theorem check24_3 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 3072 10 = true := by
  decide +kernel

private theorem check24_4 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 4096 10 = true := by
  decide +kernel

private theorem check24_5 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 5120 10 = true := by
  decide +kernel

private theorem check24_6 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 6144 10 = true := by
  decide +kernel

private theorem check24_7 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 7168 10 = true := by
  decide +kernel

private theorem check24_8 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 8192 10 = true := by
  decide +kernel

private theorem check24_9 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 9216 10 = true := by
  decide +kernel

private theorem check24_10 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 10240 10 = true := by
  decide +kernel

private theorem check24_11 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 11264 10 = true := by
  decide +kernel

private theorem check24_12 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 12288 10 = true := by
  decide +kernel

private theorem check24_13 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 13312 10 = true := by
  decide +kernel

private theorem check24_14 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 14336 10 = true := by
  decide +kernel

private theorem check24_15 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 15360 10 = true := by
  decide +kernel

private theorem check24_16 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 16384 10 = true := by
  decide +kernel

private theorem check24_17 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 17408 10 = true := by
  decide +kernel

private theorem check24_18 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 18432 10 = true := by
  decide +kernel

private theorem check24_19 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 19456 10 = true := by
  decide +kernel

private theorem check24_20 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 20480 10 = true := by
  decide +kernel

private theorem check24_21 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 21504 10 = true := by
  decide +kernel

private theorem check24_22 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 22528 10 = true := by
  decide +kernel

private theorem check24_23 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 23552 10 = true := by
  decide +kernel

private theorem check24_24 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 24576 10 = true := by
  decide +kernel

private theorem check24_25 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 25600 10 = true := by
  decide +kernel

private theorem check24_26 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 26624 10 = true := by
  decide +kernel

private theorem check24_27 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 27648 10 = true := by
  decide +kernel

private theorem check24_28 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 28672 10 = true := by
  decide +kernel

private theorem check24_29 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 29696 10 = true := by
  decide +kernel

private theorem check24_30 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 30720 10 = true := by
  decide +kernel

private theorem check24_31 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 31744 10 = true := by
  decide +kernel

private theorem checked24 : checkPow (mulTest Data.t24 Data.t6 Data.t6) 0 15 = true :=
  (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 14 0 (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 13 0 (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 12 0 (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 11 0 (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 0 check24_0 check24_1) (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 2048 check24_2 check24_3)) (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 11 4096 (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 4096 check24_4 check24_5) (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 6144 check24_6 check24_7))) (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 12 8192 (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 11 8192 (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 8192 check24_8 check24_9) (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 10240 check24_10 check24_11)) (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 11 12288 (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 12288 check24_12 check24_13) (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 14336 check24_14 check24_15)))) (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 13 16384 (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 12 16384 (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 11 16384 (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 16384 check24_16 check24_17) (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 18432 check24_18 check24_19)) (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 11 20480 (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 20480 check24_20 check24_21) (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 22528 check24_22 check24_23))) (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 12 24576 (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 11 24576 (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 24576 check24_24 check24_25) (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 26624 check24_26 check24_27)) (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 11 28672 (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 28672 check24_28 check24_29) (checkPow_join (mulTest Data.t24 Data.t6 Data.t6) 10 30720 check24_30 check24_31)))))

theorem support24 : Supports p24 Data.t24 :=
  mul_support p6 p6 Data.t24 Data.t6 Data.t6
    support6 support6 (checked _ checked24)

private theorem check25_0 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 0 10 = true := by
  decide +kernel

private theorem check25_1 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 1024 10 = true := by
  decide +kernel

private theorem check25_2 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 2048 10 = true := by
  decide +kernel

private theorem check25_3 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 3072 10 = true := by
  decide +kernel

private theorem check25_4 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 4096 10 = true := by
  decide +kernel

private theorem check25_5 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 5120 10 = true := by
  decide +kernel

private theorem check25_6 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 6144 10 = true := by
  decide +kernel

private theorem check25_7 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 7168 10 = true := by
  decide +kernel

private theorem check25_8 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 8192 10 = true := by
  decide +kernel

private theorem check25_9 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 9216 10 = true := by
  decide +kernel

private theorem check25_10 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 10240 10 = true := by
  decide +kernel

private theorem check25_11 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 11264 10 = true := by
  decide +kernel

private theorem check25_12 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 12288 10 = true := by
  decide +kernel

private theorem check25_13 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 13312 10 = true := by
  decide +kernel

private theorem check25_14 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 14336 10 = true := by
  decide +kernel

private theorem check25_15 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 15360 10 = true := by
  decide +kernel

private theorem check25_16 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 16384 10 = true := by
  decide +kernel

private theorem check25_17 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 17408 10 = true := by
  decide +kernel

private theorem check25_18 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 18432 10 = true := by
  decide +kernel

private theorem check25_19 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 19456 10 = true := by
  decide +kernel

private theorem check25_20 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 20480 10 = true := by
  decide +kernel

private theorem check25_21 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 21504 10 = true := by
  decide +kernel

private theorem check25_22 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 22528 10 = true := by
  decide +kernel

private theorem check25_23 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 23552 10 = true := by
  decide +kernel

private theorem check25_24 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 24576 10 = true := by
  decide +kernel

private theorem check25_25 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 25600 10 = true := by
  decide +kernel

private theorem check25_26 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 26624 10 = true := by
  decide +kernel

private theorem check25_27 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 27648 10 = true := by
  decide +kernel

private theorem check25_28 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 28672 10 = true := by
  decide +kernel

private theorem check25_29 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 29696 10 = true := by
  decide +kernel

private theorem check25_30 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 30720 10 = true := by
  decide +kernel

private theorem check25_31 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 31744 10 = true := by
  decide +kernel

private theorem checked25 : checkPow (mulTest Data.t25 Data.t24 Data.t7) 0 15 = true :=
  (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 14 0 (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 13 0 (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 12 0 (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 11 0 (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 0 check25_0 check25_1) (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 2048 check25_2 check25_3)) (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 11 4096 (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 4096 check25_4 check25_5) (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 6144 check25_6 check25_7))) (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 12 8192 (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 11 8192 (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 8192 check25_8 check25_9) (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 10240 check25_10 check25_11)) (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 11 12288 (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 12288 check25_12 check25_13) (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 14336 check25_14 check25_15)))) (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 13 16384 (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 12 16384 (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 11 16384 (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 16384 check25_16 check25_17) (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 18432 check25_18 check25_19)) (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 11 20480 (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 20480 check25_20 check25_21) (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 22528 check25_22 check25_23))) (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 12 24576 (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 11 24576 (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 24576 check25_24 check25_25) (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 26624 check25_26 check25_27)) (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 11 28672 (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 28672 check25_28 check25_29) (checkPow_join (mulTest Data.t25 Data.t24 Data.t7) 10 30720 check25_30 check25_31)))))

theorem support25 : Supports p25 Data.t25 :=
  mul_support p24 p7 Data.t25 Data.t24 Data.t7
    support24 support7 (checked _ checked25)

private theorem check26_0 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 0 10 = true := by
  decide +kernel

private theorem check26_1 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 1024 10 = true := by
  decide +kernel

private theorem check26_2 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 2048 10 = true := by
  decide +kernel

private theorem check26_3 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 3072 10 = true := by
  decide +kernel

private theorem check26_4 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 4096 10 = true := by
  decide +kernel

private theorem check26_5 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 5120 10 = true := by
  decide +kernel

private theorem check26_6 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 6144 10 = true := by
  decide +kernel

private theorem check26_7 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 7168 10 = true := by
  decide +kernel

private theorem check26_8 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 8192 10 = true := by
  decide +kernel

private theorem check26_9 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 9216 10 = true := by
  decide +kernel

private theorem check26_10 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 10240 10 = true := by
  decide +kernel

private theorem check26_11 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 11264 10 = true := by
  decide +kernel

private theorem check26_12 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 12288 10 = true := by
  decide +kernel

private theorem check26_13 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 13312 10 = true := by
  decide +kernel

private theorem check26_14 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 14336 10 = true := by
  decide +kernel

private theorem check26_15 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 15360 10 = true := by
  decide +kernel

private theorem check26_16 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 16384 10 = true := by
  decide +kernel

private theorem check26_17 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 17408 10 = true := by
  decide +kernel

private theorem check26_18 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 18432 10 = true := by
  decide +kernel

private theorem check26_19 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 19456 10 = true := by
  decide +kernel

private theorem check26_20 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 20480 10 = true := by
  decide +kernel

private theorem check26_21 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 21504 10 = true := by
  decide +kernel

private theorem check26_22 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 22528 10 = true := by
  decide +kernel

private theorem check26_23 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 23552 10 = true := by
  decide +kernel

private theorem check26_24 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 24576 10 = true := by
  decide +kernel

private theorem check26_25 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 25600 10 = true := by
  decide +kernel

private theorem check26_26 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 26624 10 = true := by
  decide +kernel

private theorem check26_27 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 27648 10 = true := by
  decide +kernel

private theorem check26_28 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 28672 10 = true := by
  decide +kernel

private theorem check26_29 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 29696 10 = true := by
  decide +kernel

private theorem check26_30 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 30720 10 = true := by
  decide +kernel

private theorem check26_31 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 31744 10 = true := by
  decide +kernel

private theorem checked26 : checkPow (mulTest Data.t26 Data.t25 Data.t4) 0 15 = true :=
  (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 14 0 (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 13 0 (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 12 0 (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 11 0 (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 0 check26_0 check26_1) (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 2048 check26_2 check26_3)) (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 11 4096 (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 4096 check26_4 check26_5) (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 6144 check26_6 check26_7))) (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 12 8192 (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 11 8192 (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 8192 check26_8 check26_9) (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 10240 check26_10 check26_11)) (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 11 12288 (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 12288 check26_12 check26_13) (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 14336 check26_14 check26_15)))) (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 13 16384 (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 12 16384 (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 11 16384 (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 16384 check26_16 check26_17) (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 18432 check26_18 check26_19)) (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 11 20480 (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 20480 check26_20 check26_21) (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 22528 check26_22 check26_23))) (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 12 24576 (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 11 24576 (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 24576 check26_24 check26_25) (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 26624 check26_26 check26_27)) (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 11 28672 (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 28672 check26_28 check26_29) (checkPow_join (mulTest Data.t26 Data.t25 Data.t4) 10 30720 check26_30 check26_31)))))

theorem support26 : Supports p26 Data.t26 :=
  mul_support p25 p4 Data.t26 Data.t25 Data.t4
    support25 support4 (checked _ checked26)

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.OrbitActions
