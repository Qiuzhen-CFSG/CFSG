module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.OrbitActions.ChecksShort
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.OrbitActions.DataFirst

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

private theorem check27_0 : checkPow (invTest Data.t27 Data.t19) 0 10 = true := by
  decide +kernel

private theorem check27_1 : checkPow (invTest Data.t27 Data.t19) 1024 10 = true := by
  decide +kernel

private theorem check27_2 : checkPow (invTest Data.t27 Data.t19) 2048 10 = true := by
  decide +kernel

private theorem check27_3 : checkPow (invTest Data.t27 Data.t19) 3072 10 = true := by
  decide +kernel

private theorem check27_4 : checkPow (invTest Data.t27 Data.t19) 4096 10 = true := by
  decide +kernel

private theorem check27_5 : checkPow (invTest Data.t27 Data.t19) 5120 10 = true := by
  decide +kernel

private theorem check27_6 : checkPow (invTest Data.t27 Data.t19) 6144 10 = true := by
  decide +kernel

private theorem check27_7 : checkPow (invTest Data.t27 Data.t19) 7168 10 = true := by
  decide +kernel

private theorem check27_8 : checkPow (invTest Data.t27 Data.t19) 8192 10 = true := by
  decide +kernel

private theorem check27_9 : checkPow (invTest Data.t27 Data.t19) 9216 10 = true := by
  decide +kernel

private theorem check27_10 : checkPow (invTest Data.t27 Data.t19) 10240 10 = true := by
  decide +kernel

private theorem check27_11 : checkPow (invTest Data.t27 Data.t19) 11264 10 = true := by
  decide +kernel

private theorem check27_12 : checkPow (invTest Data.t27 Data.t19) 12288 10 = true := by
  decide +kernel

private theorem check27_13 : checkPow (invTest Data.t27 Data.t19) 13312 10 = true := by
  decide +kernel

private theorem check27_14 : checkPow (invTest Data.t27 Data.t19) 14336 10 = true := by
  decide +kernel

private theorem check27_15 : checkPow (invTest Data.t27 Data.t19) 15360 10 = true := by
  decide +kernel

private theorem check27_16 : checkPow (invTest Data.t27 Data.t19) 16384 10 = true := by
  decide +kernel

private theorem check27_17 : checkPow (invTest Data.t27 Data.t19) 17408 10 = true := by
  decide +kernel

private theorem check27_18 : checkPow (invTest Data.t27 Data.t19) 18432 10 = true := by
  decide +kernel

private theorem check27_19 : checkPow (invTest Data.t27 Data.t19) 19456 10 = true := by
  decide +kernel

private theorem check27_20 : checkPow (invTest Data.t27 Data.t19) 20480 10 = true := by
  decide +kernel

private theorem check27_21 : checkPow (invTest Data.t27 Data.t19) 21504 10 = true := by
  decide +kernel

private theorem check27_22 : checkPow (invTest Data.t27 Data.t19) 22528 10 = true := by
  decide +kernel

private theorem check27_23 : checkPow (invTest Data.t27 Data.t19) 23552 10 = true := by
  decide +kernel

private theorem check27_24 : checkPow (invTest Data.t27 Data.t19) 24576 10 = true := by
  decide +kernel

private theorem check27_25 : checkPow (invTest Data.t27 Data.t19) 25600 10 = true := by
  decide +kernel

private theorem check27_26 : checkPow (invTest Data.t27 Data.t19) 26624 10 = true := by
  decide +kernel

private theorem check27_27 : checkPow (invTest Data.t27 Data.t19) 27648 10 = true := by
  decide +kernel

private theorem check27_28 : checkPow (invTest Data.t27 Data.t19) 28672 10 = true := by
  decide +kernel

private theorem check27_29 : checkPow (invTest Data.t27 Data.t19) 29696 10 = true := by
  decide +kernel

private theorem check27_30 : checkPow (invTest Data.t27 Data.t19) 30720 10 = true := by
  decide +kernel

private theorem check27_31 : checkPow (invTest Data.t27 Data.t19) 31744 10 = true := by
  decide +kernel

private theorem checked27 : checkPow (invTest Data.t27 Data.t19) 0 15 = true :=
  (checkPow_join (invTest Data.t27 Data.t19) 14 0 (checkPow_join (invTest Data.t27 Data.t19) 13 0 (checkPow_join (invTest Data.t27 Data.t19) 12 0 (checkPow_join (invTest Data.t27 Data.t19) 11 0 (checkPow_join (invTest Data.t27 Data.t19) 10 0 check27_0 check27_1) (checkPow_join (invTest Data.t27 Data.t19) 10 2048 check27_2 check27_3)) (checkPow_join (invTest Data.t27 Data.t19) 11 4096 (checkPow_join (invTest Data.t27 Data.t19) 10 4096 check27_4 check27_5) (checkPow_join (invTest Data.t27 Data.t19) 10 6144 check27_6 check27_7))) (checkPow_join (invTest Data.t27 Data.t19) 12 8192 (checkPow_join (invTest Data.t27 Data.t19) 11 8192 (checkPow_join (invTest Data.t27 Data.t19) 10 8192 check27_8 check27_9) (checkPow_join (invTest Data.t27 Data.t19) 10 10240 check27_10 check27_11)) (checkPow_join (invTest Data.t27 Data.t19) 11 12288 (checkPow_join (invTest Data.t27 Data.t19) 10 12288 check27_12 check27_13) (checkPow_join (invTest Data.t27 Data.t19) 10 14336 check27_14 check27_15)))) (checkPow_join (invTest Data.t27 Data.t19) 13 16384 (checkPow_join (invTest Data.t27 Data.t19) 12 16384 (checkPow_join (invTest Data.t27 Data.t19) 11 16384 (checkPow_join (invTest Data.t27 Data.t19) 10 16384 check27_16 check27_17) (checkPow_join (invTest Data.t27 Data.t19) 10 18432 check27_18 check27_19)) (checkPow_join (invTest Data.t27 Data.t19) 11 20480 (checkPow_join (invTest Data.t27 Data.t19) 10 20480 check27_20 check27_21) (checkPow_join (invTest Data.t27 Data.t19) 10 22528 check27_22 check27_23))) (checkPow_join (invTest Data.t27 Data.t19) 12 24576 (checkPow_join (invTest Data.t27 Data.t19) 11 24576 (checkPow_join (invTest Data.t27 Data.t19) 10 24576 check27_24 check27_25) (checkPow_join (invTest Data.t27 Data.t19) 10 26624 check27_26 check27_27)) (checkPow_join (invTest Data.t27 Data.t19) 11 28672 (checkPow_join (invTest Data.t27 Data.t19) 10 28672 check27_28 check27_29) (checkPow_join (invTest Data.t27 Data.t19) 10 30720 check27_30 check27_31)))))

theorem support27 : Supports p27 Data.t27 :=
  inv_support p19 Data.t27 Data.t19 support19 (checked _ checked27)

private theorem check28_0 : checkPow (invTest Data.t28 Data.t26) 0 10 = true := by
  decide +kernel

private theorem check28_1 : checkPow (invTest Data.t28 Data.t26) 1024 10 = true := by
  decide +kernel

private theorem check28_2 : checkPow (invTest Data.t28 Data.t26) 2048 10 = true := by
  decide +kernel

private theorem check28_3 : checkPow (invTest Data.t28 Data.t26) 3072 10 = true := by
  decide +kernel

private theorem check28_4 : checkPow (invTest Data.t28 Data.t26) 4096 10 = true := by
  decide +kernel

private theorem check28_5 : checkPow (invTest Data.t28 Data.t26) 5120 10 = true := by
  decide +kernel

private theorem check28_6 : checkPow (invTest Data.t28 Data.t26) 6144 10 = true := by
  decide +kernel

private theorem check28_7 : checkPow (invTest Data.t28 Data.t26) 7168 10 = true := by
  decide +kernel

private theorem check28_8 : checkPow (invTest Data.t28 Data.t26) 8192 10 = true := by
  decide +kernel

private theorem check28_9 : checkPow (invTest Data.t28 Data.t26) 9216 10 = true := by
  decide +kernel

private theorem check28_10 : checkPow (invTest Data.t28 Data.t26) 10240 10 = true := by
  decide +kernel

private theorem check28_11 : checkPow (invTest Data.t28 Data.t26) 11264 10 = true := by
  decide +kernel

private theorem check28_12 : checkPow (invTest Data.t28 Data.t26) 12288 10 = true := by
  decide +kernel

private theorem check28_13 : checkPow (invTest Data.t28 Data.t26) 13312 10 = true := by
  decide +kernel

private theorem check28_14 : checkPow (invTest Data.t28 Data.t26) 14336 10 = true := by
  decide +kernel

private theorem check28_15 : checkPow (invTest Data.t28 Data.t26) 15360 10 = true := by
  decide +kernel

private theorem check28_16 : checkPow (invTest Data.t28 Data.t26) 16384 10 = true := by
  decide +kernel

private theorem check28_17 : checkPow (invTest Data.t28 Data.t26) 17408 10 = true := by
  decide +kernel

private theorem check28_18 : checkPow (invTest Data.t28 Data.t26) 18432 10 = true := by
  decide +kernel

private theorem check28_19 : checkPow (invTest Data.t28 Data.t26) 19456 10 = true := by
  decide +kernel

private theorem check28_20 : checkPow (invTest Data.t28 Data.t26) 20480 10 = true := by
  decide +kernel

private theorem check28_21 : checkPow (invTest Data.t28 Data.t26) 21504 10 = true := by
  decide +kernel

private theorem check28_22 : checkPow (invTest Data.t28 Data.t26) 22528 10 = true := by
  decide +kernel

private theorem check28_23 : checkPow (invTest Data.t28 Data.t26) 23552 10 = true := by
  decide +kernel

private theorem check28_24 : checkPow (invTest Data.t28 Data.t26) 24576 10 = true := by
  decide +kernel

private theorem check28_25 : checkPow (invTest Data.t28 Data.t26) 25600 10 = true := by
  decide +kernel

private theorem check28_26 : checkPow (invTest Data.t28 Data.t26) 26624 10 = true := by
  decide +kernel

private theorem check28_27 : checkPow (invTest Data.t28 Data.t26) 27648 10 = true := by
  decide +kernel

private theorem check28_28 : checkPow (invTest Data.t28 Data.t26) 28672 10 = true := by
  decide +kernel

private theorem check28_29 : checkPow (invTest Data.t28 Data.t26) 29696 10 = true := by
  decide +kernel

private theorem check28_30 : checkPow (invTest Data.t28 Data.t26) 30720 10 = true := by
  decide +kernel

private theorem check28_31 : checkPow (invTest Data.t28 Data.t26) 31744 10 = true := by
  decide +kernel

private theorem checked28 : checkPow (invTest Data.t28 Data.t26) 0 15 = true :=
  (checkPow_join (invTest Data.t28 Data.t26) 14 0 (checkPow_join (invTest Data.t28 Data.t26) 13 0 (checkPow_join (invTest Data.t28 Data.t26) 12 0 (checkPow_join (invTest Data.t28 Data.t26) 11 0 (checkPow_join (invTest Data.t28 Data.t26) 10 0 check28_0 check28_1) (checkPow_join (invTest Data.t28 Data.t26) 10 2048 check28_2 check28_3)) (checkPow_join (invTest Data.t28 Data.t26) 11 4096 (checkPow_join (invTest Data.t28 Data.t26) 10 4096 check28_4 check28_5) (checkPow_join (invTest Data.t28 Data.t26) 10 6144 check28_6 check28_7))) (checkPow_join (invTest Data.t28 Data.t26) 12 8192 (checkPow_join (invTest Data.t28 Data.t26) 11 8192 (checkPow_join (invTest Data.t28 Data.t26) 10 8192 check28_8 check28_9) (checkPow_join (invTest Data.t28 Data.t26) 10 10240 check28_10 check28_11)) (checkPow_join (invTest Data.t28 Data.t26) 11 12288 (checkPow_join (invTest Data.t28 Data.t26) 10 12288 check28_12 check28_13) (checkPow_join (invTest Data.t28 Data.t26) 10 14336 check28_14 check28_15)))) (checkPow_join (invTest Data.t28 Data.t26) 13 16384 (checkPow_join (invTest Data.t28 Data.t26) 12 16384 (checkPow_join (invTest Data.t28 Data.t26) 11 16384 (checkPow_join (invTest Data.t28 Data.t26) 10 16384 check28_16 check28_17) (checkPow_join (invTest Data.t28 Data.t26) 10 18432 check28_18 check28_19)) (checkPow_join (invTest Data.t28 Data.t26) 11 20480 (checkPow_join (invTest Data.t28 Data.t26) 10 20480 check28_20 check28_21) (checkPow_join (invTest Data.t28 Data.t26) 10 22528 check28_22 check28_23))) (checkPow_join (invTest Data.t28 Data.t26) 12 24576 (checkPow_join (invTest Data.t28 Data.t26) 11 24576 (checkPow_join (invTest Data.t28 Data.t26) 10 24576 check28_24 check28_25) (checkPow_join (invTest Data.t28 Data.t26) 10 26624 check28_26 check28_27)) (checkPow_join (invTest Data.t28 Data.t26) 11 28672 (checkPow_join (invTest Data.t28 Data.t26) 10 28672 check28_28 check28_29) (checkPow_join (invTest Data.t28 Data.t26) 10 30720 check28_30 check28_31)))))

theorem support28 : Supports p28 Data.t28 :=
  inv_support p26 Data.t28 Data.t26 support26 (checked _ checked28)

private theorem check29_0 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 0 10 = true := by
  decide +kernel

private theorem check29_1 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 1024 10 = true := by
  decide +kernel

private theorem check29_2 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 2048 10 = true := by
  decide +kernel

private theorem check29_3 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 3072 10 = true := by
  decide +kernel

private theorem check29_4 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 4096 10 = true := by
  decide +kernel

private theorem check29_5 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 5120 10 = true := by
  decide +kernel

private theorem check29_6 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 6144 10 = true := by
  decide +kernel

private theorem check29_7 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 7168 10 = true := by
  decide +kernel

private theorem check29_8 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 8192 10 = true := by
  decide +kernel

private theorem check29_9 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 9216 10 = true := by
  decide +kernel

private theorem check29_10 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 10240 10 = true := by
  decide +kernel

private theorem check29_11 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 11264 10 = true := by
  decide +kernel

private theorem check29_12 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 12288 10 = true := by
  decide +kernel

private theorem check29_13 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 13312 10 = true := by
  decide +kernel

private theorem check29_14 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 14336 10 = true := by
  decide +kernel

private theorem check29_15 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 15360 10 = true := by
  decide +kernel

private theorem check29_16 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 16384 10 = true := by
  decide +kernel

private theorem check29_17 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 17408 10 = true := by
  decide +kernel

private theorem check29_18 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 18432 10 = true := by
  decide +kernel

private theorem check29_19 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 19456 10 = true := by
  decide +kernel

private theorem check29_20 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 20480 10 = true := by
  decide +kernel

private theorem check29_21 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 21504 10 = true := by
  decide +kernel

private theorem check29_22 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 22528 10 = true := by
  decide +kernel

private theorem check29_23 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 23552 10 = true := by
  decide +kernel

private theorem check29_24 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 24576 10 = true := by
  decide +kernel

private theorem check29_25 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 25600 10 = true := by
  decide +kernel

private theorem check29_26 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 26624 10 = true := by
  decide +kernel

private theorem check29_27 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 27648 10 = true := by
  decide +kernel

private theorem check29_28 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 28672 10 = true := by
  decide +kernel

private theorem check29_29 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 29696 10 = true := by
  decide +kernel

private theorem check29_30 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 30720 10 = true := by
  decide +kernel

private theorem check29_31 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 31744 10 = true := by
  decide +kernel

private theorem checked29 : checkPow (mulTest Data.t29 Data.t15 Data.t1) 0 15 = true :=
  (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 14 0 (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 13 0 (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 12 0 (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 11 0 (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 0 check29_0 check29_1) (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 2048 check29_2 check29_3)) (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 11 4096 (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 4096 check29_4 check29_5) (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 6144 check29_6 check29_7))) (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 12 8192 (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 11 8192 (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 8192 check29_8 check29_9) (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 10240 check29_10 check29_11)) (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 11 12288 (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 12288 check29_12 check29_13) (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 14336 check29_14 check29_15)))) (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 13 16384 (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 12 16384 (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 11 16384 (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 16384 check29_16 check29_17) (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 18432 check29_18 check29_19)) (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 11 20480 (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 20480 check29_20 check29_21) (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 22528 check29_22 check29_23))) (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 12 24576 (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 11 24576 (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 24576 check29_24 check29_25) (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 26624 check29_26 check29_27)) (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 11 28672 (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 28672 check29_28 check29_29) (checkPow_join (mulTest Data.t29 Data.t15 Data.t1) 10 30720 check29_30 check29_31)))))

theorem support29 : Supports p29 Data.t29 :=
  mul_support p15 p1 Data.t29 Data.t15 Data.t1
    support15 support1 (checked _ checked29)

private theorem check30_0 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 0 10 = true := by
  decide +kernel

private theorem check30_1 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 1024 10 = true := by
  decide +kernel

private theorem check30_2 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 2048 10 = true := by
  decide +kernel

private theorem check30_3 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 3072 10 = true := by
  decide +kernel

private theorem check30_4 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 4096 10 = true := by
  decide +kernel

private theorem check30_5 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 5120 10 = true := by
  decide +kernel

private theorem check30_6 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 6144 10 = true := by
  decide +kernel

private theorem check30_7 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 7168 10 = true := by
  decide +kernel

private theorem check30_8 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 8192 10 = true := by
  decide +kernel

private theorem check30_9 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 9216 10 = true := by
  decide +kernel

private theorem check30_10 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 10240 10 = true := by
  decide +kernel

private theorem check30_11 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 11264 10 = true := by
  decide +kernel

private theorem check30_12 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 12288 10 = true := by
  decide +kernel

private theorem check30_13 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 13312 10 = true := by
  decide +kernel

private theorem check30_14 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 14336 10 = true := by
  decide +kernel

private theorem check30_15 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 15360 10 = true := by
  decide +kernel

private theorem check30_16 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 16384 10 = true := by
  decide +kernel

private theorem check30_17 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 17408 10 = true := by
  decide +kernel

private theorem check30_18 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 18432 10 = true := by
  decide +kernel

private theorem check30_19 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 19456 10 = true := by
  decide +kernel

private theorem check30_20 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 20480 10 = true := by
  decide +kernel

private theorem check30_21 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 21504 10 = true := by
  decide +kernel

private theorem check30_22 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 22528 10 = true := by
  decide +kernel

private theorem check30_23 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 23552 10 = true := by
  decide +kernel

private theorem check30_24 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 24576 10 = true := by
  decide +kernel

private theorem check30_25 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 25600 10 = true := by
  decide +kernel

private theorem check30_26 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 26624 10 = true := by
  decide +kernel

private theorem check30_27 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 27648 10 = true := by
  decide +kernel

private theorem check30_28 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 28672 10 = true := by
  decide +kernel

private theorem check30_29 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 29696 10 = true := by
  decide +kernel

private theorem check30_30 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 30720 10 = true := by
  decide +kernel

private theorem check30_31 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 31744 10 = true := by
  decide +kernel

private theorem checked30 : checkPow (mulTest Data.t30 Data.t29 Data.t27) 0 15 = true :=
  (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 14 0 (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 13 0 (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 12 0 (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 11 0 (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 0 check30_0 check30_1) (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 2048 check30_2 check30_3)) (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 11 4096 (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 4096 check30_4 check30_5) (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 6144 check30_6 check30_7))) (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 12 8192 (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 11 8192 (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 8192 check30_8 check30_9) (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 10240 check30_10 check30_11)) (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 11 12288 (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 12288 check30_12 check30_13) (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 14336 check30_14 check30_15)))) (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 13 16384 (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 12 16384 (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 11 16384 (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 16384 check30_16 check30_17) (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 18432 check30_18 check30_19)) (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 11 20480 (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 20480 check30_20 check30_21) (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 22528 check30_22 check30_23))) (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 12 24576 (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 11 24576 (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 24576 check30_24 check30_25) (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 26624 check30_26 check30_27)) (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 11 28672 (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 28672 check30_28 check30_29) (checkPow_join (mulTest Data.t30 Data.t29 Data.t27) 10 30720 check30_30 check30_31)))))

theorem support30 : Supports p30 Data.t30 :=
  mul_support p29 p27 Data.t30 Data.t29 Data.t27
    support29 support27 (checked _ checked30)

private theorem check31_0 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 0 10 = true := by
  decide +kernel

private theorem check31_1 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 1024 10 = true := by
  decide +kernel

private theorem check31_2 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 2048 10 = true := by
  decide +kernel

private theorem check31_3 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 3072 10 = true := by
  decide +kernel

private theorem check31_4 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 4096 10 = true := by
  decide +kernel

private theorem check31_5 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 5120 10 = true := by
  decide +kernel

private theorem check31_6 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 6144 10 = true := by
  decide +kernel

private theorem check31_7 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 7168 10 = true := by
  decide +kernel

private theorem check31_8 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 8192 10 = true := by
  decide +kernel

private theorem check31_9 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 9216 10 = true := by
  decide +kernel

private theorem check31_10 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 10240 10 = true := by
  decide +kernel

private theorem check31_11 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 11264 10 = true := by
  decide +kernel

private theorem check31_12 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 12288 10 = true := by
  decide +kernel

private theorem check31_13 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 13312 10 = true := by
  decide +kernel

private theorem check31_14 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 14336 10 = true := by
  decide +kernel

private theorem check31_15 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 15360 10 = true := by
  decide +kernel

private theorem check31_16 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 16384 10 = true := by
  decide +kernel

private theorem check31_17 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 17408 10 = true := by
  decide +kernel

private theorem check31_18 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 18432 10 = true := by
  decide +kernel

private theorem check31_19 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 19456 10 = true := by
  decide +kernel

private theorem check31_20 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 20480 10 = true := by
  decide +kernel

private theorem check31_21 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 21504 10 = true := by
  decide +kernel

private theorem check31_22 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 22528 10 = true := by
  decide +kernel

private theorem check31_23 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 23552 10 = true := by
  decide +kernel

private theorem check31_24 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 24576 10 = true := by
  decide +kernel

private theorem check31_25 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 25600 10 = true := by
  decide +kernel

private theorem check31_26 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 26624 10 = true := by
  decide +kernel

private theorem check31_27 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 27648 10 = true := by
  decide +kernel

private theorem check31_28 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 28672 10 = true := by
  decide +kernel

private theorem check31_29 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 29696 10 = true := by
  decide +kernel

private theorem check31_30 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 30720 10 = true := by
  decide +kernel

private theorem check31_31 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 31744 10 = true := by
  decide +kernel

private theorem checked31 : checkPow (mulTest Data.t31 Data.t23 Data.t1) 0 15 = true :=
  (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 14 0 (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 13 0 (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 12 0 (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 11 0 (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 0 check31_0 check31_1) (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 2048 check31_2 check31_3)) (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 11 4096 (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 4096 check31_4 check31_5) (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 6144 check31_6 check31_7))) (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 12 8192 (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 11 8192 (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 8192 check31_8 check31_9) (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 10240 check31_10 check31_11)) (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 11 12288 (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 12288 check31_12 check31_13) (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 14336 check31_14 check31_15)))) (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 13 16384 (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 12 16384 (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 11 16384 (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 16384 check31_16 check31_17) (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 18432 check31_18 check31_19)) (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 11 20480 (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 20480 check31_20 check31_21) (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 22528 check31_22 check31_23))) (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 12 24576 (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 11 24576 (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 24576 check31_24 check31_25) (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 26624 check31_26 check31_27)) (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 11 28672 (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 28672 check31_28 check31_29) (checkPow_join (mulTest Data.t31 Data.t23 Data.t1) 10 30720 check31_30 check31_31)))))

theorem support31 : Supports p31 Data.t31 :=
  mul_support p23 p1 Data.t31 Data.t23 Data.t1
    support23 support1 (checked _ checked31)

private theorem check32_0 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 0 10 = true := by
  decide +kernel

private theorem check32_1 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 1024 10 = true := by
  decide +kernel

private theorem check32_2 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 2048 10 = true := by
  decide +kernel

private theorem check32_3 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 3072 10 = true := by
  decide +kernel

private theorem check32_4 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 4096 10 = true := by
  decide +kernel

private theorem check32_5 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 5120 10 = true := by
  decide +kernel

private theorem check32_6 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 6144 10 = true := by
  decide +kernel

private theorem check32_7 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 7168 10 = true := by
  decide +kernel

private theorem check32_8 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 8192 10 = true := by
  decide +kernel

private theorem check32_9 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 9216 10 = true := by
  decide +kernel

private theorem check32_10 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 10240 10 = true := by
  decide +kernel

private theorem check32_11 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 11264 10 = true := by
  decide +kernel

private theorem check32_12 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 12288 10 = true := by
  decide +kernel

private theorem check32_13 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 13312 10 = true := by
  decide +kernel

private theorem check32_14 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 14336 10 = true := by
  decide +kernel

private theorem check32_15 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 15360 10 = true := by
  decide +kernel

private theorem check32_16 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 16384 10 = true := by
  decide +kernel

private theorem check32_17 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 17408 10 = true := by
  decide +kernel

private theorem check32_18 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 18432 10 = true := by
  decide +kernel

private theorem check32_19 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 19456 10 = true := by
  decide +kernel

private theorem check32_20 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 20480 10 = true := by
  decide +kernel

private theorem check32_21 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 21504 10 = true := by
  decide +kernel

private theorem check32_22 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 22528 10 = true := by
  decide +kernel

private theorem check32_23 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 23552 10 = true := by
  decide +kernel

private theorem check32_24 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 24576 10 = true := by
  decide +kernel

private theorem check32_25 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 25600 10 = true := by
  decide +kernel

private theorem check32_26 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 26624 10 = true := by
  decide +kernel

private theorem check32_27 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 27648 10 = true := by
  decide +kernel

private theorem check32_28 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 28672 10 = true := by
  decide +kernel

private theorem check32_29 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 29696 10 = true := by
  decide +kernel

private theorem check32_30 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 30720 10 = true := by
  decide +kernel

private theorem check32_31 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 31744 10 = true := by
  decide +kernel

private theorem checked32 : checkPow (mulTest Data.t32 Data.t31 Data.t28) 0 15 = true :=
  (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 14 0 (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 13 0 (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 12 0 (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 11 0 (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 0 check32_0 check32_1) (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 2048 check32_2 check32_3)) (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 11 4096 (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 4096 check32_4 check32_5) (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 6144 check32_6 check32_7))) (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 12 8192 (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 11 8192 (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 8192 check32_8 check32_9) (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 10240 check32_10 check32_11)) (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 11 12288 (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 12288 check32_12 check32_13) (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 14336 check32_14 check32_15)))) (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 13 16384 (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 12 16384 (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 11 16384 (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 16384 check32_16 check32_17) (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 18432 check32_18 check32_19)) (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 11 20480 (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 20480 check32_20 check32_21) (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 22528 check32_22 check32_23))) (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 12 24576 (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 11 24576 (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 24576 check32_24 check32_25) (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 26624 check32_26 check32_27)) (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 11 28672 (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 28672 check32_28 check32_29) (checkPow_join (mulTest Data.t32 Data.t31 Data.t28) 10 30720 check32_30 check32_31)))))

theorem support32 : Supports p32 Data.t32 :=
  mul_support p31 p28 Data.t32 Data.t31 Data.t28
    support31 support28 (checked _ checked32)

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.OrbitActions
