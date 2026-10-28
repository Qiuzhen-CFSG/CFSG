module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.RelationTests

/-!
# The Fi23 suffix generators 4 and 5 commute

Each of the 32 blocks checks 1024 inputs by kernel reduction. Joining
these proofs covers 32768 inputs; `Fin.ofNat 31671` covers every letter.
Only the block proofs reduce the tables. Assembly uses `checkPow_join`.

Source application: GLS3 Table 5.3u; ATLAS F23G1-p31671B0.
Reproduce with `KernelLower/Relations/source/Generate.py`.
-/

-- Check blocks sequentially so their reduction caches can be released.
set_option Elab.async false

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerData.Relations.Commute45
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

private theorem block0 : checkPow (commutationTest 4 5) 0 10 = true := by
  decide +kernel

private theorem block1 : checkPow (commutationTest 4 5) 1024 10 = true := by
  decide +kernel

private theorem block2 : checkPow (commutationTest 4 5) 2048 10 = true := by
  decide +kernel

private theorem block3 : checkPow (commutationTest 4 5) 3072 10 = true := by
  decide +kernel

private theorem block4 : checkPow (commutationTest 4 5) 4096 10 = true := by
  decide +kernel

private theorem block5 : checkPow (commutationTest 4 5) 5120 10 = true := by
  decide +kernel

private theorem block6 : checkPow (commutationTest 4 5) 6144 10 = true := by
  decide +kernel

private theorem block7 : checkPow (commutationTest 4 5) 7168 10 = true := by
  decide +kernel

private theorem block8 : checkPow (commutationTest 4 5) 8192 10 = true := by
  decide +kernel

private theorem block9 : checkPow (commutationTest 4 5) 9216 10 = true := by
  decide +kernel

private theorem block10 : checkPow (commutationTest 4 5) 10240 10 = true := by
  decide +kernel

private theorem block11 : checkPow (commutationTest 4 5) 11264 10 = true := by
  decide +kernel

private theorem block12 : checkPow (commutationTest 4 5) 12288 10 = true := by
  decide +kernel

private theorem block13 : checkPow (commutationTest 4 5) 13312 10 = true := by
  decide +kernel

private theorem block14 : checkPow (commutationTest 4 5) 14336 10 = true := by
  decide +kernel

private theorem block15 : checkPow (commutationTest 4 5) 15360 10 = true := by
  decide +kernel

private theorem block16 : checkPow (commutationTest 4 5) 16384 10 = true := by
  decide +kernel

private theorem block17 : checkPow (commutationTest 4 5) 17408 10 = true := by
  decide +kernel

private theorem block18 : checkPow (commutationTest 4 5) 18432 10 = true := by
  decide +kernel

private theorem block19 : checkPow (commutationTest 4 5) 19456 10 = true := by
  decide +kernel

private theorem block20 : checkPow (commutationTest 4 5) 20480 10 = true := by
  decide +kernel

private theorem block21 : checkPow (commutationTest 4 5) 21504 10 = true := by
  decide +kernel

private theorem block22 : checkPow (commutationTest 4 5) 22528 10 = true := by
  decide +kernel

private theorem block23 : checkPow (commutationTest 4 5) 23552 10 = true := by
  decide +kernel

private theorem block24 : checkPow (commutationTest 4 5) 24576 10 = true := by
  decide +kernel

private theorem block25 : checkPow (commutationTest 4 5) 25600 10 = true := by
  decide +kernel

private theorem block26 : checkPow (commutationTest 4 5) 26624 10 = true := by
  decide +kernel

private theorem block27 : checkPow (commutationTest 4 5) 27648 10 = true := by
  decide +kernel

private theorem block28 : checkPow (commutationTest 4 5) 28672 10 = true := by
  decide +kernel

private theorem block29 : checkPow (commutationTest 4 5) 29696 10 = true := by
  decide +kernel

private theorem block30 : checkPow (commutationTest 4 5) 30720 10 = true := by
  decide +kernel

private theorem block31 : checkPow (commutationTest 4 5) 31744 10 = true := by
  decide +kernel

private theorem joined11_0 : checkPow (commutationTest 4 5) 0 11 = true :=
  checkPow_join (commutationTest 4 5) 10 0 block0 block1

private theorem joined11_1 : checkPow (commutationTest 4 5) 2048 11 = true :=
  checkPow_join (commutationTest 4 5) 10 2048 block2 block3

private theorem joined11_2 : checkPow (commutationTest 4 5) 4096 11 = true :=
  checkPow_join (commutationTest 4 5) 10 4096 block4 block5

private theorem joined11_3 : checkPow (commutationTest 4 5) 6144 11 = true :=
  checkPow_join (commutationTest 4 5) 10 6144 block6 block7

private theorem joined11_4 : checkPow (commutationTest 4 5) 8192 11 = true :=
  checkPow_join (commutationTest 4 5) 10 8192 block8 block9

private theorem joined11_5 : checkPow (commutationTest 4 5) 10240 11 = true :=
  checkPow_join (commutationTest 4 5) 10 10240 block10 block11

private theorem joined11_6 : checkPow (commutationTest 4 5) 12288 11 = true :=
  checkPow_join (commutationTest 4 5) 10 12288 block12 block13

private theorem joined11_7 : checkPow (commutationTest 4 5) 14336 11 = true :=
  checkPow_join (commutationTest 4 5) 10 14336 block14 block15

private theorem joined11_8 : checkPow (commutationTest 4 5) 16384 11 = true :=
  checkPow_join (commutationTest 4 5) 10 16384 block16 block17

private theorem joined11_9 : checkPow (commutationTest 4 5) 18432 11 = true :=
  checkPow_join (commutationTest 4 5) 10 18432 block18 block19

private theorem joined11_10 : checkPow (commutationTest 4 5) 20480 11 = true :=
  checkPow_join (commutationTest 4 5) 10 20480 block20 block21

private theorem joined11_11 : checkPow (commutationTest 4 5) 22528 11 = true :=
  checkPow_join (commutationTest 4 5) 10 22528 block22 block23

private theorem joined11_12 : checkPow (commutationTest 4 5) 24576 11 = true :=
  checkPow_join (commutationTest 4 5) 10 24576 block24 block25

private theorem joined11_13 : checkPow (commutationTest 4 5) 26624 11 = true :=
  checkPow_join (commutationTest 4 5) 10 26624 block26 block27

private theorem joined11_14 : checkPow (commutationTest 4 5) 28672 11 = true :=
  checkPow_join (commutationTest 4 5) 10 28672 block28 block29

private theorem joined11_15 : checkPow (commutationTest 4 5) 30720 11 = true :=
  checkPow_join (commutationTest 4 5) 10 30720 block30 block31

private theorem joined12_0 : checkPow (commutationTest 4 5) 0 12 = true :=
  checkPow_join (commutationTest 4 5) 11 0 joined11_0 joined11_1

private theorem joined12_1 : checkPow (commutationTest 4 5) 4096 12 = true :=
  checkPow_join (commutationTest 4 5) 11 4096 joined11_2 joined11_3

private theorem joined12_2 : checkPow (commutationTest 4 5) 8192 12 = true :=
  checkPow_join (commutationTest 4 5) 11 8192 joined11_4 joined11_5

private theorem joined12_3 : checkPow (commutationTest 4 5) 12288 12 = true :=
  checkPow_join (commutationTest 4 5) 11 12288 joined11_6 joined11_7

private theorem joined12_4 : checkPow (commutationTest 4 5) 16384 12 = true :=
  checkPow_join (commutationTest 4 5) 11 16384 joined11_8 joined11_9

private theorem joined12_5 : checkPow (commutationTest 4 5) 20480 12 = true :=
  checkPow_join (commutationTest 4 5) 11 20480 joined11_10 joined11_11

private theorem joined12_6 : checkPow (commutationTest 4 5) 24576 12 = true :=
  checkPow_join (commutationTest 4 5) 11 24576 joined11_12 joined11_13

private theorem joined12_7 : checkPow (commutationTest 4 5) 28672 12 = true :=
  checkPow_join (commutationTest 4 5) 11 28672 joined11_14 joined11_15

private theorem joined13_0 : checkPow (commutationTest 4 5) 0 13 = true :=
  checkPow_join (commutationTest 4 5) 12 0 joined12_0 joined12_1

private theorem joined13_1 : checkPow (commutationTest 4 5) 8192 13 = true :=
  checkPow_join (commutationTest 4 5) 12 8192 joined12_2 joined12_3

private theorem joined13_2 : checkPow (commutationTest 4 5) 16384 13 = true :=
  checkPow_join (commutationTest 4 5) 12 16384 joined12_4 joined12_5

private theorem joined13_3 : checkPow (commutationTest 4 5) 24576 13 = true :=
  checkPow_join (commutationTest 4 5) 12 24576 joined12_6 joined12_7

private theorem joined14_0 : checkPow (commutationTest 4 5) 0 14 = true :=
  checkPow_join (commutationTest 4 5) 13 0 joined13_0 joined13_1

private theorem joined14_1 : checkPow (commutationTest 4 5) 16384 14 = true :=
  checkPow_join (commutationTest 4 5) 13 16384 joined13_2 joined13_3

/-- The complete numerical certificate, including all 31671 letters. -/
theorem checked : checkPow (commutationTest 4 5) 0 15 = true :=
  checkPow_join (commutationTest 4 5) 14 0 joined14_0 joined14_1

end Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerData.Relations.Commute45
