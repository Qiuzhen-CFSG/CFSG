module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageZero.Data

/-!
# Checked defining edges and base-return separation

The 32 leaves check 1024 rows each. Padding is reduced modulo 31671.
Each row checks a single inverse generator at a single ambient point, avoiding
repeated evaluation of full representative words. These checks assert no
Schreier factorization or faithfulness. Source: the exact packed model, ATLAS
F24G1-p306936B0 and GLS3 Table 5.3v. Reproduce with `source/representatives.py`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageZero
open Certificate

def boundedTreeCheck (j : Nat) : Bool := treeCheck (j % 31671)

private theorem block0 : checkPow boundedTreeCheck 0 10 = true := by
  decide +kernel

private theorem block1 : checkPow boundedTreeCheck 1024 10 = true := by
  decide +kernel

private theorem block2 : checkPow boundedTreeCheck 2048 10 = true := by
  decide +kernel

private theorem block3 : checkPow boundedTreeCheck 3072 10 = true := by
  decide +kernel

private theorem block4 : checkPow boundedTreeCheck 4096 10 = true := by
  decide +kernel

private theorem block5 : checkPow boundedTreeCheck 5120 10 = true := by
  decide +kernel

private theorem block6 : checkPow boundedTreeCheck 6144 10 = true := by
  decide +kernel

private theorem block7 : checkPow boundedTreeCheck 7168 10 = true := by
  decide +kernel

private theorem block8 : checkPow boundedTreeCheck 8192 10 = true := by
  decide +kernel

private theorem block9 : checkPow boundedTreeCheck 9216 10 = true := by
  decide +kernel

private theorem block10 : checkPow boundedTreeCheck 10240 10 = true := by
  decide +kernel

private theorem block11 : checkPow boundedTreeCheck 11264 10 = true := by
  decide +kernel

private theorem block12 : checkPow boundedTreeCheck 12288 10 = true := by
  decide +kernel

private theorem block13 : checkPow boundedTreeCheck 13312 10 = true := by
  decide +kernel

private theorem block14 : checkPow boundedTreeCheck 14336 10 = true := by
  decide +kernel

private theorem block15 : checkPow boundedTreeCheck 15360 10 = true := by
  decide +kernel

private theorem block16 : checkPow boundedTreeCheck 16384 10 = true := by
  decide +kernel

private theorem block17 : checkPow boundedTreeCheck 17408 10 = true := by
  decide +kernel

private theorem block18 : checkPow boundedTreeCheck 18432 10 = true := by
  decide +kernel

private theorem block19 : checkPow boundedTreeCheck 19456 10 = true := by
  decide +kernel

private theorem block20 : checkPow boundedTreeCheck 20480 10 = true := by
  decide +kernel

private theorem block21 : checkPow boundedTreeCheck 21504 10 = true := by
  decide +kernel

private theorem block22 : checkPow boundedTreeCheck 22528 10 = true := by
  decide +kernel

private theorem block23 : checkPow boundedTreeCheck 23552 10 = true := by
  decide +kernel

private theorem block24 : checkPow boundedTreeCheck 24576 10 = true := by
  decide +kernel

private theorem block25 : checkPow boundedTreeCheck 25600 10 = true := by
  decide +kernel

private theorem block26 : checkPow boundedTreeCheck 26624 10 = true := by
  decide +kernel

private theorem block27 : checkPow boundedTreeCheck 27648 10 = true := by
  decide +kernel

private theorem block28 : checkPow boundedTreeCheck 28672 10 = true := by
  decide +kernel

private theorem block29 : checkPow boundedTreeCheck 29696 10 = true := by
  decide +kernel

private theorem block30 : checkPow boundedTreeCheck 30720 10 = true := by
  decide +kernel

private theorem block31 : checkPow boundedTreeCheck 31744 10 = true := by
  decide +kernel

private theorem allBlocks : checkPow boundedTreeCheck 0 15 = true :=
  (checkPow_join boundedTreeCheck 14 0 (checkPow_join boundedTreeCheck 13 0 (checkPow_join boundedTreeCheck 12 0 (checkPow_join boundedTreeCheck 11 0 (checkPow_join boundedTreeCheck 10 0 block0 block1) (checkPow_join boundedTreeCheck 10 2048 block2 block3)) (checkPow_join boundedTreeCheck 11 4096 (checkPow_join boundedTreeCheck 10 4096 block4 block5) (checkPow_join boundedTreeCheck 10 6144 block6 block7))) (checkPow_join boundedTreeCheck 12 8192 (checkPow_join boundedTreeCheck 11 8192 (checkPow_join boundedTreeCheck 10 8192 block8 block9) (checkPow_join boundedTreeCheck 10 10240 block10 block11)) (checkPow_join boundedTreeCheck 11 12288 (checkPow_join boundedTreeCheck 10 12288 block12 block13) (checkPow_join boundedTreeCheck 10 14336 block14 block15)))) (checkPow_join boundedTreeCheck 13 16384 (checkPow_join boundedTreeCheck 12 16384 (checkPow_join boundedTreeCheck 11 16384 (checkPow_join boundedTreeCheck 10 16384 block16 block17) (checkPow_join boundedTreeCheck 10 18432 block18 block19)) (checkPow_join boundedTreeCheck 11 20480 (checkPow_join boundedTreeCheck 10 20480 block20 block21) (checkPow_join boundedTreeCheck 10 22528 block22 block23))) (checkPow_join boundedTreeCheck 12 24576 (checkPow_join boundedTreeCheck 11 24576 (checkPow_join boundedTreeCheck 10 24576 block24 block25) (checkPow_join boundedTreeCheck 10 26624 block26 block27)) (checkPow_join boundedTreeCheck 11 28672 (checkPow_join boundedTreeCheck 10 28672 block28 block29) (checkPow_join boundedTreeCheck 10 30720 block30 block31)))))

/-- Every actual row passes the defining-edge and separation check. -/
theorem treeCheck_eq_true (j : Nat) (hj : j < 31671) : treeCheck j = true := by
  have h := checkPow_sound boundedTreeCheck 15 0 allBlocks j (Nat.zero_le _) (by omega)
  simpa only [boundedTreeCheck, Nat.mod_eq_of_lt hj] using h

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageZero
