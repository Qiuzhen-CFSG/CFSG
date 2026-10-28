module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Data

/-!
# Checked coverage and paths for the Fi23 fixed-point loops

The finite checks establish coverage for every actual fixed letter and identify
the recorded paths with the original tree. They do not check the action of a
subgroup word on a loop; that independent obligation is `ActionCheck`.

Source: retained ATLAS F23G1-p31671B0 and GLS3 Table 5.3u.
-/

set_option Elab.async false

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

private theorem path0 : checkPow pathTest 0 7 = true := by decide +kernel

private theorem path1 : checkPow pathTest 128 7 = true := by decide +kernel

private theorem path2 : checkPow pathTest 256 7 = true := by decide +kernel

private theorem path3 : checkPow pathTest 384 7 = true := by decide +kernel

private theorem path4 : checkPow pathTest 512 7 = true := by decide +kernel

private theorem path5 : checkPow pathTest 640 7 = true := by decide +kernel

private theorem path6 : checkPow pathTest 768 7 = true := by decide +kernel

private theorem path7 : checkPow pathTest 896 7 = true := by decide +kernel

private theorem pathChecked : checkPow pathTest 0 10 = true :=
  (checkPow_join pathTest 9 0 (checkPow_join pathTest 8 0 (checkPow_join pathTest 7 0 path0 path1) (checkPow_join pathTest 7 256 path2 path3)) (checkPow_join pathTest 8 512 (checkPow_join pathTest 7 512 path4 path5) (checkPow_join pathTest 7 768 path6 path7)))

private theorem coverage0 : checkPow coverageTest 0 10 = true := by decide +kernel

private theorem coverage1 : checkPow coverageTest 1024 10 = true := by decide +kernel

private theorem coverage2 : checkPow coverageTest 2048 10 = true := by decide +kernel

private theorem coverage3 : checkPow coverageTest 3072 10 = true := by decide +kernel

private theorem coverage4 : checkPow coverageTest 4096 10 = true := by decide +kernel

private theorem coverage5 : checkPow coverageTest 5120 10 = true := by decide +kernel

private theorem coverage6 : checkPow coverageTest 6144 10 = true := by decide +kernel

private theorem coverage7 : checkPow coverageTest 7168 10 = true := by decide +kernel

private theorem coverage8 : checkPow coverageTest 8192 10 = true := by decide +kernel

private theorem coverage9 : checkPow coverageTest 9216 10 = true := by decide +kernel

private theorem coverage10 : checkPow coverageTest 10240 10 = true := by decide +kernel

private theorem coverage11 : checkPow coverageTest 11264 10 = true := by decide +kernel

private theorem coverage12 : checkPow coverageTest 12288 10 = true := by decide +kernel

private theorem coverage13 : checkPow coverageTest 13312 10 = true := by decide +kernel

private theorem coverage14 : checkPow coverageTest 14336 10 = true := by decide +kernel

private theorem coverage15 : checkPow coverageTest 15360 10 = true := by decide +kernel

private theorem coverage16 : checkPow coverageTest 16384 10 = true := by decide +kernel

private theorem coverage17 : checkPow coverageTest 17408 10 = true := by decide +kernel

private theorem coverage18 : checkPow coverageTest 18432 10 = true := by decide +kernel

private theorem coverage19 : checkPow coverageTest 19456 10 = true := by decide +kernel

private theorem coverage20 : checkPow coverageTest 20480 10 = true := by decide +kernel

private theorem coverage21 : checkPow coverageTest 21504 10 = true := by decide +kernel

private theorem coverage22 : checkPow coverageTest 22528 10 = true := by decide +kernel

private theorem coverage23 : checkPow coverageTest 23552 10 = true := by decide +kernel

private theorem coverage24 : checkPow coverageTest 24576 10 = true := by decide +kernel

private theorem coverage25 : checkPow coverageTest 25600 10 = true := by decide +kernel

private theorem coverage26 : checkPow coverageTest 26624 10 = true := by decide +kernel

private theorem coverage27 : checkPow coverageTest 27648 10 = true := by decide +kernel

private theorem coverage28 : checkPow coverageTest 28672 10 = true := by decide +kernel

private theorem coverage29 : checkPow coverageTest 29696 10 = true := by decide +kernel

private theorem coverage30 : checkPow coverageTest 30720 10 = true := by decide +kernel

private theorem coverage31 : checkPow coverageTest 31744 10 = true := by decide +kernel

private theorem coverageChecked : checkPow coverageTest 0 15 = true :=
  (checkPow_join coverageTest 14 0 (checkPow_join coverageTest 13 0 (checkPow_join coverageTest 12 0 (checkPow_join coverageTest 11 0 (checkPow_join coverageTest 10 0 coverage0 coverage1) (checkPow_join coverageTest 10 2048 coverage2 coverage3)) (checkPow_join coverageTest 11 4096 (checkPow_join coverageTest 10 4096 coverage4 coverage5) (checkPow_join coverageTest 10 6144 coverage6 coverage7))) (checkPow_join coverageTest 12 8192 (checkPow_join coverageTest 11 8192 (checkPow_join coverageTest 10 8192 coverage8 coverage9) (checkPow_join coverageTest 10 10240 coverage10 coverage11)) (checkPow_join coverageTest 11 12288 (checkPow_join coverageTest 10 12288 coverage12 coverage13) (checkPow_join coverageTest 10 14336 coverage14 coverage15)))) (checkPow_join coverageTest 13 16384 (checkPow_join coverageTest 12 16384 (checkPow_join coverageTest 11 16384 (checkPow_join coverageTest 10 16384 coverage16 coverage17) (checkPow_join coverageTest 10 18432 coverage18 coverage19)) (checkPow_join coverageTest 11 20480 (checkPow_join coverageTest 10 20480 coverage20 coverage21) (checkPow_join coverageTest 10 22528 coverage22 coverage23))) (checkPow_join coverageTest 12 24576 (checkPow_join coverageTest 11 24576 (checkPow_join coverageTest 10 24576 coverage24 coverage25) (checkPow_join coverageTest 10 26624 coverage26 coverage27)) (checkPow_join coverageTest 11 28672 (checkPow_join coverageTest 10 28672 coverage28 coverage29) (checkPow_join coverageTest 10 30720 coverage30 coverage31)))))

theorem path_properties (i : Fin 722) :
    pathOK (pathLength i) (pathBits i) (loopPoint i) = true ∧
      sourceGenerator i (loopPoint i) = loopPoint i := by
  have h := checkPow_sound pathTest 10 0 pathChecked i.val (Nat.zero_le _)
    (Nat.lt_trans i.isLt (by decide))
  have hi : Fin.ofNat 722 i.val = i := by simp
  simpa only [pathTest, hi, Bool.and_eq_true, decide_eq_true_eq] using h

theorem coverage (x : Fin 31671) :
    (sourceA x = x → (loopIndex x).val < 695 ∧ loopPoint (loopIndex x) = x) ∧
    (sourceB x = x → 695 ≤ (loopIndex x).val ∧ loopPoint (loopIndex x) = x) := by
  have h := checkPow_sound coverageTest 15 0 coverageChecked x.val (Nat.zero_le _)
    (Nat.lt_trans x.isLt (by decide))
  have hx : Fin.ofNat 31671 x.val = x := by simp
  simpa only [coverageTest, hx, decide_eq_true_eq] using h

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops
