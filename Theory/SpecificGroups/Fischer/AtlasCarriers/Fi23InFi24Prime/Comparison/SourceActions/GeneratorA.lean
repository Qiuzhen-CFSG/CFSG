module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.SourceActions.Checker
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.FixedLetters.DisjointA

/-!
# Exact packed action of Fi23 generator A

Each cycle check reads one original decoded block (at most 256 cycles).
The complement checks cover all 31671 letters in 32 blocks of 1024; padding
wraps modulo 31671. Existing certificates supply exact decoding, disjointness
and support. All new Boolean checks use kernel reduction.

Source: ATLAS F23G1-p31671B0.g1; attribution and hashes are retained in
`AtlasCarriers/source/`. This discharges a source-action premise of the Fi23
comparison used for GLS3 Table 5.3v. Reproduce with `source/generate.py`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.SourceActionCheck
open Fi23.CentralizerSection.KernelCertificate
open Fi23.CentralizerSection.KernelCertificate.FixedLetterCheck

private theorem blockA0 : cycleTest sourceA cyclesA0 = true :=
  by decide +kernel

private theorem blockA1 : cycleTest sourceA cyclesA1 = true :=
  by decide +kernel

private theorem blockA2 : cycleTest sourceA cyclesA2 = true :=
  by decide +kernel

private theorem blockA3 : cycleTest sourceA cyclesA3 = true :=
  by decide +kernel

private theorem blockA4 : cycleTest sourceA cyclesA4 = true :=
  by decide +kernel

private theorem blockA5 : cycleTest sourceA cyclesA5 = true :=
  by decide +kernel

private theorem blockA6 : cycleTest sourceA cyclesA6 = true :=
  by decide +kernel

private theorem blockA7 : cycleTest sourceA cyclesA7 = true :=
  by decide +kernel

private theorem blockA8 : cycleTest sourceA cyclesA8 = true :=
  by decide +kernel

private theorem blockA9 : cycleTest sourceA cyclesA9 = true :=
  by decide +kernel

private theorem blockA10 : cycleTest sourceA cyclesA10 = true :=
  by decide +kernel

private theorem blockA11 : cycleTest sourceA cyclesA11 = true :=
  by decide +kernel

private theorem blockA12 : cycleTest sourceA cyclesA12 = true :=
  by decide +kernel

private theorem blockA13 : cycleTest sourceA cyclesA13 = true :=
  by decide +kernel

private theorem blockA14 : cycleTest sourceA cyclesA14 = true :=
  by decide +kernel

private theorem blockA15 : cycleTest sourceA cyclesA15 = true :=
  by decide +kernel

private theorem blockA16 : cycleTest sourceA cyclesA16 = true :=
  by decide +kernel

private theorem blockA17 : cycleTest sourceA cyclesA17 = true :=
  by decide +kernel

private theorem blockA18 : cycleTest sourceA cyclesA18 = true :=
  by decide +kernel

private theorem blockA19 : cycleTest sourceA cyclesA19 = true :=
  by decide +kernel

private theorem blockA20 : cycleTest sourceA cyclesA20 = true :=
  by decide +kernel

private theorem blockA21 : cycleTest sourceA cyclesA21 = true :=
  by decide +kernel

private theorem blockA22 : cycleTest sourceA cyclesA22 = true :=
  by decide +kernel

private theorem blockA23 : cycleTest sourceA cyclesA23 = true :=
  by decide +kernel

private theorem blockA24 : cycleTest sourceA cyclesA24 = true :=
  by decide +kernel

private theorem blockA25 : cycleTest sourceA cyclesA25 = true :=
  by decide +kernel

private theorem blockA26 : cycleTest sourceA cyclesA26 = true :=
  by decide +kernel

private theorem blockA27 : cycleTest sourceA cyclesA27 = true :=
  by decide +kernel

private theorem blockA28 : cycleTest sourceA cyclesA28 = true :=
  by decide +kernel

private theorem blockA29 : cycleTest sourceA cyclesA29 = true :=
  by decide +kernel

private theorem blockA30 : cycleTest sourceA cyclesA30 = true :=
  by decide +kernel

private theorem blockA31 : cycleTest sourceA cyclesA31 = true :=
  by decide +kernel

private theorem blockA32 : cycleTest sourceA cyclesA32 = true :=
  by decide +kernel

private theorem blockA33 : cycleTest sourceA cyclesA33 = true :=
  by decide +kernel

private theorem blockA34 : cycleTest sourceA cyclesA34 = true :=
  by decide +kernel

private theorem blockA35 : cycleTest sourceA cyclesA35 = true :=
  by decide +kernel

private theorem blockA36 : cycleTest sourceA cyclesA36 = true :=
  by decide +kernel

private theorem blockA37 : cycleTest sourceA cyclesA37 = true :=
  by decide +kernel

private theorem blockA38 : cycleTest sourceA cyclesA38 = true :=
  by decide +kernel

private theorem blockA39 : cycleTest sourceA cyclesA39 = true :=
  by decide +kernel

private theorem blockA40 : cycleTest sourceA cyclesA40 = true :=
  by decide +kernel

private theorem blockA41 : cycleTest sourceA cyclesA41 = true :=
  by decide +kernel

private theorem blockA42 : cycleTest sourceA cyclesA42 = true :=
  by decide +kernel

private theorem blockA43 : cycleTest sourceA cyclesA43 = true :=
  by decide +kernel

private theorem blockA44 : cycleTest sourceA cyclesA44 = true :=
  by decide +kernel

private theorem blockA45 : cycleTest sourceA cyclesA45 = true :=
  by decide +kernel

private theorem blockA46 : cycleTest sourceA cyclesA46 = true :=
  by decide +kernel

private theorem blockA47 : cycleTest sourceA cyclesA47 = true :=
  by decide +kernel

private theorem blockA48 : cycleTest sourceA cyclesA48 = true :=
  by decide +kernel

private theorem blockA49 : cycleTest sourceA cyclesA49 = true :=
  by decide +kernel

private theorem blockA50 : cycleTest sourceA cyclesA50 = true :=
  by decide +kernel

private theorem blockA51 : cycleTest sourceA cyclesA51 = true :=
  by decide +kernel

private theorem blockA52 : cycleTest sourceA cyclesA52 = true :=
  by decide +kernel

private theorem blockA53 : cycleTest sourceA cyclesA53 = true :=
  by decide +kernel

private theorem blockA54 : cycleTest sourceA cyclesA54 = true :=
  by decide +kernel

private theorem blockA55 : cycleTest sourceA cyclesA55 = true :=
  by decide +kernel

private theorem blockA56 : cycleTest sourceA cyclesA56 = true :=
  by decide +kernel

private theorem blockA57 : cycleTest sourceA cyclesA57 = true :=
  by decide +kernel

private theorem blockA58 : cycleTest sourceA cyclesA58 = true :=
  by decide +kernel

private theorem blockA59 : cycleTest sourceA cyclesA59 = true :=
  by decide +kernel

private theorem blockA60 : cycleTest sourceA cyclesA60 = true :=
  by decide +kernel

theorem sourceA_cycle_actions :
    ∀ c ∈ cyclesA, ∀ x ∈ c, cycleInv c x = sourceA x := by
  apply blockTests_sound sourceA [cyclesA0, cyclesA1, cyclesA2, cyclesA3, cyclesA4, cyclesA5, cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60]
  simp only [List.all_cons, List.all_nil, blockA0,
    blockA1,
    blockA2,
    blockA3,
    blockA4,
    blockA5,
    blockA6,
    blockA7,
    blockA8,
    blockA9,
    blockA10,
    blockA11,
    blockA12,
    blockA13,
    blockA14,
    blockA15,
    blockA16,
    blockA17,
    blockA18,
    blockA19,
    blockA20,
    blockA21,
    blockA22,
    blockA23,
    blockA24,
    blockA25,
    blockA26,
    blockA27,
    blockA28,
    blockA29,
    blockA30,
    blockA31,
    blockA32,
    blockA33,
    blockA34,
    blockA35,
    blockA36,
    blockA37,
    blockA38,
    blockA39,
    blockA40,
    blockA41,
    blockA42,
    blockA43,
    blockA44,
    blockA45,
    blockA46,
    blockA47,
    blockA48,
    blockA49,
    blockA50,
    blockA51,
    blockA52,
    blockA53,
    blockA54,
    blockA55,
    blockA56,
    blockA57,
    blockA58,
    blockA59,
    blockA60, Bool.and_self]

private theorem fixedA0 :
    checkPow (fixedTest sourceA maskA) 0 10 = true :=
  by decide +kernel

private theorem fixedA1 :
    checkPow (fixedTest sourceA maskA) 1024 10 = true :=
  by decide +kernel

private theorem fixedA2 :
    checkPow (fixedTest sourceA maskA) 2048 10 = true :=
  by decide +kernel

private theorem fixedA3 :
    checkPow (fixedTest sourceA maskA) 3072 10 = true :=
  by decide +kernel

private theorem fixedA4 :
    checkPow (fixedTest sourceA maskA) 4096 10 = true :=
  by decide +kernel

private theorem fixedA5 :
    checkPow (fixedTest sourceA maskA) 5120 10 = true :=
  by decide +kernel

private theorem fixedA6 :
    checkPow (fixedTest sourceA maskA) 6144 10 = true :=
  by decide +kernel

private theorem fixedA7 :
    checkPow (fixedTest sourceA maskA) 7168 10 = true :=
  by decide +kernel

private theorem fixedA8 :
    checkPow (fixedTest sourceA maskA) 8192 10 = true :=
  by decide +kernel

private theorem fixedA9 :
    checkPow (fixedTest sourceA maskA) 9216 10 = true :=
  by decide +kernel

private theorem fixedA10 :
    checkPow (fixedTest sourceA maskA) 10240 10 = true :=
  by decide +kernel

private theorem fixedA11 :
    checkPow (fixedTest sourceA maskA) 11264 10 = true :=
  by decide +kernel

private theorem fixedA12 :
    checkPow (fixedTest sourceA maskA) 12288 10 = true :=
  by decide +kernel

private theorem fixedA13 :
    checkPow (fixedTest sourceA maskA) 13312 10 = true :=
  by decide +kernel

private theorem fixedA14 :
    checkPow (fixedTest sourceA maskA) 14336 10 = true :=
  by decide +kernel

private theorem fixedA15 :
    checkPow (fixedTest sourceA maskA) 15360 10 = true :=
  by decide +kernel

private theorem fixedA16 :
    checkPow (fixedTest sourceA maskA) 16384 10 = true :=
  by decide +kernel

private theorem fixedA17 :
    checkPow (fixedTest sourceA maskA) 17408 10 = true :=
  by decide +kernel

private theorem fixedA18 :
    checkPow (fixedTest sourceA maskA) 18432 10 = true :=
  by decide +kernel

private theorem fixedA19 :
    checkPow (fixedTest sourceA maskA) 19456 10 = true :=
  by decide +kernel

private theorem fixedA20 :
    checkPow (fixedTest sourceA maskA) 20480 10 = true :=
  by decide +kernel

private theorem fixedA21 :
    checkPow (fixedTest sourceA maskA) 21504 10 = true :=
  by decide +kernel

private theorem fixedA22 :
    checkPow (fixedTest sourceA maskA) 22528 10 = true :=
  by decide +kernel

private theorem fixedA23 :
    checkPow (fixedTest sourceA maskA) 23552 10 = true :=
  by decide +kernel

private theorem fixedA24 :
    checkPow (fixedTest sourceA maskA) 24576 10 = true :=
  by decide +kernel

private theorem fixedA25 :
    checkPow (fixedTest sourceA maskA) 25600 10 = true :=
  by decide +kernel

private theorem fixedA26 :
    checkPow (fixedTest sourceA maskA) 26624 10 = true :=
  by decide +kernel

private theorem fixedA27 :
    checkPow (fixedTest sourceA maskA) 27648 10 = true :=
  by decide +kernel

private theorem fixedA28 :
    checkPow (fixedTest sourceA maskA) 28672 10 = true :=
  by decide +kernel

private theorem fixedA29 :
    checkPow (fixedTest sourceA maskA) 29696 10 = true :=
  by decide +kernel

private theorem fixedA30 :
    checkPow (fixedTest sourceA maskA) 30720 10 = true :=
  by decide +kernel

private theorem fixedA31 :
    checkPow (fixedTest sourceA maskA) 31744 10 = true :=
  by decide +kernel

theorem sourceA_fixed_complement :
    ∀ x : Fin 31671, maskA.testBit x.val = false → sourceA x = x := by
  apply fixedTest_sound
  exact (checkPow_join (fixedTest sourceA maskA) 14 0
    (checkPow_join (fixedTest sourceA maskA) 13 0
    (checkPow_join (fixedTest sourceA maskA) 12 0
    (checkPow_join (fixedTest sourceA maskA) 11 0
    (checkPow_join (fixedTest sourceA maskA) 10 0
    fixedA0
    fixedA1)
    (checkPow_join (fixedTest sourceA maskA) 10 2048
    fixedA2
    fixedA3))
    (checkPow_join (fixedTest sourceA maskA) 11 4096
    (checkPow_join (fixedTest sourceA maskA) 10 4096
    fixedA4
    fixedA5)
    (checkPow_join (fixedTest sourceA maskA) 10 6144
    fixedA6
    fixedA7)))
    (checkPow_join (fixedTest sourceA maskA) 12 8192
    (checkPow_join (fixedTest sourceA maskA) 11 8192
    (checkPow_join (fixedTest sourceA maskA) 10 8192
    fixedA8
    fixedA9)
    (checkPow_join (fixedTest sourceA maskA) 10 10240
    fixedA10
    fixedA11))
    (checkPow_join (fixedTest sourceA maskA) 11 12288
    (checkPow_join (fixedTest sourceA maskA) 10 12288
    fixedA12
    fixedA13)
    (checkPow_join (fixedTest sourceA maskA) 10 14336
    fixedA14
    fixedA15))))
    (checkPow_join (fixedTest sourceA maskA) 13 16384
    (checkPow_join (fixedTest sourceA maskA) 12 16384
    (checkPow_join (fixedTest sourceA maskA) 11 16384
    (checkPow_join (fixedTest sourceA maskA) 10 16384
    fixedA16
    fixedA17)
    (checkPow_join (fixedTest sourceA maskA) 10 18432
    fixedA18
    fixedA19))
    (checkPow_join (fixedTest sourceA maskA) 11 20480
    (checkPow_join (fixedTest sourceA maskA) 10 20480
    fixedA20
    fixedA21)
    (checkPow_join (fixedTest sourceA maskA) 10 22528
    fixedA22
    fixedA23)))
    (checkPow_join (fixedTest sourceA maskA) 12 24576
    (checkPow_join (fixedTest sourceA maskA) 11 24576
    (checkPow_join (fixedTest sourceA maskA) 10 24576
    fixedA24
    fixedA25)
    (checkPow_join (fixedTest sourceA maskA) 10 26624
    fixedA26
    fixedA27))
    (checkPow_join (fixedTest sourceA maskA) 11 28672
    (checkPow_join (fixedTest sourceA maskA) 10 28672
    fixedA28
    fixedA29)
    (checkPow_join (fixedTest sourceA maskA) 10 30720
    fixedA30
    fixedA31)))))

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.SourceActionCheck
