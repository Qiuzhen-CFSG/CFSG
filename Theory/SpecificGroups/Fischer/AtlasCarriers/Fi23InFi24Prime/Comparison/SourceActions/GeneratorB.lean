module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.SourceActions.Checker
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.FixedLetters.DisjointB

/-!
# Exact packed action of Fi23 generator B

Each cycle check reads one original decoded block (at most 256 cycles).
The complement checks cover all 31671 letters in 32 blocks of 1024; padding
wraps modulo 31671. Existing certificates supply exact decoding, disjointness
and support. All new Boolean checks use kernel reduction.

Source: ATLAS F23G1-p31671B0.g2; attribution and hashes are retained in
`AtlasCarriers/source/`. This discharges a source-action premise of the Fi23
comparison used for GLS3 Table 5.3v. Reproduce with `source/generate.py`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.SourceActionCheck
open Fi23.CentralizerSection.KernelCertificate
open Fi23.CentralizerSection.KernelCertificate.FixedLetterCheck

private theorem blockB0 : cycleTest sourceB cyclesB0 = true :=
  by decide +kernel

private theorem blockB1 : cycleTest sourceB cyclesB1 = true :=
  by decide +kernel

private theorem blockB2 : cycleTest sourceB cyclesB2 = true :=
  by decide +kernel

private theorem blockB3 : cycleTest sourceB cyclesB3 = true :=
  by decide +kernel

private theorem blockB4 : cycleTest sourceB cyclesB4 = true :=
  by decide +kernel

private theorem blockB5 : cycleTest sourceB cyclesB5 = true :=
  by decide +kernel

private theorem blockB6 : cycleTest sourceB cyclesB6 = true :=
  by decide +kernel

private theorem blockB7 : cycleTest sourceB cyclesB7 = true :=
  by decide +kernel

private theorem blockB8 : cycleTest sourceB cyclesB8 = true :=
  by decide +kernel

private theorem blockB9 : cycleTest sourceB cyclesB9 = true :=
  by decide +kernel

private theorem blockB10 : cycleTest sourceB cyclesB10 = true :=
  by decide +kernel

private theorem blockB11 : cycleTest sourceB cyclesB11 = true :=
  by decide +kernel

private theorem blockB12 : cycleTest sourceB cyclesB12 = true :=
  by decide +kernel

private theorem blockB13 : cycleTest sourceB cyclesB13 = true :=
  by decide +kernel

private theorem blockB14 : cycleTest sourceB cyclesB14 = true :=
  by decide +kernel

private theorem blockB15 : cycleTest sourceB cyclesB15 = true :=
  by decide +kernel

private theorem blockB16 : cycleTest sourceB cyclesB16 = true :=
  by decide +kernel

private theorem blockB17 : cycleTest sourceB cyclesB17 = true :=
  by decide +kernel

private theorem blockB18 : cycleTest sourceB cyclesB18 = true :=
  by decide +kernel

private theorem blockB19 : cycleTest sourceB cyclesB19 = true :=
  by decide +kernel

private theorem blockB20 : cycleTest sourceB cyclesB20 = true :=
  by decide +kernel

private theorem blockB21 : cycleTest sourceB cyclesB21 = true :=
  by decide +kernel

private theorem blockB22 : cycleTest sourceB cyclesB22 = true :=
  by decide +kernel

private theorem blockB23 : cycleTest sourceB cyclesB23 = true :=
  by decide +kernel

private theorem blockB24 : cycleTest sourceB cyclesB24 = true :=
  by decide +kernel

private theorem blockB25 : cycleTest sourceB cyclesB25 = true :=
  by decide +kernel

private theorem blockB26 : cycleTest sourceB cyclesB26 = true :=
  by decide +kernel

private theorem blockB27 : cycleTest sourceB cyclesB27 = true :=
  by decide +kernel

private theorem blockB28 : cycleTest sourceB cyclesB28 = true :=
  by decide +kernel

private theorem blockB29 : cycleTest sourceB cyclesB29 = true :=
  by decide +kernel

private theorem blockB30 : cycleTest sourceB cyclesB30 = true :=
  by decide +kernel

private theorem blockB31 : cycleTest sourceB cyclesB31 = true :=
  by decide +kernel

private theorem blockB32 : cycleTest sourceB cyclesB32 = true :=
  by decide +kernel

private theorem blockB33 : cycleTest sourceB cyclesB33 = true :=
  by decide +kernel

private theorem blockB34 : cycleTest sourceB cyclesB34 = true :=
  by decide +kernel

private theorem blockB35 : cycleTest sourceB cyclesB35 = true :=
  by decide +kernel

private theorem blockB36 : cycleTest sourceB cyclesB36 = true :=
  by decide +kernel

private theorem blockB37 : cycleTest sourceB cyclesB37 = true :=
  by decide +kernel

private theorem blockB38 : cycleTest sourceB cyclesB38 = true :=
  by decide +kernel

private theorem blockB39 : cycleTest sourceB cyclesB39 = true :=
  by decide +kernel

private theorem blockB40 : cycleTest sourceB cyclesB40 = true :=
  by decide +kernel

private theorem blockB41 : cycleTest sourceB cyclesB41 = true :=
  by decide +kernel

theorem sourceB_cycle_actions :
    ∀ c ∈ cyclesB, ∀ x ∈ c, cycleInv c x = sourceB x := by
  apply blockTests_sound sourceB [cyclesB0, cyclesB1, cyclesB2, cyclesB3, cyclesB4, cyclesB5, cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41]
  simp only [List.all_cons, List.all_nil, blockB0,
    blockB1,
    blockB2,
    blockB3,
    blockB4,
    blockB5,
    blockB6,
    blockB7,
    blockB8,
    blockB9,
    blockB10,
    blockB11,
    blockB12,
    blockB13,
    blockB14,
    blockB15,
    blockB16,
    blockB17,
    blockB18,
    blockB19,
    blockB20,
    blockB21,
    blockB22,
    blockB23,
    blockB24,
    blockB25,
    blockB26,
    blockB27,
    blockB28,
    blockB29,
    blockB30,
    blockB31,
    blockB32,
    blockB33,
    blockB34,
    blockB35,
    blockB36,
    blockB37,
    blockB38,
    blockB39,
    blockB40,
    blockB41, Bool.and_self]

private theorem fixedB0 :
    checkPow (fixedTest sourceB maskB) 0 10 = true :=
  by decide +kernel

private theorem fixedB1 :
    checkPow (fixedTest sourceB maskB) 1024 10 = true :=
  by decide +kernel

private theorem fixedB2 :
    checkPow (fixedTest sourceB maskB) 2048 10 = true :=
  by decide +kernel

private theorem fixedB3 :
    checkPow (fixedTest sourceB maskB) 3072 10 = true :=
  by decide +kernel

private theorem fixedB4 :
    checkPow (fixedTest sourceB maskB) 4096 10 = true :=
  by decide +kernel

private theorem fixedB5 :
    checkPow (fixedTest sourceB maskB) 5120 10 = true :=
  by decide +kernel

private theorem fixedB6 :
    checkPow (fixedTest sourceB maskB) 6144 10 = true :=
  by decide +kernel

private theorem fixedB7 :
    checkPow (fixedTest sourceB maskB) 7168 10 = true :=
  by decide +kernel

private theorem fixedB8 :
    checkPow (fixedTest sourceB maskB) 8192 10 = true :=
  by decide +kernel

private theorem fixedB9 :
    checkPow (fixedTest sourceB maskB) 9216 10 = true :=
  by decide +kernel

private theorem fixedB10 :
    checkPow (fixedTest sourceB maskB) 10240 10 = true :=
  by decide +kernel

private theorem fixedB11 :
    checkPow (fixedTest sourceB maskB) 11264 10 = true :=
  by decide +kernel

private theorem fixedB12 :
    checkPow (fixedTest sourceB maskB) 12288 10 = true :=
  by decide +kernel

private theorem fixedB13 :
    checkPow (fixedTest sourceB maskB) 13312 10 = true :=
  by decide +kernel

private theorem fixedB14 :
    checkPow (fixedTest sourceB maskB) 14336 10 = true :=
  by decide +kernel

private theorem fixedB15 :
    checkPow (fixedTest sourceB maskB) 15360 10 = true :=
  by decide +kernel

private theorem fixedB16 :
    checkPow (fixedTest sourceB maskB) 16384 10 = true :=
  by decide +kernel

private theorem fixedB17 :
    checkPow (fixedTest sourceB maskB) 17408 10 = true :=
  by decide +kernel

private theorem fixedB18 :
    checkPow (fixedTest sourceB maskB) 18432 10 = true :=
  by decide +kernel

private theorem fixedB19 :
    checkPow (fixedTest sourceB maskB) 19456 10 = true :=
  by decide +kernel

private theorem fixedB20 :
    checkPow (fixedTest sourceB maskB) 20480 10 = true :=
  by decide +kernel

private theorem fixedB21 :
    checkPow (fixedTest sourceB maskB) 21504 10 = true :=
  by decide +kernel

private theorem fixedB22 :
    checkPow (fixedTest sourceB maskB) 22528 10 = true :=
  by decide +kernel

private theorem fixedB23 :
    checkPow (fixedTest sourceB maskB) 23552 10 = true :=
  by decide +kernel

private theorem fixedB24 :
    checkPow (fixedTest sourceB maskB) 24576 10 = true :=
  by decide +kernel

private theorem fixedB25 :
    checkPow (fixedTest sourceB maskB) 25600 10 = true :=
  by decide +kernel

private theorem fixedB26 :
    checkPow (fixedTest sourceB maskB) 26624 10 = true :=
  by decide +kernel

private theorem fixedB27 :
    checkPow (fixedTest sourceB maskB) 27648 10 = true :=
  by decide +kernel

private theorem fixedB28 :
    checkPow (fixedTest sourceB maskB) 28672 10 = true :=
  by decide +kernel

private theorem fixedB29 :
    checkPow (fixedTest sourceB maskB) 29696 10 = true :=
  by decide +kernel

private theorem fixedB30 :
    checkPow (fixedTest sourceB maskB) 30720 10 = true :=
  by decide +kernel

private theorem fixedB31 :
    checkPow (fixedTest sourceB maskB) 31744 10 = true :=
  by decide +kernel

theorem sourceB_fixed_complement :
    ∀ x : Fin 31671, maskB.testBit x.val = false → sourceB x = x := by
  apply fixedTest_sound
  exact (checkPow_join (fixedTest sourceB maskB) 14 0
    (checkPow_join (fixedTest sourceB maskB) 13 0
    (checkPow_join (fixedTest sourceB maskB) 12 0
    (checkPow_join (fixedTest sourceB maskB) 11 0
    (checkPow_join (fixedTest sourceB maskB) 10 0
    fixedB0
    fixedB1)
    (checkPow_join (fixedTest sourceB maskB) 10 2048
    fixedB2
    fixedB3))
    (checkPow_join (fixedTest sourceB maskB) 11 4096
    (checkPow_join (fixedTest sourceB maskB) 10 4096
    fixedB4
    fixedB5)
    (checkPow_join (fixedTest sourceB maskB) 10 6144
    fixedB6
    fixedB7)))
    (checkPow_join (fixedTest sourceB maskB) 12 8192
    (checkPow_join (fixedTest sourceB maskB) 11 8192
    (checkPow_join (fixedTest sourceB maskB) 10 8192
    fixedB8
    fixedB9)
    (checkPow_join (fixedTest sourceB maskB) 10 10240
    fixedB10
    fixedB11))
    (checkPow_join (fixedTest sourceB maskB) 11 12288
    (checkPow_join (fixedTest sourceB maskB) 10 12288
    fixedB12
    fixedB13)
    (checkPow_join (fixedTest sourceB maskB) 10 14336
    fixedB14
    fixedB15))))
    (checkPow_join (fixedTest sourceB maskB) 13 16384
    (checkPow_join (fixedTest sourceB maskB) 12 16384
    (checkPow_join (fixedTest sourceB maskB) 11 16384
    (checkPow_join (fixedTest sourceB maskB) 10 16384
    fixedB16
    fixedB17)
    (checkPow_join (fixedTest sourceB maskB) 10 18432
    fixedB18
    fixedB19))
    (checkPow_join (fixedTest sourceB maskB) 11 20480
    (checkPow_join (fixedTest sourceB maskB) 10 20480
    fixedB20
    fixedB21)
    (checkPow_join (fixedTest sourceB maskB) 10 22528
    fixedB22
    fixedB23)))
    (checkPow_join (fixedTest sourceB maskB) 12 24576
    (checkPow_join (fixedTest sourceB maskB) 11 24576
    (checkPow_join (fixedTest sourceB maskB) 10 24576
    fixedB24
    fixedB25)
    (checkPow_join (fixedTest sourceB maskB) 10 26624
    fixedB26
    fixedB27))
    (checkPow_join (fixedTest sourceB maskB) 11 28672
    (checkPow_join (fixedTest sourceB maskB) 10 28672
    fixedB28
    fixedB29)
    (checkPow_join (fixedTest sourceB maskB) 10 30720
    fixedB30
    fixedB31)))))

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.SourceActionCheck
