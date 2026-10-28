module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks2_0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks2_1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks2_2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks2_3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks2_4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks2_5

/-!
# The exact third-stage generator 2

The disjoint block certificates cover every moved letter. Balanced checks
verify the fixed complement. Together these determine the entire literal
inverse cycle product, not merely its generated subgroup.
All witnesses are checked in Lean. The literal strings and packed tables are
unchanged. Reproduce with `GeneratorAgreement/source/generate.py`.
Source: ATLAS F23G1-p31671B0; application: GLS3 Table 5.3u.
-/

set_option Elab.async false

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.GeneratorAgreement
open AtlasCarriers KernelCertificate KernelCertificate.FixedLetterCheck
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate
open SourceActionCheck

private def parts2 : List (List (List (Fin 31671))) := [cycles2_0, cycles2_1, cycles2_2, cycles2_3, cycles2_4, cycles2_5, cycles2_6, cycles2_7, cycles2_8, cycles2_9, cycles2_10, cycles2_11, cycles2_12, cycles2_13, cycles2_14, cycles2_15, cycles2_16, cycles2_17, cycles2_18, cycles2_19, cycles2_20, cycles2_21, cycles2_22, cycles2_23, cycles2_24, cycles2_25, cycles2_26, cycles2_27, cycles2_28, cycles2_29, cycles2_30, cycles2_31, cycles2_32, cycles2_33, cycles2_34, cycles2_35, cycles2_36, cycles2_37, cycles2_38, cycles2_39, cycles2_40]
private def masks2 : List Nat := [mask2_0, mask2_1, mask2_2, mask2_3, mask2_4, mask2_5, mask2_6, mask2_7, mask2_8, mask2_9, mask2_10, mask2_11, mask2_12, mask2_13, mask2_14, mask2_15, mask2_16, mask2_17, mask2_18, mask2_19, mask2_20, mask2_21, mask2_22, mask2_23, mask2_24, mask2_25, mask2_26, mask2_27, mask2_28, mask2_29, mask2_30, mask2_31, mask2_32, mask2_33, mask2_34, mask2_35, mask2_36, mask2_37, mask2_38, mask2_39, mask2_40]
private def fullMask2 : Nat := 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ffffe00000000000

private theorem decoded :
    decodeCycleBlocks 31671 KernelData.cycleBlocks2 = parts2.flatten := by
  apply decode_of_blocks
  exact (List.Forall₂.cons cycles2_0_spec (List.Forall₂.cons cycles2_1_spec (List.Forall₂.cons cycles2_2_spec (List.Forall₂.cons cycles2_3_spec (List.Forall₂.cons cycles2_4_spec (List.Forall₂.cons cycles2_5_spec (List.Forall₂.cons cycles2_6_spec (List.Forall₂.cons cycles2_7_spec (List.Forall₂.cons cycles2_8_spec (List.Forall₂.cons cycles2_9_spec (List.Forall₂.cons cycles2_10_spec (List.Forall₂.cons cycles2_11_spec (List.Forall₂.cons cycles2_12_spec (List.Forall₂.cons cycles2_13_spec (List.Forall₂.cons cycles2_14_spec (List.Forall₂.cons cycles2_15_spec (List.Forall₂.cons cycles2_16_spec (List.Forall₂.cons cycles2_17_spec (List.Forall₂.cons cycles2_18_spec (List.Forall₂.cons cycles2_19_spec (List.Forall₂.cons cycles2_20_spec (List.Forall₂.cons cycles2_21_spec (List.Forall₂.cons cycles2_22_spec (List.Forall₂.cons cycles2_23_spec (List.Forall₂.cons cycles2_24_spec (List.Forall₂.cons cycles2_25_spec (List.Forall₂.cons cycles2_26_spec (List.Forall₂.cons cycles2_27_spec (List.Forall₂.cons cycles2_28_spec (List.Forall₂.cons cycles2_29_spec (List.Forall₂.cons cycles2_30_spec (List.Forall₂.cons cycles2_31_spec (List.Forall₂.cons cycles2_32_spec (List.Forall₂.cons cycles2_33_spec (List.Forall₂.cons cycles2_34_spec (List.Forall₂.cons cycles2_35_spec (List.Forall₂.cons cycles2_36_spec (List.Forall₂.cons cycles2_37_spec (List.Forall₂.cons cycles2_38_spec (List.Forall₂.cons cycles2_39_spec (List.Forall₂.cons cycles2_40_spec List.Forall₂.nil)))))))))))))))))))))))))))))))))))))))))

private theorem certificates :
    List.Forall₂ (fun cs m => Certificate cs.flatten m) parts2 masks2 :=
  (List.Forall₂.cons certificate2_0 (List.Forall₂.cons certificate2_1 (List.Forall₂.cons certificate2_2 (List.Forall₂.cons certificate2_3 (List.Forall₂.cons certificate2_4 (List.Forall₂.cons certificate2_5 (List.Forall₂.cons certificate2_6 (List.Forall₂.cons certificate2_7 (List.Forall₂.cons certificate2_8 (List.Forall₂.cons certificate2_9 (List.Forall₂.cons certificate2_10 (List.Forall₂.cons certificate2_11 (List.Forall₂.cons certificate2_12 (List.Forall₂.cons certificate2_13 (List.Forall₂.cons certificate2_14 (List.Forall₂.cons certificate2_15 (List.Forall₂.cons certificate2_16 (List.Forall₂.cons certificate2_17 (List.Forall₂.cons certificate2_18 (List.Forall₂.cons certificate2_19 (List.Forall₂.cons certificate2_20 (List.Forall₂.cons certificate2_21 (List.Forall₂.cons certificate2_22 (List.Forall₂.cons certificate2_23 (List.Forall₂.cons certificate2_24 (List.Forall₂.cons certificate2_25 (List.Forall₂.cons certificate2_26 (List.Forall₂.cons certificate2_27 (List.Forall₂.cons certificate2_28 (List.Forall₂.cons certificate2_29 (List.Forall₂.cons certificate2_30 (List.Forall₂.cons certificate2_31 (List.Forall₂.cons certificate2_32 (List.Forall₂.cons certificate2_33 (List.Forall₂.cons certificate2_34 (List.Forall₂.cons certificate2_35 (List.Forall₂.cons certificate2_36 (List.Forall₂.cons certificate2_37 (List.Forall₂.cons certificate2_38 (List.Forall₂.cons certificate2_39 (List.Forall₂.cons certificate2_40 List.Forall₂.nil)))))))))))))))))))))))))))))))))))))))))

private theorem disjoint : disjointMasks masks2 = true := by decide +kernel

private theorem actions : parts2.all (cycleTest Packed2.forward) = true := by
  simp only [parts2, List.all_cons, List.all_nil, action2_0, action2_1, action2_2, action2_3, action2_4, action2_5, action2_6, action2_7, action2_8, action2_9, action2_10, action2_11, action2_12, action2_13, action2_14, action2_15, action2_16, action2_17, action2_18, action2_19, action2_20, action2_21, action2_22, action2_23, action2_24, action2_25, action2_26, action2_27, action2_28, action2_29, action2_30, action2_31, action2_32, action2_33, action2_34, action2_35, action2_36, action2_37, action2_38, action2_39, action2_40, Bool.and_self]

private theorem mask_union : unionMasks masks2 = fullMask2 := by decide +kernel

private theorem fixed0 :
    checkPow (fixedTest Packed2.forward fullMask2) 0 10 = true := by
  decide +kernel

private theorem fixed1 :
    checkPow (fixedTest Packed2.forward fullMask2) 1024 10 = true := by
  decide +kernel

private theorem fixed2 :
    checkPow (fixedTest Packed2.forward fullMask2) 2048 10 = true := by
  decide +kernel

private theorem fixed3 :
    checkPow (fixedTest Packed2.forward fullMask2) 3072 10 = true := by
  decide +kernel

private theorem fixed4 :
    checkPow (fixedTest Packed2.forward fullMask2) 4096 10 = true := by
  decide +kernel

private theorem fixed5 :
    checkPow (fixedTest Packed2.forward fullMask2) 5120 10 = true := by
  decide +kernel

private theorem fixed6 :
    checkPow (fixedTest Packed2.forward fullMask2) 6144 10 = true := by
  decide +kernel

private theorem fixed7 :
    checkPow (fixedTest Packed2.forward fullMask2) 7168 10 = true := by
  decide +kernel

private theorem fixed8 :
    checkPow (fixedTest Packed2.forward fullMask2) 8192 10 = true := by
  decide +kernel

private theorem fixed9 :
    checkPow (fixedTest Packed2.forward fullMask2) 9216 10 = true := by
  decide +kernel

private theorem fixed10 :
    checkPow (fixedTest Packed2.forward fullMask2) 10240 10 = true := by
  decide +kernel

private theorem fixed11 :
    checkPow (fixedTest Packed2.forward fullMask2) 11264 10 = true := by
  decide +kernel

private theorem fixed12 :
    checkPow (fixedTest Packed2.forward fullMask2) 12288 10 = true := by
  decide +kernel

private theorem fixed13 :
    checkPow (fixedTest Packed2.forward fullMask2) 13312 10 = true := by
  decide +kernel

private theorem fixed14 :
    checkPow (fixedTest Packed2.forward fullMask2) 14336 10 = true := by
  decide +kernel

private theorem fixed15 :
    checkPow (fixedTest Packed2.forward fullMask2) 15360 10 = true := by
  decide +kernel

private theorem fixed16 :
    checkPow (fixedTest Packed2.forward fullMask2) 16384 10 = true := by
  decide +kernel

private theorem fixed17 :
    checkPow (fixedTest Packed2.forward fullMask2) 17408 10 = true := by
  decide +kernel

private theorem fixed18 :
    checkPow (fixedTest Packed2.forward fullMask2) 18432 10 = true := by
  decide +kernel

private theorem fixed19 :
    checkPow (fixedTest Packed2.forward fullMask2) 19456 10 = true := by
  decide +kernel

private theorem fixed20 :
    checkPow (fixedTest Packed2.forward fullMask2) 20480 10 = true := by
  decide +kernel

private theorem fixed21 :
    checkPow (fixedTest Packed2.forward fullMask2) 21504 10 = true := by
  decide +kernel

private theorem fixed22 :
    checkPow (fixedTest Packed2.forward fullMask2) 22528 10 = true := by
  decide +kernel

private theorem fixed23 :
    checkPow (fixedTest Packed2.forward fullMask2) 23552 10 = true := by
  decide +kernel

private theorem fixed24 :
    checkPow (fixedTest Packed2.forward fullMask2) 24576 10 = true := by
  decide +kernel

private theorem fixed25 :
    checkPow (fixedTest Packed2.forward fullMask2) 25600 10 = true := by
  decide +kernel

private theorem fixed26 :
    checkPow (fixedTest Packed2.forward fullMask2) 26624 10 = true := by
  decide +kernel

private theorem fixed27 :
    checkPow (fixedTest Packed2.forward fullMask2) 27648 10 = true := by
  decide +kernel

private theorem fixed28 :
    checkPow (fixedTest Packed2.forward fullMask2) 28672 10 = true := by
  decide +kernel

private theorem fixed29 :
    checkPow (fixedTest Packed2.forward fullMask2) 29696 10 = true := by
  decide +kernel

private theorem fixed30 :
    checkPow (fixedTest Packed2.forward fullMask2) 30720 10 = true := by
  decide +kernel

private theorem fixed31 :
    checkPow (fixedTest Packed2.forward fullMask2) 31744 10 = true := by
  decide +kernel

private theorem fixed_complement :
    ∀ x : Fin 31671, (unionMasks masks2).testBit x.val = false → Packed2.forward x = x := by
  rw [mask_union]
  apply fixedTest_sound
  exact (checkPow_join (fixedTest Packed2.forward fullMask2) 14 0
    (checkPow_join (fixedTest Packed2.forward fullMask2) 13 0
    (checkPow_join (fixedTest Packed2.forward fullMask2) 12 0
    (checkPow_join (fixedTest Packed2.forward fullMask2) 11 0
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 0
    fixed0
    fixed1)
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 2048
    fixed2
    fixed3))
    (checkPow_join (fixedTest Packed2.forward fullMask2) 11 4096
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 4096
    fixed4
    fixed5)
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 6144
    fixed6
    fixed7)))
    (checkPow_join (fixedTest Packed2.forward fullMask2) 12 8192
    (checkPow_join (fixedTest Packed2.forward fullMask2) 11 8192
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 8192
    fixed8
    fixed9)
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 10240
    fixed10
    fixed11))
    (checkPow_join (fixedTest Packed2.forward fullMask2) 11 12288
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 12288
    fixed12
    fixed13)
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 14336
    fixed14
    fixed15))))
    (checkPow_join (fixedTest Packed2.forward fullMask2) 13 16384
    (checkPow_join (fixedTest Packed2.forward fullMask2) 12 16384
    (checkPow_join (fixedTest Packed2.forward fullMask2) 11 16384
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 16384
    fixed16
    fixed17)
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 18432
    fixed18
    fixed19))
    (checkPow_join (fixedTest Packed2.forward fullMask2) 11 20480
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 20480
    fixed20
    fixed21)
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 22528
    fixed22
    fixed23)))
    (checkPow_join (fixedTest Packed2.forward fullMask2) 12 24576
    (checkPow_join (fixedTest Packed2.forward fullMask2) 11 24576
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 24576
    fixed24
    fixed25)
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 26624
    fixed26
    fixed27))
    (checkPow_join (fixedTest Packed2.forward fullMask2) 11 28672
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 28672
    fixed28
    fixed29)
    (checkPow_join (fixedTest Packed2.forward fullMask2) 10 30720
    fixed30
    fixed31)))))

/-- Equality with the unchanged, literal inverse cycle product. -/
theorem permutation2_eq : Packed2.permutation = KernelData.generator2 := by
  apply Equiv.ext
  intro x
  exact map_eq_of_certificates Packed2.forward KernelData.cycleBlocks2
    parts2 masks2 decoded certificates disjoint actions fixed_complement x

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.GeneratorAgreement
