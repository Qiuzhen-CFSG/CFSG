module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks3_0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks3_1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks3_2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks3_3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks3_4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks3_5

/-!
# The exact third-stage generator 3

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

private def parts3 : List (List (List (Fin 31671))) := [cycles3_0, cycles3_1, cycles3_2, cycles3_3, cycles3_4, cycles3_5, cycles3_6, cycles3_7, cycles3_8, cycles3_9, cycles3_10, cycles3_11, cycles3_12, cycles3_13, cycles3_14, cycles3_15, cycles3_16, cycles3_17, cycles3_18, cycles3_19, cycles3_20, cycles3_21, cycles3_22, cycles3_23, cycles3_24, cycles3_25, cycles3_26, cycles3_27, cycles3_28, cycles3_29, cycles3_30, cycles3_31, cycles3_32, cycles3_33, cycles3_34, cycles3_35, cycles3_36, cycles3_37, cycles3_38, cycles3_39, cycles3_40, cycles3_41, cycles3_42, cycles3_43]
private def masks3 : List Nat := [mask3_0, mask3_1, mask3_2, mask3_3, mask3_4, mask3_5, mask3_6, mask3_7, mask3_8, mask3_9, mask3_10, mask3_11, mask3_12, mask3_13, mask3_14, mask3_15, mask3_16, mask3_17, mask3_18, mask3_19, mask3_20, mask3_21, mask3_22, mask3_23, mask3_24, mask3_25, mask3_26, mask3_27, mask3_28, mask3_29, mask3_30, mask3_31, mask3_32, mask3_33, mask3_34, mask3_35, mask3_36, mask3_37, mask3_38, mask3_39, mask3_40, mask3_41, mask3_42, mask3_43]
private def fullMask3 : Nat := 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000001ffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000007ffffffffffffffffffffffffffffffffffffffffffff8000ffffffffffffffffffffffffffffff0000000000000000001ffffffffffffffffffffffffffffffffffe00000007fffffffffffe000000000000001ffffffffffffffffffffffffffffffffffe00000007ffffffffffffffffe0001ffffec0c07ff8000

private theorem decoded :
    decodeCycleBlocks 31671 KernelData.cycleBlocks3 = parts3.flatten := by
  apply decode_of_blocks
  exact (List.Forall₂.cons cycles3_0_spec (List.Forall₂.cons cycles3_1_spec (List.Forall₂.cons cycles3_2_spec (List.Forall₂.cons cycles3_3_spec (List.Forall₂.cons cycles3_4_spec (List.Forall₂.cons cycles3_5_spec (List.Forall₂.cons cycles3_6_spec (List.Forall₂.cons cycles3_7_spec (List.Forall₂.cons cycles3_8_spec (List.Forall₂.cons cycles3_9_spec (List.Forall₂.cons cycles3_10_spec (List.Forall₂.cons cycles3_11_spec (List.Forall₂.cons cycles3_12_spec (List.Forall₂.cons cycles3_13_spec (List.Forall₂.cons cycles3_14_spec (List.Forall₂.cons cycles3_15_spec (List.Forall₂.cons cycles3_16_spec (List.Forall₂.cons cycles3_17_spec (List.Forall₂.cons cycles3_18_spec (List.Forall₂.cons cycles3_19_spec (List.Forall₂.cons cycles3_20_spec (List.Forall₂.cons cycles3_21_spec (List.Forall₂.cons cycles3_22_spec (List.Forall₂.cons cycles3_23_spec (List.Forall₂.cons cycles3_24_spec (List.Forall₂.cons cycles3_25_spec (List.Forall₂.cons cycles3_26_spec (List.Forall₂.cons cycles3_27_spec (List.Forall₂.cons cycles3_28_spec (List.Forall₂.cons cycles3_29_spec (List.Forall₂.cons cycles3_30_spec (List.Forall₂.cons cycles3_31_spec (List.Forall₂.cons cycles3_32_spec (List.Forall₂.cons cycles3_33_spec (List.Forall₂.cons cycles3_34_spec (List.Forall₂.cons cycles3_35_spec (List.Forall₂.cons cycles3_36_spec (List.Forall₂.cons cycles3_37_spec (List.Forall₂.cons cycles3_38_spec (List.Forall₂.cons cycles3_39_spec (List.Forall₂.cons cycles3_40_spec (List.Forall₂.cons cycles3_41_spec (List.Forall₂.cons cycles3_42_spec (List.Forall₂.cons cycles3_43_spec List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))

private theorem certificates :
    List.Forall₂ (fun cs m => Certificate cs.flatten m) parts3 masks3 :=
  (List.Forall₂.cons certificate3_0 (List.Forall₂.cons certificate3_1 (List.Forall₂.cons certificate3_2 (List.Forall₂.cons certificate3_3 (List.Forall₂.cons certificate3_4 (List.Forall₂.cons certificate3_5 (List.Forall₂.cons certificate3_6 (List.Forall₂.cons certificate3_7 (List.Forall₂.cons certificate3_8 (List.Forall₂.cons certificate3_9 (List.Forall₂.cons certificate3_10 (List.Forall₂.cons certificate3_11 (List.Forall₂.cons certificate3_12 (List.Forall₂.cons certificate3_13 (List.Forall₂.cons certificate3_14 (List.Forall₂.cons certificate3_15 (List.Forall₂.cons certificate3_16 (List.Forall₂.cons certificate3_17 (List.Forall₂.cons certificate3_18 (List.Forall₂.cons certificate3_19 (List.Forall₂.cons certificate3_20 (List.Forall₂.cons certificate3_21 (List.Forall₂.cons certificate3_22 (List.Forall₂.cons certificate3_23 (List.Forall₂.cons certificate3_24 (List.Forall₂.cons certificate3_25 (List.Forall₂.cons certificate3_26 (List.Forall₂.cons certificate3_27 (List.Forall₂.cons certificate3_28 (List.Forall₂.cons certificate3_29 (List.Forall₂.cons certificate3_30 (List.Forall₂.cons certificate3_31 (List.Forall₂.cons certificate3_32 (List.Forall₂.cons certificate3_33 (List.Forall₂.cons certificate3_34 (List.Forall₂.cons certificate3_35 (List.Forall₂.cons certificate3_36 (List.Forall₂.cons certificate3_37 (List.Forall₂.cons certificate3_38 (List.Forall₂.cons certificate3_39 (List.Forall₂.cons certificate3_40 (List.Forall₂.cons certificate3_41 (List.Forall₂.cons certificate3_42 (List.Forall₂.cons certificate3_43 List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))

private theorem disjoint : disjointMasks masks3 = true := by decide +kernel

private theorem actions : parts3.all (cycleTest Packed3.forward) = true := by
  simp only [parts3, List.all_cons, List.all_nil, action3_0, action3_1, action3_2, action3_3, action3_4, action3_5, action3_6, action3_7, action3_8, action3_9, action3_10, action3_11, action3_12, action3_13, action3_14, action3_15, action3_16, action3_17, action3_18, action3_19, action3_20, action3_21, action3_22, action3_23, action3_24, action3_25, action3_26, action3_27, action3_28, action3_29, action3_30, action3_31, action3_32, action3_33, action3_34, action3_35, action3_36, action3_37, action3_38, action3_39, action3_40, action3_41, action3_42, action3_43, Bool.and_self]

private theorem mask_union : unionMasks masks3 = fullMask3 := by decide +kernel

private theorem fixed0 :
    checkPow (fixedTest Packed3.forward fullMask3) 0 10 = true := by
  decide +kernel

private theorem fixed1 :
    checkPow (fixedTest Packed3.forward fullMask3) 1024 10 = true := by
  decide +kernel

private theorem fixed2 :
    checkPow (fixedTest Packed3.forward fullMask3) 2048 10 = true := by
  decide +kernel

private theorem fixed3 :
    checkPow (fixedTest Packed3.forward fullMask3) 3072 10 = true := by
  decide +kernel

private theorem fixed4 :
    checkPow (fixedTest Packed3.forward fullMask3) 4096 10 = true := by
  decide +kernel

private theorem fixed5 :
    checkPow (fixedTest Packed3.forward fullMask3) 5120 10 = true := by
  decide +kernel

private theorem fixed6 :
    checkPow (fixedTest Packed3.forward fullMask3) 6144 10 = true := by
  decide +kernel

private theorem fixed7 :
    checkPow (fixedTest Packed3.forward fullMask3) 7168 10 = true := by
  decide +kernel

private theorem fixed8 :
    checkPow (fixedTest Packed3.forward fullMask3) 8192 10 = true := by
  decide +kernel

private theorem fixed9 :
    checkPow (fixedTest Packed3.forward fullMask3) 9216 10 = true := by
  decide +kernel

private theorem fixed10 :
    checkPow (fixedTest Packed3.forward fullMask3) 10240 10 = true := by
  decide +kernel

private theorem fixed11 :
    checkPow (fixedTest Packed3.forward fullMask3) 11264 10 = true := by
  decide +kernel

private theorem fixed12 :
    checkPow (fixedTest Packed3.forward fullMask3) 12288 10 = true := by
  decide +kernel

private theorem fixed13 :
    checkPow (fixedTest Packed3.forward fullMask3) 13312 10 = true := by
  decide +kernel

private theorem fixed14 :
    checkPow (fixedTest Packed3.forward fullMask3) 14336 10 = true := by
  decide +kernel

private theorem fixed15 :
    checkPow (fixedTest Packed3.forward fullMask3) 15360 10 = true := by
  decide +kernel

private theorem fixed16 :
    checkPow (fixedTest Packed3.forward fullMask3) 16384 10 = true := by
  decide +kernel

private theorem fixed17 :
    checkPow (fixedTest Packed3.forward fullMask3) 17408 10 = true := by
  decide +kernel

private theorem fixed18 :
    checkPow (fixedTest Packed3.forward fullMask3) 18432 10 = true := by
  decide +kernel

private theorem fixed19 :
    checkPow (fixedTest Packed3.forward fullMask3) 19456 10 = true := by
  decide +kernel

private theorem fixed20 :
    checkPow (fixedTest Packed3.forward fullMask3) 20480 10 = true := by
  decide +kernel

private theorem fixed21 :
    checkPow (fixedTest Packed3.forward fullMask3) 21504 10 = true := by
  decide +kernel

private theorem fixed22 :
    checkPow (fixedTest Packed3.forward fullMask3) 22528 10 = true := by
  decide +kernel

private theorem fixed23 :
    checkPow (fixedTest Packed3.forward fullMask3) 23552 10 = true := by
  decide +kernel

private theorem fixed24 :
    checkPow (fixedTest Packed3.forward fullMask3) 24576 10 = true := by
  decide +kernel

private theorem fixed25 :
    checkPow (fixedTest Packed3.forward fullMask3) 25600 10 = true := by
  decide +kernel

private theorem fixed26 :
    checkPow (fixedTest Packed3.forward fullMask3) 26624 10 = true := by
  decide +kernel

private theorem fixed27 :
    checkPow (fixedTest Packed3.forward fullMask3) 27648 10 = true := by
  decide +kernel

private theorem fixed28 :
    checkPow (fixedTest Packed3.forward fullMask3) 28672 10 = true := by
  decide +kernel

private theorem fixed29 :
    checkPow (fixedTest Packed3.forward fullMask3) 29696 10 = true := by
  decide +kernel

private theorem fixed30 :
    checkPow (fixedTest Packed3.forward fullMask3) 30720 10 = true := by
  decide +kernel

private theorem fixed31 :
    checkPow (fixedTest Packed3.forward fullMask3) 31744 10 = true := by
  decide +kernel

private theorem fixed_complement :
    ∀ x : Fin 31671, (unionMasks masks3).testBit x.val = false → Packed3.forward x = x := by
  rw [mask_union]
  apply fixedTest_sound
  exact (checkPow_join (fixedTest Packed3.forward fullMask3) 14 0
    (checkPow_join (fixedTest Packed3.forward fullMask3) 13 0
    (checkPow_join (fixedTest Packed3.forward fullMask3) 12 0
    (checkPow_join (fixedTest Packed3.forward fullMask3) 11 0
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 0
    fixed0
    fixed1)
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 2048
    fixed2
    fixed3))
    (checkPow_join (fixedTest Packed3.forward fullMask3) 11 4096
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 4096
    fixed4
    fixed5)
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 6144
    fixed6
    fixed7)))
    (checkPow_join (fixedTest Packed3.forward fullMask3) 12 8192
    (checkPow_join (fixedTest Packed3.forward fullMask3) 11 8192
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 8192
    fixed8
    fixed9)
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 10240
    fixed10
    fixed11))
    (checkPow_join (fixedTest Packed3.forward fullMask3) 11 12288
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 12288
    fixed12
    fixed13)
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 14336
    fixed14
    fixed15))))
    (checkPow_join (fixedTest Packed3.forward fullMask3) 13 16384
    (checkPow_join (fixedTest Packed3.forward fullMask3) 12 16384
    (checkPow_join (fixedTest Packed3.forward fullMask3) 11 16384
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 16384
    fixed16
    fixed17)
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 18432
    fixed18
    fixed19))
    (checkPow_join (fixedTest Packed3.forward fullMask3) 11 20480
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 20480
    fixed20
    fixed21)
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 22528
    fixed22
    fixed23)))
    (checkPow_join (fixedTest Packed3.forward fullMask3) 12 24576
    (checkPow_join (fixedTest Packed3.forward fullMask3) 11 24576
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 24576
    fixed24
    fixed25)
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 26624
    fixed26
    fixed27))
    (checkPow_join (fixedTest Packed3.forward fullMask3) 11 28672
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 28672
    fixed28
    fixed29)
    (checkPow_join (fixedTest Packed3.forward fullMask3) 10 30720
    fixed30
    fixed31)))))

/-- Equality with the unchanged, literal inverse cycle product. -/
theorem permutation3_eq : Packed3.permutation = KernelData.generator3 := by
  apply Equiv.ext
  intro x
  exact map_eq_of_certificates Packed3.forward KernelData.cycleBlocks3
    parts3 masks3 decoded certificates disjoint actions fixed_complement x

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.GeneratorAgreement
