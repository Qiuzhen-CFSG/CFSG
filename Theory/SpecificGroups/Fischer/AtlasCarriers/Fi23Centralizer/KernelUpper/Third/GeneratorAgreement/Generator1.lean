module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks1_0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks1_1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks1_2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks1_3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks1_4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks1_5

/-!
# The exact third-stage generator 1

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

private def parts1 : List (List (List (Fin 31671))) := [cycles1_0, cycles1_1, cycles1_2, cycles1_3, cycles1_4, cycles1_5, cycles1_6, cycles1_7, cycles1_8, cycles1_9, cycles1_10, cycles1_11, cycles1_12, cycles1_13, cycles1_14, cycles1_15, cycles1_16, cycles1_17, cycles1_18, cycles1_19, cycles1_20, cycles1_21, cycles1_22, cycles1_23, cycles1_24, cycles1_25, cycles1_26, cycles1_27, cycles1_28, cycles1_29, cycles1_30, cycles1_31, cycles1_32, cycles1_33, cycles1_34, cycles1_35, cycles1_36, cycles1_37, cycles1_38, cycles1_39, cycles1_40, cycles1_41, cycles1_42, cycles1_43, cycles1_44]
private def masks1 : List Nat := [mask1_0, mask1_1, mask1_2, mask1_3, mask1_4, mask1_5, mask1_6, mask1_7, mask1_8, mask1_9, mask1_10, mask1_11, mask1_12, mask1_13, mask1_14, mask1_15, mask1_16, mask1_17, mask1_18, mask1_19, mask1_20, mask1_21, mask1_22, mask1_23, mask1_24, mask1_25, mask1_26, mask1_27, mask1_28, mask1_29, mask1_30, mask1_31, mask1_32, mask1_33, mask1_34, mask1_35, mask1_36, mask1_37, mask1_38, mask1_39, mask1_40, mask1_41, mask1_42, mask1_43, mask1_44]
private def fullMask1 : Nat := 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000003fffffff000000000

private theorem decoded :
    decodeCycleBlocks 31671 KernelData.cycleBlocks1 = parts1.flatten := by
  apply decode_of_blocks
  exact (List.Forall₂.cons cycles1_0_spec (List.Forall₂.cons cycles1_1_spec (List.Forall₂.cons cycles1_2_spec (List.Forall₂.cons cycles1_3_spec (List.Forall₂.cons cycles1_4_spec (List.Forall₂.cons cycles1_5_spec (List.Forall₂.cons cycles1_6_spec (List.Forall₂.cons cycles1_7_spec (List.Forall₂.cons cycles1_8_spec (List.Forall₂.cons cycles1_9_spec (List.Forall₂.cons cycles1_10_spec (List.Forall₂.cons cycles1_11_spec (List.Forall₂.cons cycles1_12_spec (List.Forall₂.cons cycles1_13_spec (List.Forall₂.cons cycles1_14_spec (List.Forall₂.cons cycles1_15_spec (List.Forall₂.cons cycles1_16_spec (List.Forall₂.cons cycles1_17_spec (List.Forall₂.cons cycles1_18_spec (List.Forall₂.cons cycles1_19_spec (List.Forall₂.cons cycles1_20_spec (List.Forall₂.cons cycles1_21_spec (List.Forall₂.cons cycles1_22_spec (List.Forall₂.cons cycles1_23_spec (List.Forall₂.cons cycles1_24_spec (List.Forall₂.cons cycles1_25_spec (List.Forall₂.cons cycles1_26_spec (List.Forall₂.cons cycles1_27_spec (List.Forall₂.cons cycles1_28_spec (List.Forall₂.cons cycles1_29_spec (List.Forall₂.cons cycles1_30_spec (List.Forall₂.cons cycles1_31_spec (List.Forall₂.cons cycles1_32_spec (List.Forall₂.cons cycles1_33_spec (List.Forall₂.cons cycles1_34_spec (List.Forall₂.cons cycles1_35_spec (List.Forall₂.cons cycles1_36_spec (List.Forall₂.cons cycles1_37_spec (List.Forall₂.cons cycles1_38_spec (List.Forall₂.cons cycles1_39_spec (List.Forall₂.cons cycles1_40_spec (List.Forall₂.cons cycles1_41_spec (List.Forall₂.cons cycles1_42_spec (List.Forall₂.cons cycles1_43_spec (List.Forall₂.cons cycles1_44_spec List.Forall₂.nil)))))))))))))))))))))))))))))))))))))))))))))

private theorem certificates :
    List.Forall₂ (fun cs m => Certificate cs.flatten m) parts1 masks1 :=
  (List.Forall₂.cons certificate1_0 (List.Forall₂.cons certificate1_1 (List.Forall₂.cons certificate1_2 (List.Forall₂.cons certificate1_3 (List.Forall₂.cons certificate1_4 (List.Forall₂.cons certificate1_5 (List.Forall₂.cons certificate1_6 (List.Forall₂.cons certificate1_7 (List.Forall₂.cons certificate1_8 (List.Forall₂.cons certificate1_9 (List.Forall₂.cons certificate1_10 (List.Forall₂.cons certificate1_11 (List.Forall₂.cons certificate1_12 (List.Forall₂.cons certificate1_13 (List.Forall₂.cons certificate1_14 (List.Forall₂.cons certificate1_15 (List.Forall₂.cons certificate1_16 (List.Forall₂.cons certificate1_17 (List.Forall₂.cons certificate1_18 (List.Forall₂.cons certificate1_19 (List.Forall₂.cons certificate1_20 (List.Forall₂.cons certificate1_21 (List.Forall₂.cons certificate1_22 (List.Forall₂.cons certificate1_23 (List.Forall₂.cons certificate1_24 (List.Forall₂.cons certificate1_25 (List.Forall₂.cons certificate1_26 (List.Forall₂.cons certificate1_27 (List.Forall₂.cons certificate1_28 (List.Forall₂.cons certificate1_29 (List.Forall₂.cons certificate1_30 (List.Forall₂.cons certificate1_31 (List.Forall₂.cons certificate1_32 (List.Forall₂.cons certificate1_33 (List.Forall₂.cons certificate1_34 (List.Forall₂.cons certificate1_35 (List.Forall₂.cons certificate1_36 (List.Forall₂.cons certificate1_37 (List.Forall₂.cons certificate1_38 (List.Forall₂.cons certificate1_39 (List.Forall₂.cons certificate1_40 (List.Forall₂.cons certificate1_41 (List.Forall₂.cons certificate1_42 (List.Forall₂.cons certificate1_43 (List.Forall₂.cons certificate1_44 List.Forall₂.nil)))))))))))))))))))))))))))))))))))))))))))))

private theorem disjoint : disjointMasks masks1 = true := by decide +kernel

private theorem actions : parts1.all (cycleTest Packed1.forward) = true := by
  simp only [parts1, List.all_cons, List.all_nil, action1_0, action1_1, action1_2, action1_3, action1_4, action1_5, action1_6, action1_7, action1_8, action1_9, action1_10, action1_11, action1_12, action1_13, action1_14, action1_15, action1_16, action1_17, action1_18, action1_19, action1_20, action1_21, action1_22, action1_23, action1_24, action1_25, action1_26, action1_27, action1_28, action1_29, action1_30, action1_31, action1_32, action1_33, action1_34, action1_35, action1_36, action1_37, action1_38, action1_39, action1_40, action1_41, action1_42, action1_43, action1_44, Bool.and_self]

private theorem mask_union : unionMasks masks1 = fullMask1 := by decide +kernel

private theorem fixed0 :
    checkPow (fixedTest Packed1.forward fullMask1) 0 10 = true := by
  decide +kernel

private theorem fixed1 :
    checkPow (fixedTest Packed1.forward fullMask1) 1024 10 = true := by
  decide +kernel

private theorem fixed2 :
    checkPow (fixedTest Packed1.forward fullMask1) 2048 10 = true := by
  decide +kernel

private theorem fixed3 :
    checkPow (fixedTest Packed1.forward fullMask1) 3072 10 = true := by
  decide +kernel

private theorem fixed4 :
    checkPow (fixedTest Packed1.forward fullMask1) 4096 10 = true := by
  decide +kernel

private theorem fixed5 :
    checkPow (fixedTest Packed1.forward fullMask1) 5120 10 = true := by
  decide +kernel

private theorem fixed6 :
    checkPow (fixedTest Packed1.forward fullMask1) 6144 10 = true := by
  decide +kernel

private theorem fixed7 :
    checkPow (fixedTest Packed1.forward fullMask1) 7168 10 = true := by
  decide +kernel

private theorem fixed8 :
    checkPow (fixedTest Packed1.forward fullMask1) 8192 10 = true := by
  decide +kernel

private theorem fixed9 :
    checkPow (fixedTest Packed1.forward fullMask1) 9216 10 = true := by
  decide +kernel

private theorem fixed10 :
    checkPow (fixedTest Packed1.forward fullMask1) 10240 10 = true := by
  decide +kernel

private theorem fixed11 :
    checkPow (fixedTest Packed1.forward fullMask1) 11264 10 = true := by
  decide +kernel

private theorem fixed12 :
    checkPow (fixedTest Packed1.forward fullMask1) 12288 10 = true := by
  decide +kernel

private theorem fixed13 :
    checkPow (fixedTest Packed1.forward fullMask1) 13312 10 = true := by
  decide +kernel

private theorem fixed14 :
    checkPow (fixedTest Packed1.forward fullMask1) 14336 10 = true := by
  decide +kernel

private theorem fixed15 :
    checkPow (fixedTest Packed1.forward fullMask1) 15360 10 = true := by
  decide +kernel

private theorem fixed16 :
    checkPow (fixedTest Packed1.forward fullMask1) 16384 10 = true := by
  decide +kernel

private theorem fixed17 :
    checkPow (fixedTest Packed1.forward fullMask1) 17408 10 = true := by
  decide +kernel

private theorem fixed18 :
    checkPow (fixedTest Packed1.forward fullMask1) 18432 10 = true := by
  decide +kernel

private theorem fixed19 :
    checkPow (fixedTest Packed1.forward fullMask1) 19456 10 = true := by
  decide +kernel

private theorem fixed20 :
    checkPow (fixedTest Packed1.forward fullMask1) 20480 10 = true := by
  decide +kernel

private theorem fixed21 :
    checkPow (fixedTest Packed1.forward fullMask1) 21504 10 = true := by
  decide +kernel

private theorem fixed22 :
    checkPow (fixedTest Packed1.forward fullMask1) 22528 10 = true := by
  decide +kernel

private theorem fixed23 :
    checkPow (fixedTest Packed1.forward fullMask1) 23552 10 = true := by
  decide +kernel

private theorem fixed24 :
    checkPow (fixedTest Packed1.forward fullMask1) 24576 10 = true := by
  decide +kernel

private theorem fixed25 :
    checkPow (fixedTest Packed1.forward fullMask1) 25600 10 = true := by
  decide +kernel

private theorem fixed26 :
    checkPow (fixedTest Packed1.forward fullMask1) 26624 10 = true := by
  decide +kernel

private theorem fixed27 :
    checkPow (fixedTest Packed1.forward fullMask1) 27648 10 = true := by
  decide +kernel

private theorem fixed28 :
    checkPow (fixedTest Packed1.forward fullMask1) 28672 10 = true := by
  decide +kernel

private theorem fixed29 :
    checkPow (fixedTest Packed1.forward fullMask1) 29696 10 = true := by
  decide +kernel

private theorem fixed30 :
    checkPow (fixedTest Packed1.forward fullMask1) 30720 10 = true := by
  decide +kernel

private theorem fixed31 :
    checkPow (fixedTest Packed1.forward fullMask1) 31744 10 = true := by
  decide +kernel

private theorem fixed_complement :
    ∀ x : Fin 31671, (unionMasks masks1).testBit x.val = false → Packed1.forward x = x := by
  rw [mask_union]
  apply fixedTest_sound
  exact (checkPow_join (fixedTest Packed1.forward fullMask1) 14 0
    (checkPow_join (fixedTest Packed1.forward fullMask1) 13 0
    (checkPow_join (fixedTest Packed1.forward fullMask1) 12 0
    (checkPow_join (fixedTest Packed1.forward fullMask1) 11 0
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 0
    fixed0
    fixed1)
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 2048
    fixed2
    fixed3))
    (checkPow_join (fixedTest Packed1.forward fullMask1) 11 4096
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 4096
    fixed4
    fixed5)
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 6144
    fixed6
    fixed7)))
    (checkPow_join (fixedTest Packed1.forward fullMask1) 12 8192
    (checkPow_join (fixedTest Packed1.forward fullMask1) 11 8192
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 8192
    fixed8
    fixed9)
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 10240
    fixed10
    fixed11))
    (checkPow_join (fixedTest Packed1.forward fullMask1) 11 12288
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 12288
    fixed12
    fixed13)
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 14336
    fixed14
    fixed15))))
    (checkPow_join (fixedTest Packed1.forward fullMask1) 13 16384
    (checkPow_join (fixedTest Packed1.forward fullMask1) 12 16384
    (checkPow_join (fixedTest Packed1.forward fullMask1) 11 16384
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 16384
    fixed16
    fixed17)
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 18432
    fixed18
    fixed19))
    (checkPow_join (fixedTest Packed1.forward fullMask1) 11 20480
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 20480
    fixed20
    fixed21)
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 22528
    fixed22
    fixed23)))
    (checkPow_join (fixedTest Packed1.forward fullMask1) 12 24576
    (checkPow_join (fixedTest Packed1.forward fullMask1) 11 24576
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 24576
    fixed24
    fixed25)
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 26624
    fixed26
    fixed27))
    (checkPow_join (fixedTest Packed1.forward fullMask1) 11 28672
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 28672
    fixed28
    fixed29)
    (checkPow_join (fixedTest Packed1.forward fullMask1) 10 30720
    fixed30
    fixed31)))))

/-- Equality with the unchanged, literal inverse cycle product. -/
theorem permutation1_eq : Packed1.permutation = KernelData.generator1 := by
  apply Equiv.ext
  intro x
  exact map_eq_of_certificates Packed1.forward KernelData.cycleBlocks1
    parts1 masks1 decoded certificates disjoint actions fixed_complement x

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.GeneratorAgreement
