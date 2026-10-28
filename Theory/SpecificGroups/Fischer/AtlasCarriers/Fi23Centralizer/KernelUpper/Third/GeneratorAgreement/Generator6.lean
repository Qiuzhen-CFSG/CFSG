module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks6_0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks6_1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks6_2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks6_3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks6_4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks6_5

/-!
# The exact third-stage generator 6

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

private def parts6 : List (List (List (Fin 31671))) := [cycles6_0, cycles6_1, cycles6_2, cycles6_3, cycles6_4, cycles6_5, cycles6_6, cycles6_7, cycles6_8, cycles6_9, cycles6_10, cycles6_11, cycles6_12, cycles6_13, cycles6_14, cycles6_15, cycles6_16, cycles6_17, cycles6_18, cycles6_19, cycles6_20, cycles6_21, cycles6_22, cycles6_23, cycles6_24, cycles6_25, cycles6_26, cycles6_27, cycles6_28, cycles6_29, cycles6_30, cycles6_31, cycles6_32, cycles6_33, cycles6_34, cycles6_35, cycles6_36, cycles6_37, cycles6_38, cycles6_39, cycles6_40, cycles6_41, cycles6_42, cycles6_43, cycles6_44, cycles6_45]
private def masks6 : List Nat := [mask6_0, mask6_1, mask6_2, mask6_3, mask6_4, mask6_5, mask6_6, mask6_7, mask6_8, mask6_9, mask6_10, mask6_11, mask6_12, mask6_13, mask6_14, mask6_15, mask6_16, mask6_17, mask6_18, mask6_19, mask6_20, mask6_21, mask6_22, mask6_23, mask6_24, mask6_25, mask6_26, mask6_27, mask6_28, mask6_29, mask6_30, mask6_31, mask6_32, mask6_33, mask6_34, mask6_35, mask6_36, mask6_37, mask6_38, mask6_39, mask6_40, mask6_41, mask6_42, mask6_43, mask6_44, mask6_45]
private def fullMask6 : Nat := 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffebfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffdffd

private theorem decoded :
    decodeCycleBlocks 31671 KernelData.cycleBlocks6 = parts6.flatten := by
  apply decode_of_blocks
  exact (List.Forall₂.cons cycles6_0_spec (List.Forall₂.cons cycles6_1_spec (List.Forall₂.cons cycles6_2_spec (List.Forall₂.cons cycles6_3_spec (List.Forall₂.cons cycles6_4_spec (List.Forall₂.cons cycles6_5_spec (List.Forall₂.cons cycles6_6_spec (List.Forall₂.cons cycles6_7_spec (List.Forall₂.cons cycles6_8_spec (List.Forall₂.cons cycles6_9_spec (List.Forall₂.cons cycles6_10_spec (List.Forall₂.cons cycles6_11_spec (List.Forall₂.cons cycles6_12_spec (List.Forall₂.cons cycles6_13_spec (List.Forall₂.cons cycles6_14_spec (List.Forall₂.cons cycles6_15_spec (List.Forall₂.cons cycles6_16_spec (List.Forall₂.cons cycles6_17_spec (List.Forall₂.cons cycles6_18_spec (List.Forall₂.cons cycles6_19_spec (List.Forall₂.cons cycles6_20_spec (List.Forall₂.cons cycles6_21_spec (List.Forall₂.cons cycles6_22_spec (List.Forall₂.cons cycles6_23_spec (List.Forall₂.cons cycles6_24_spec (List.Forall₂.cons cycles6_25_spec (List.Forall₂.cons cycles6_26_spec (List.Forall₂.cons cycles6_27_spec (List.Forall₂.cons cycles6_28_spec (List.Forall₂.cons cycles6_29_spec (List.Forall₂.cons cycles6_30_spec (List.Forall₂.cons cycles6_31_spec (List.Forall₂.cons cycles6_32_spec (List.Forall₂.cons cycles6_33_spec (List.Forall₂.cons cycles6_34_spec (List.Forall₂.cons cycles6_35_spec (List.Forall₂.cons cycles6_36_spec (List.Forall₂.cons cycles6_37_spec (List.Forall₂.cons cycles6_38_spec (List.Forall₂.cons cycles6_39_spec (List.Forall₂.cons cycles6_40_spec (List.Forall₂.cons cycles6_41_spec (List.Forall₂.cons cycles6_42_spec (List.Forall₂.cons cycles6_43_spec (List.Forall₂.cons cycles6_44_spec (List.Forall₂.cons cycles6_45_spec List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))

private theorem certificates :
    List.Forall₂ (fun cs m => Certificate cs.flatten m) parts6 masks6 :=
  (List.Forall₂.cons certificate6_0 (List.Forall₂.cons certificate6_1 (List.Forall₂.cons certificate6_2 (List.Forall₂.cons certificate6_3 (List.Forall₂.cons certificate6_4 (List.Forall₂.cons certificate6_5 (List.Forall₂.cons certificate6_6 (List.Forall₂.cons certificate6_7 (List.Forall₂.cons certificate6_8 (List.Forall₂.cons certificate6_9 (List.Forall₂.cons certificate6_10 (List.Forall₂.cons certificate6_11 (List.Forall₂.cons certificate6_12 (List.Forall₂.cons certificate6_13 (List.Forall₂.cons certificate6_14 (List.Forall₂.cons certificate6_15 (List.Forall₂.cons certificate6_16 (List.Forall₂.cons certificate6_17 (List.Forall₂.cons certificate6_18 (List.Forall₂.cons certificate6_19 (List.Forall₂.cons certificate6_20 (List.Forall₂.cons certificate6_21 (List.Forall₂.cons certificate6_22 (List.Forall₂.cons certificate6_23 (List.Forall₂.cons certificate6_24 (List.Forall₂.cons certificate6_25 (List.Forall₂.cons certificate6_26 (List.Forall₂.cons certificate6_27 (List.Forall₂.cons certificate6_28 (List.Forall₂.cons certificate6_29 (List.Forall₂.cons certificate6_30 (List.Forall₂.cons certificate6_31 (List.Forall₂.cons certificate6_32 (List.Forall₂.cons certificate6_33 (List.Forall₂.cons certificate6_34 (List.Forall₂.cons certificate6_35 (List.Forall₂.cons certificate6_36 (List.Forall₂.cons certificate6_37 (List.Forall₂.cons certificate6_38 (List.Forall₂.cons certificate6_39 (List.Forall₂.cons certificate6_40 (List.Forall₂.cons certificate6_41 (List.Forall₂.cons certificate6_42 (List.Forall₂.cons certificate6_43 (List.Forall₂.cons certificate6_44 (List.Forall₂.cons certificate6_45 List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))

private theorem disjoint : disjointMasks masks6 = true := by decide +kernel

private theorem actions : parts6.all (cycleTest Packed6.forward) = true := by
  simp only [parts6, List.all_cons, List.all_nil, action6_0, action6_1, action6_2, action6_3, action6_4, action6_5, action6_6, action6_7, action6_8, action6_9, action6_10, action6_11, action6_12, action6_13, action6_14, action6_15, action6_16, action6_17, action6_18, action6_19, action6_20, action6_21, action6_22, action6_23, action6_24, action6_25, action6_26, action6_27, action6_28, action6_29, action6_30, action6_31, action6_32, action6_33, action6_34, action6_35, action6_36, action6_37, action6_38, action6_39, action6_40, action6_41, action6_42, action6_43, action6_44, action6_45, Bool.and_self]

private theorem mask_union : unionMasks masks6 = fullMask6 := by decide +kernel

private theorem fixed0 :
    checkPow (fixedTest Packed6.forward fullMask6) 0 10 = true := by
  decide +kernel

private theorem fixed1 :
    checkPow (fixedTest Packed6.forward fullMask6) 1024 10 = true := by
  decide +kernel

private theorem fixed2 :
    checkPow (fixedTest Packed6.forward fullMask6) 2048 10 = true := by
  decide +kernel

private theorem fixed3 :
    checkPow (fixedTest Packed6.forward fullMask6) 3072 10 = true := by
  decide +kernel

private theorem fixed4 :
    checkPow (fixedTest Packed6.forward fullMask6) 4096 10 = true := by
  decide +kernel

private theorem fixed5 :
    checkPow (fixedTest Packed6.forward fullMask6) 5120 10 = true := by
  decide +kernel

private theorem fixed6 :
    checkPow (fixedTest Packed6.forward fullMask6) 6144 10 = true := by
  decide +kernel

private theorem fixed7 :
    checkPow (fixedTest Packed6.forward fullMask6) 7168 10 = true := by
  decide +kernel

private theorem fixed8 :
    checkPow (fixedTest Packed6.forward fullMask6) 8192 10 = true := by
  decide +kernel

private theorem fixed9 :
    checkPow (fixedTest Packed6.forward fullMask6) 9216 10 = true := by
  decide +kernel

private theorem fixed10 :
    checkPow (fixedTest Packed6.forward fullMask6) 10240 10 = true := by
  decide +kernel

private theorem fixed11 :
    checkPow (fixedTest Packed6.forward fullMask6) 11264 10 = true := by
  decide +kernel

private theorem fixed12 :
    checkPow (fixedTest Packed6.forward fullMask6) 12288 10 = true := by
  decide +kernel

private theorem fixed13 :
    checkPow (fixedTest Packed6.forward fullMask6) 13312 10 = true := by
  decide +kernel

private theorem fixed14 :
    checkPow (fixedTest Packed6.forward fullMask6) 14336 10 = true := by
  decide +kernel

private theorem fixed15 :
    checkPow (fixedTest Packed6.forward fullMask6) 15360 10 = true := by
  decide +kernel

private theorem fixed16 :
    checkPow (fixedTest Packed6.forward fullMask6) 16384 10 = true := by
  decide +kernel

private theorem fixed17 :
    checkPow (fixedTest Packed6.forward fullMask6) 17408 10 = true := by
  decide +kernel

private theorem fixed18 :
    checkPow (fixedTest Packed6.forward fullMask6) 18432 10 = true := by
  decide +kernel

private theorem fixed19 :
    checkPow (fixedTest Packed6.forward fullMask6) 19456 10 = true := by
  decide +kernel

private theorem fixed20 :
    checkPow (fixedTest Packed6.forward fullMask6) 20480 10 = true := by
  decide +kernel

private theorem fixed21 :
    checkPow (fixedTest Packed6.forward fullMask6) 21504 10 = true := by
  decide +kernel

private theorem fixed22 :
    checkPow (fixedTest Packed6.forward fullMask6) 22528 10 = true := by
  decide +kernel

private theorem fixed23 :
    checkPow (fixedTest Packed6.forward fullMask6) 23552 10 = true := by
  decide +kernel

private theorem fixed24 :
    checkPow (fixedTest Packed6.forward fullMask6) 24576 10 = true := by
  decide +kernel

private theorem fixed25 :
    checkPow (fixedTest Packed6.forward fullMask6) 25600 10 = true := by
  decide +kernel

private theorem fixed26 :
    checkPow (fixedTest Packed6.forward fullMask6) 26624 10 = true := by
  decide +kernel

private theorem fixed27 :
    checkPow (fixedTest Packed6.forward fullMask6) 27648 10 = true := by
  decide +kernel

private theorem fixed28 :
    checkPow (fixedTest Packed6.forward fullMask6) 28672 10 = true := by
  decide +kernel

private theorem fixed29 :
    checkPow (fixedTest Packed6.forward fullMask6) 29696 10 = true := by
  decide +kernel

private theorem fixed30 :
    checkPow (fixedTest Packed6.forward fullMask6) 30720 10 = true := by
  decide +kernel

private theorem fixed31 :
    checkPow (fixedTest Packed6.forward fullMask6) 31744 10 = true := by
  decide +kernel

private theorem fixed_complement :
    ∀ x : Fin 31671, (unionMasks masks6).testBit x.val = false → Packed6.forward x = x := by
  rw [mask_union]
  apply fixedTest_sound
  exact (checkPow_join (fixedTest Packed6.forward fullMask6) 14 0
    (checkPow_join (fixedTest Packed6.forward fullMask6) 13 0
    (checkPow_join (fixedTest Packed6.forward fullMask6) 12 0
    (checkPow_join (fixedTest Packed6.forward fullMask6) 11 0
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 0
    fixed0
    fixed1)
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 2048
    fixed2
    fixed3))
    (checkPow_join (fixedTest Packed6.forward fullMask6) 11 4096
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 4096
    fixed4
    fixed5)
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 6144
    fixed6
    fixed7)))
    (checkPow_join (fixedTest Packed6.forward fullMask6) 12 8192
    (checkPow_join (fixedTest Packed6.forward fullMask6) 11 8192
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 8192
    fixed8
    fixed9)
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 10240
    fixed10
    fixed11))
    (checkPow_join (fixedTest Packed6.forward fullMask6) 11 12288
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 12288
    fixed12
    fixed13)
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 14336
    fixed14
    fixed15))))
    (checkPow_join (fixedTest Packed6.forward fullMask6) 13 16384
    (checkPow_join (fixedTest Packed6.forward fullMask6) 12 16384
    (checkPow_join (fixedTest Packed6.forward fullMask6) 11 16384
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 16384
    fixed16
    fixed17)
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 18432
    fixed18
    fixed19))
    (checkPow_join (fixedTest Packed6.forward fullMask6) 11 20480
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 20480
    fixed20
    fixed21)
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 22528
    fixed22
    fixed23)))
    (checkPow_join (fixedTest Packed6.forward fullMask6) 12 24576
    (checkPow_join (fixedTest Packed6.forward fullMask6) 11 24576
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 24576
    fixed24
    fixed25)
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 26624
    fixed26
    fixed27))
    (checkPow_join (fixedTest Packed6.forward fullMask6) 11 28672
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 28672
    fixed28
    fixed29)
    (checkPow_join (fixedTest Packed6.forward fullMask6) 10 30720
    fixed30
    fixed31)))))

/-- Equality with the unchanged, literal inverse cycle product. -/
theorem permutation6_eq : Packed6.permutation = KernelData.generator6 := by
  apply Equiv.ext
  intro x
  exact map_eq_of_certificates Packed6.forward KernelData.cycleBlocks6
    parts6 masks6 decoded certificates disjoint actions fixed_complement x

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.GeneratorAgreement
