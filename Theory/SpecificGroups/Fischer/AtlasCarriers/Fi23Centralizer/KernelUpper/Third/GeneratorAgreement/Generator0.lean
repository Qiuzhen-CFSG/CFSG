module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks0_0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks0_1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks0_2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks0_3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks0_4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks0_5

/-!
# The exact third-stage generator 0

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

private def parts0 : List (List (List (Fin 31671))) := [cycles0_0, cycles0_1, cycles0_2, cycles0_3, cycles0_4, cycles0_5, cycles0_6, cycles0_7, cycles0_8, cycles0_9, cycles0_10, cycles0_11, cycles0_12, cycles0_13, cycles0_14, cycles0_15, cycles0_16, cycles0_17, cycles0_18, cycles0_19, cycles0_20, cycles0_21, cycles0_22, cycles0_23, cycles0_24, cycles0_25, cycles0_26, cycles0_27, cycles0_28, cycles0_29, cycles0_30, cycles0_31, cycles0_32, cycles0_33, cycles0_34, cycles0_35, cycles0_36, cycles0_37, cycles0_38, cycles0_39, cycles0_40, cycles0_41, cycles0_42, cycles0_43, cycles0_44]
private def masks0 : List Nat := [mask0_0, mask0_1, mask0_2, mask0_3, mask0_4, mask0_5, mask0_6, mask0_7, mask0_8, mask0_9, mask0_10, mask0_11, mask0_12, mask0_13, mask0_14, mask0_15, mask0_16, mask0_17, mask0_18, mask0_19, mask0_20, mask0_21, mask0_22, mask0_23, mask0_24, mask0_25, mask0_26, mask0_27, mask0_28, mask0_29, mask0_30, mask0_31, mask0_32, mask0_33, mask0_34, mask0_35, mask0_36, mask0_37, mask0_38, mask0_39, mask0_40, mask0_41, mask0_42, mask0_43, mask0_44]
private def fullMask0 : Nat := 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000003807ffffff0000000

private theorem decoded :
    decodeCycleBlocks 31671 KernelData.cycleBlocks0 = parts0.flatten := by
  apply decode_of_blocks
  exact (List.Forall₂.cons cycles0_0_spec (List.Forall₂.cons cycles0_1_spec (List.Forall₂.cons cycles0_2_spec (List.Forall₂.cons cycles0_3_spec (List.Forall₂.cons cycles0_4_spec (List.Forall₂.cons cycles0_5_spec (List.Forall₂.cons cycles0_6_spec (List.Forall₂.cons cycles0_7_spec (List.Forall₂.cons cycles0_8_spec (List.Forall₂.cons cycles0_9_spec (List.Forall₂.cons cycles0_10_spec (List.Forall₂.cons cycles0_11_spec (List.Forall₂.cons cycles0_12_spec (List.Forall₂.cons cycles0_13_spec (List.Forall₂.cons cycles0_14_spec (List.Forall₂.cons cycles0_15_spec (List.Forall₂.cons cycles0_16_spec (List.Forall₂.cons cycles0_17_spec (List.Forall₂.cons cycles0_18_spec (List.Forall₂.cons cycles0_19_spec (List.Forall₂.cons cycles0_20_spec (List.Forall₂.cons cycles0_21_spec (List.Forall₂.cons cycles0_22_spec (List.Forall₂.cons cycles0_23_spec (List.Forall₂.cons cycles0_24_spec (List.Forall₂.cons cycles0_25_spec (List.Forall₂.cons cycles0_26_spec (List.Forall₂.cons cycles0_27_spec (List.Forall₂.cons cycles0_28_spec (List.Forall₂.cons cycles0_29_spec (List.Forall₂.cons cycles0_30_spec (List.Forall₂.cons cycles0_31_spec (List.Forall₂.cons cycles0_32_spec (List.Forall₂.cons cycles0_33_spec (List.Forall₂.cons cycles0_34_spec (List.Forall₂.cons cycles0_35_spec (List.Forall₂.cons cycles0_36_spec (List.Forall₂.cons cycles0_37_spec (List.Forall₂.cons cycles0_38_spec (List.Forall₂.cons cycles0_39_spec (List.Forall₂.cons cycles0_40_spec (List.Forall₂.cons cycles0_41_spec (List.Forall₂.cons cycles0_42_spec (List.Forall₂.cons cycles0_43_spec (List.Forall₂.cons cycles0_44_spec List.Forall₂.nil)))))))))))))))))))))))))))))))))))))))))))))

private theorem certificates :
    List.Forall₂ (fun cs m => Certificate cs.flatten m) parts0 masks0 :=
  (List.Forall₂.cons certificate0_0 (List.Forall₂.cons certificate0_1 (List.Forall₂.cons certificate0_2 (List.Forall₂.cons certificate0_3 (List.Forall₂.cons certificate0_4 (List.Forall₂.cons certificate0_5 (List.Forall₂.cons certificate0_6 (List.Forall₂.cons certificate0_7 (List.Forall₂.cons certificate0_8 (List.Forall₂.cons certificate0_9 (List.Forall₂.cons certificate0_10 (List.Forall₂.cons certificate0_11 (List.Forall₂.cons certificate0_12 (List.Forall₂.cons certificate0_13 (List.Forall₂.cons certificate0_14 (List.Forall₂.cons certificate0_15 (List.Forall₂.cons certificate0_16 (List.Forall₂.cons certificate0_17 (List.Forall₂.cons certificate0_18 (List.Forall₂.cons certificate0_19 (List.Forall₂.cons certificate0_20 (List.Forall₂.cons certificate0_21 (List.Forall₂.cons certificate0_22 (List.Forall₂.cons certificate0_23 (List.Forall₂.cons certificate0_24 (List.Forall₂.cons certificate0_25 (List.Forall₂.cons certificate0_26 (List.Forall₂.cons certificate0_27 (List.Forall₂.cons certificate0_28 (List.Forall₂.cons certificate0_29 (List.Forall₂.cons certificate0_30 (List.Forall₂.cons certificate0_31 (List.Forall₂.cons certificate0_32 (List.Forall₂.cons certificate0_33 (List.Forall₂.cons certificate0_34 (List.Forall₂.cons certificate0_35 (List.Forall₂.cons certificate0_36 (List.Forall₂.cons certificate0_37 (List.Forall₂.cons certificate0_38 (List.Forall₂.cons certificate0_39 (List.Forall₂.cons certificate0_40 (List.Forall₂.cons certificate0_41 (List.Forall₂.cons certificate0_42 (List.Forall₂.cons certificate0_43 (List.Forall₂.cons certificate0_44 List.Forall₂.nil)))))))))))))))))))))))))))))))))))))))))))))

private theorem disjoint : disjointMasks masks0 = true := by decide +kernel

private theorem actions : parts0.all (cycleTest Packed0.forward) = true := by
  simp only [parts0, List.all_cons, List.all_nil, action0_0, action0_1, action0_2, action0_3, action0_4, action0_5, action0_6, action0_7, action0_8, action0_9, action0_10, action0_11, action0_12, action0_13, action0_14, action0_15, action0_16, action0_17, action0_18, action0_19, action0_20, action0_21, action0_22, action0_23, action0_24, action0_25, action0_26, action0_27, action0_28, action0_29, action0_30, action0_31, action0_32, action0_33, action0_34, action0_35, action0_36, action0_37, action0_38, action0_39, action0_40, action0_41, action0_42, action0_43, action0_44, Bool.and_self]

private theorem mask_union : unionMasks masks0 = fullMask0 := by decide +kernel

private theorem fixed0 :
    checkPow (fixedTest Packed0.forward fullMask0) 0 10 = true := by
  decide +kernel

private theorem fixed1 :
    checkPow (fixedTest Packed0.forward fullMask0) 1024 10 = true := by
  decide +kernel

private theorem fixed2 :
    checkPow (fixedTest Packed0.forward fullMask0) 2048 10 = true := by
  decide +kernel

private theorem fixed3 :
    checkPow (fixedTest Packed0.forward fullMask0) 3072 10 = true := by
  decide +kernel

private theorem fixed4 :
    checkPow (fixedTest Packed0.forward fullMask0) 4096 10 = true := by
  decide +kernel

private theorem fixed5 :
    checkPow (fixedTest Packed0.forward fullMask0) 5120 10 = true := by
  decide +kernel

private theorem fixed6 :
    checkPow (fixedTest Packed0.forward fullMask0) 6144 10 = true := by
  decide +kernel

private theorem fixed7 :
    checkPow (fixedTest Packed0.forward fullMask0) 7168 10 = true := by
  decide +kernel

private theorem fixed8 :
    checkPow (fixedTest Packed0.forward fullMask0) 8192 10 = true := by
  decide +kernel

private theorem fixed9 :
    checkPow (fixedTest Packed0.forward fullMask0) 9216 10 = true := by
  decide +kernel

private theorem fixed10 :
    checkPow (fixedTest Packed0.forward fullMask0) 10240 10 = true := by
  decide +kernel

private theorem fixed11 :
    checkPow (fixedTest Packed0.forward fullMask0) 11264 10 = true := by
  decide +kernel

private theorem fixed12 :
    checkPow (fixedTest Packed0.forward fullMask0) 12288 10 = true := by
  decide +kernel

private theorem fixed13 :
    checkPow (fixedTest Packed0.forward fullMask0) 13312 10 = true := by
  decide +kernel

private theorem fixed14 :
    checkPow (fixedTest Packed0.forward fullMask0) 14336 10 = true := by
  decide +kernel

private theorem fixed15 :
    checkPow (fixedTest Packed0.forward fullMask0) 15360 10 = true := by
  decide +kernel

private theorem fixed16 :
    checkPow (fixedTest Packed0.forward fullMask0) 16384 10 = true := by
  decide +kernel

private theorem fixed17 :
    checkPow (fixedTest Packed0.forward fullMask0) 17408 10 = true := by
  decide +kernel

private theorem fixed18 :
    checkPow (fixedTest Packed0.forward fullMask0) 18432 10 = true := by
  decide +kernel

private theorem fixed19 :
    checkPow (fixedTest Packed0.forward fullMask0) 19456 10 = true := by
  decide +kernel

private theorem fixed20 :
    checkPow (fixedTest Packed0.forward fullMask0) 20480 10 = true := by
  decide +kernel

private theorem fixed21 :
    checkPow (fixedTest Packed0.forward fullMask0) 21504 10 = true := by
  decide +kernel

private theorem fixed22 :
    checkPow (fixedTest Packed0.forward fullMask0) 22528 10 = true := by
  decide +kernel

private theorem fixed23 :
    checkPow (fixedTest Packed0.forward fullMask0) 23552 10 = true := by
  decide +kernel

private theorem fixed24 :
    checkPow (fixedTest Packed0.forward fullMask0) 24576 10 = true := by
  decide +kernel

private theorem fixed25 :
    checkPow (fixedTest Packed0.forward fullMask0) 25600 10 = true := by
  decide +kernel

private theorem fixed26 :
    checkPow (fixedTest Packed0.forward fullMask0) 26624 10 = true := by
  decide +kernel

private theorem fixed27 :
    checkPow (fixedTest Packed0.forward fullMask0) 27648 10 = true := by
  decide +kernel

private theorem fixed28 :
    checkPow (fixedTest Packed0.forward fullMask0) 28672 10 = true := by
  decide +kernel

private theorem fixed29 :
    checkPow (fixedTest Packed0.forward fullMask0) 29696 10 = true := by
  decide +kernel

private theorem fixed30 :
    checkPow (fixedTest Packed0.forward fullMask0) 30720 10 = true := by
  decide +kernel

private theorem fixed31 :
    checkPow (fixedTest Packed0.forward fullMask0) 31744 10 = true := by
  decide +kernel

private theorem fixed_complement :
    ∀ x : Fin 31671, (unionMasks masks0).testBit x.val = false → Packed0.forward x = x := by
  rw [mask_union]
  apply fixedTest_sound
  exact (checkPow_join (fixedTest Packed0.forward fullMask0) 14 0
    (checkPow_join (fixedTest Packed0.forward fullMask0) 13 0
    (checkPow_join (fixedTest Packed0.forward fullMask0) 12 0
    (checkPow_join (fixedTest Packed0.forward fullMask0) 11 0
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 0
    fixed0
    fixed1)
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 2048
    fixed2
    fixed3))
    (checkPow_join (fixedTest Packed0.forward fullMask0) 11 4096
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 4096
    fixed4
    fixed5)
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 6144
    fixed6
    fixed7)))
    (checkPow_join (fixedTest Packed0.forward fullMask0) 12 8192
    (checkPow_join (fixedTest Packed0.forward fullMask0) 11 8192
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 8192
    fixed8
    fixed9)
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 10240
    fixed10
    fixed11))
    (checkPow_join (fixedTest Packed0.forward fullMask0) 11 12288
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 12288
    fixed12
    fixed13)
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 14336
    fixed14
    fixed15))))
    (checkPow_join (fixedTest Packed0.forward fullMask0) 13 16384
    (checkPow_join (fixedTest Packed0.forward fullMask0) 12 16384
    (checkPow_join (fixedTest Packed0.forward fullMask0) 11 16384
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 16384
    fixed16
    fixed17)
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 18432
    fixed18
    fixed19))
    (checkPow_join (fixedTest Packed0.forward fullMask0) 11 20480
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 20480
    fixed20
    fixed21)
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 22528
    fixed22
    fixed23)))
    (checkPow_join (fixedTest Packed0.forward fullMask0) 12 24576
    (checkPow_join (fixedTest Packed0.forward fullMask0) 11 24576
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 24576
    fixed24
    fixed25)
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 26624
    fixed26
    fixed27))
    (checkPow_join (fixedTest Packed0.forward fullMask0) 11 28672
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 28672
    fixed28
    fixed29)
    (checkPow_join (fixedTest Packed0.forward fullMask0) 10 30720
    fixed30
    fixed31)))))

/-- Equality with the unchanged, literal inverse cycle product. -/
theorem permutation0_eq : Packed0.permutation = KernelData.generator0 := by
  apply Equiv.ext
  intro x
  exact map_eq_of_certificates Packed0.forward KernelData.cycleBlocks0
    parts0 masks0 decoded certificates disjoint actions fixed_complement x

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.GeneratorAgreement
