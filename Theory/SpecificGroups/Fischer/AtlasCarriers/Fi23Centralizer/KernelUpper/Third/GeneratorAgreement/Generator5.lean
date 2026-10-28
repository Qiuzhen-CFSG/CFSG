module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks5_0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks5_1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks5_2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks5_3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks5_4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks5_5

/-!
# The exact third-stage generator 5

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

private def parts5 : List (List (List (Fin 31671))) := [cycles5_0, cycles5_1, cycles5_2, cycles5_3, cycles5_4, cycles5_5, cycles5_6, cycles5_7, cycles5_8, cycles5_9, cycles5_10, cycles5_11, cycles5_12, cycles5_13, cycles5_14, cycles5_15, cycles5_16, cycles5_17, cycles5_18, cycles5_19, cycles5_20, cycles5_21, cycles5_22, cycles5_23, cycles5_24, cycles5_25, cycles5_26, cycles5_27, cycles5_28, cycles5_29, cycles5_30, cycles5_31, cycles5_32, cycles5_33, cycles5_34, cycles5_35, cycles5_36, cycles5_37, cycles5_38, cycles5_39, cycles5_40, cycles5_41, cycles5_42, cycles5_43, cycles5_44]
private def masks5 : List Nat := [mask5_0, mask5_1, mask5_2, mask5_3, mask5_4, mask5_5, mask5_6, mask5_7, mask5_8, mask5_9, mask5_10, mask5_11, mask5_12, mask5_13, mask5_14, mask5_15, mask5_16, mask5_17, mask5_18, mask5_19, mask5_20, mask5_21, mask5_22, mask5_23, mask5_24, mask5_25, mask5_26, mask5_27, mask5_28, mask5_29, mask5_30, mask5_31, mask5_32, mask5_33, mask5_34, mask5_35, mask5_36, mask5_37, mask5_38, mask5_39, mask5_40, mask5_41, mask5_42, mask5_43, mask5_44]
private def fullMask5 : Nat := 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfff7ffffffffffffffffffffffef7fffffffffffefffbffffbdffffbffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffff7ffdff8

private theorem decoded :
    decodeCycleBlocks 31671 KernelData.cycleBlocks5 = parts5.flatten := by
  apply decode_of_blocks
  exact (List.Forall₂.cons cycles5_0_spec (List.Forall₂.cons cycles5_1_spec (List.Forall₂.cons cycles5_2_spec (List.Forall₂.cons cycles5_3_spec (List.Forall₂.cons cycles5_4_spec (List.Forall₂.cons cycles5_5_spec (List.Forall₂.cons cycles5_6_spec (List.Forall₂.cons cycles5_7_spec (List.Forall₂.cons cycles5_8_spec (List.Forall₂.cons cycles5_9_spec (List.Forall₂.cons cycles5_10_spec (List.Forall₂.cons cycles5_11_spec (List.Forall₂.cons cycles5_12_spec (List.Forall₂.cons cycles5_13_spec (List.Forall₂.cons cycles5_14_spec (List.Forall₂.cons cycles5_15_spec (List.Forall₂.cons cycles5_16_spec (List.Forall₂.cons cycles5_17_spec (List.Forall₂.cons cycles5_18_spec (List.Forall₂.cons cycles5_19_spec (List.Forall₂.cons cycles5_20_spec (List.Forall₂.cons cycles5_21_spec (List.Forall₂.cons cycles5_22_spec (List.Forall₂.cons cycles5_23_spec (List.Forall₂.cons cycles5_24_spec (List.Forall₂.cons cycles5_25_spec (List.Forall₂.cons cycles5_26_spec (List.Forall₂.cons cycles5_27_spec (List.Forall₂.cons cycles5_28_spec (List.Forall₂.cons cycles5_29_spec (List.Forall₂.cons cycles5_30_spec (List.Forall₂.cons cycles5_31_spec (List.Forall₂.cons cycles5_32_spec (List.Forall₂.cons cycles5_33_spec (List.Forall₂.cons cycles5_34_spec (List.Forall₂.cons cycles5_35_spec (List.Forall₂.cons cycles5_36_spec (List.Forall₂.cons cycles5_37_spec (List.Forall₂.cons cycles5_38_spec (List.Forall₂.cons cycles5_39_spec (List.Forall₂.cons cycles5_40_spec (List.Forall₂.cons cycles5_41_spec (List.Forall₂.cons cycles5_42_spec (List.Forall₂.cons cycles5_43_spec (List.Forall₂.cons cycles5_44_spec List.Forall₂.nil)))))))))))))))))))))))))))))))))))))))))))))

private theorem certificates :
    List.Forall₂ (fun cs m => Certificate cs.flatten m) parts5 masks5 :=
  (List.Forall₂.cons certificate5_0 (List.Forall₂.cons certificate5_1 (List.Forall₂.cons certificate5_2 (List.Forall₂.cons certificate5_3 (List.Forall₂.cons certificate5_4 (List.Forall₂.cons certificate5_5 (List.Forall₂.cons certificate5_6 (List.Forall₂.cons certificate5_7 (List.Forall₂.cons certificate5_8 (List.Forall₂.cons certificate5_9 (List.Forall₂.cons certificate5_10 (List.Forall₂.cons certificate5_11 (List.Forall₂.cons certificate5_12 (List.Forall₂.cons certificate5_13 (List.Forall₂.cons certificate5_14 (List.Forall₂.cons certificate5_15 (List.Forall₂.cons certificate5_16 (List.Forall₂.cons certificate5_17 (List.Forall₂.cons certificate5_18 (List.Forall₂.cons certificate5_19 (List.Forall₂.cons certificate5_20 (List.Forall₂.cons certificate5_21 (List.Forall₂.cons certificate5_22 (List.Forall₂.cons certificate5_23 (List.Forall₂.cons certificate5_24 (List.Forall₂.cons certificate5_25 (List.Forall₂.cons certificate5_26 (List.Forall₂.cons certificate5_27 (List.Forall₂.cons certificate5_28 (List.Forall₂.cons certificate5_29 (List.Forall₂.cons certificate5_30 (List.Forall₂.cons certificate5_31 (List.Forall₂.cons certificate5_32 (List.Forall₂.cons certificate5_33 (List.Forall₂.cons certificate5_34 (List.Forall₂.cons certificate5_35 (List.Forall₂.cons certificate5_36 (List.Forall₂.cons certificate5_37 (List.Forall₂.cons certificate5_38 (List.Forall₂.cons certificate5_39 (List.Forall₂.cons certificate5_40 (List.Forall₂.cons certificate5_41 (List.Forall₂.cons certificate5_42 (List.Forall₂.cons certificate5_43 (List.Forall₂.cons certificate5_44 List.Forall₂.nil)))))))))))))))))))))))))))))))))))))))))))))

private theorem disjoint : disjointMasks masks5 = true := by decide +kernel

private theorem actions : parts5.all (cycleTest Packed5.forward) = true := by
  simp only [parts5, List.all_cons, List.all_nil, action5_0, action5_1, action5_2, action5_3, action5_4, action5_5, action5_6, action5_7, action5_8, action5_9, action5_10, action5_11, action5_12, action5_13, action5_14, action5_15, action5_16, action5_17, action5_18, action5_19, action5_20, action5_21, action5_22, action5_23, action5_24, action5_25, action5_26, action5_27, action5_28, action5_29, action5_30, action5_31, action5_32, action5_33, action5_34, action5_35, action5_36, action5_37, action5_38, action5_39, action5_40, action5_41, action5_42, action5_43, action5_44, Bool.and_self]

private theorem mask_union : unionMasks masks5 = fullMask5 := by decide +kernel

private theorem fixed0 :
    checkPow (fixedTest Packed5.forward fullMask5) 0 10 = true := by
  decide +kernel

private theorem fixed1 :
    checkPow (fixedTest Packed5.forward fullMask5) 1024 10 = true := by
  decide +kernel

private theorem fixed2 :
    checkPow (fixedTest Packed5.forward fullMask5) 2048 10 = true := by
  decide +kernel

private theorem fixed3 :
    checkPow (fixedTest Packed5.forward fullMask5) 3072 10 = true := by
  decide +kernel

private theorem fixed4 :
    checkPow (fixedTest Packed5.forward fullMask5) 4096 10 = true := by
  decide +kernel

private theorem fixed5 :
    checkPow (fixedTest Packed5.forward fullMask5) 5120 10 = true := by
  decide +kernel

private theorem fixed6 :
    checkPow (fixedTest Packed5.forward fullMask5) 6144 10 = true := by
  decide +kernel

private theorem fixed7 :
    checkPow (fixedTest Packed5.forward fullMask5) 7168 10 = true := by
  decide +kernel

private theorem fixed8 :
    checkPow (fixedTest Packed5.forward fullMask5) 8192 10 = true := by
  decide +kernel

private theorem fixed9 :
    checkPow (fixedTest Packed5.forward fullMask5) 9216 10 = true := by
  decide +kernel

private theorem fixed10 :
    checkPow (fixedTest Packed5.forward fullMask5) 10240 10 = true := by
  decide +kernel

private theorem fixed11 :
    checkPow (fixedTest Packed5.forward fullMask5) 11264 10 = true := by
  decide +kernel

private theorem fixed12 :
    checkPow (fixedTest Packed5.forward fullMask5) 12288 10 = true := by
  decide +kernel

private theorem fixed13 :
    checkPow (fixedTest Packed5.forward fullMask5) 13312 10 = true := by
  decide +kernel

private theorem fixed14 :
    checkPow (fixedTest Packed5.forward fullMask5) 14336 10 = true := by
  decide +kernel

private theorem fixed15 :
    checkPow (fixedTest Packed5.forward fullMask5) 15360 10 = true := by
  decide +kernel

private theorem fixed16 :
    checkPow (fixedTest Packed5.forward fullMask5) 16384 10 = true := by
  decide +kernel

private theorem fixed17 :
    checkPow (fixedTest Packed5.forward fullMask5) 17408 10 = true := by
  decide +kernel

private theorem fixed18 :
    checkPow (fixedTest Packed5.forward fullMask5) 18432 10 = true := by
  decide +kernel

private theorem fixed19 :
    checkPow (fixedTest Packed5.forward fullMask5) 19456 10 = true := by
  decide +kernel

private theorem fixed20 :
    checkPow (fixedTest Packed5.forward fullMask5) 20480 10 = true := by
  decide +kernel

private theorem fixed21 :
    checkPow (fixedTest Packed5.forward fullMask5) 21504 10 = true := by
  decide +kernel

private theorem fixed22 :
    checkPow (fixedTest Packed5.forward fullMask5) 22528 10 = true := by
  decide +kernel

private theorem fixed23 :
    checkPow (fixedTest Packed5.forward fullMask5) 23552 10 = true := by
  decide +kernel

private theorem fixed24 :
    checkPow (fixedTest Packed5.forward fullMask5) 24576 10 = true := by
  decide +kernel

private theorem fixed25 :
    checkPow (fixedTest Packed5.forward fullMask5) 25600 10 = true := by
  decide +kernel

private theorem fixed26 :
    checkPow (fixedTest Packed5.forward fullMask5) 26624 10 = true := by
  decide +kernel

private theorem fixed27 :
    checkPow (fixedTest Packed5.forward fullMask5) 27648 10 = true := by
  decide +kernel

private theorem fixed28 :
    checkPow (fixedTest Packed5.forward fullMask5) 28672 10 = true := by
  decide +kernel

private theorem fixed29 :
    checkPow (fixedTest Packed5.forward fullMask5) 29696 10 = true := by
  decide +kernel

private theorem fixed30 :
    checkPow (fixedTest Packed5.forward fullMask5) 30720 10 = true := by
  decide +kernel

private theorem fixed31 :
    checkPow (fixedTest Packed5.forward fullMask5) 31744 10 = true := by
  decide +kernel

private theorem fixed_complement :
    ∀ x : Fin 31671, (unionMasks masks5).testBit x.val = false → Packed5.forward x = x := by
  rw [mask_union]
  apply fixedTest_sound
  exact (checkPow_join (fixedTest Packed5.forward fullMask5) 14 0
    (checkPow_join (fixedTest Packed5.forward fullMask5) 13 0
    (checkPow_join (fixedTest Packed5.forward fullMask5) 12 0
    (checkPow_join (fixedTest Packed5.forward fullMask5) 11 0
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 0
    fixed0
    fixed1)
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 2048
    fixed2
    fixed3))
    (checkPow_join (fixedTest Packed5.forward fullMask5) 11 4096
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 4096
    fixed4
    fixed5)
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 6144
    fixed6
    fixed7)))
    (checkPow_join (fixedTest Packed5.forward fullMask5) 12 8192
    (checkPow_join (fixedTest Packed5.forward fullMask5) 11 8192
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 8192
    fixed8
    fixed9)
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 10240
    fixed10
    fixed11))
    (checkPow_join (fixedTest Packed5.forward fullMask5) 11 12288
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 12288
    fixed12
    fixed13)
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 14336
    fixed14
    fixed15))))
    (checkPow_join (fixedTest Packed5.forward fullMask5) 13 16384
    (checkPow_join (fixedTest Packed5.forward fullMask5) 12 16384
    (checkPow_join (fixedTest Packed5.forward fullMask5) 11 16384
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 16384
    fixed16
    fixed17)
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 18432
    fixed18
    fixed19))
    (checkPow_join (fixedTest Packed5.forward fullMask5) 11 20480
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 20480
    fixed20
    fixed21)
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 22528
    fixed22
    fixed23)))
    (checkPow_join (fixedTest Packed5.forward fullMask5) 12 24576
    (checkPow_join (fixedTest Packed5.forward fullMask5) 11 24576
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 24576
    fixed24
    fixed25)
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 26624
    fixed26
    fixed27))
    (checkPow_join (fixedTest Packed5.forward fullMask5) 11 28672
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 28672
    fixed28
    fixed29)
    (checkPow_join (fixedTest Packed5.forward fullMask5) 10 30720
    fixed30
    fixed31)))))

/-- Equality with the unchanged, literal inverse cycle product. -/
theorem permutation5_eq : Packed5.permutation = KernelData.generator5 := by
  apply Equiv.ext
  intro x
  exact map_eq_of_certificates Packed5.forward KernelData.cycleBlocks5
    parts5 masks5 decoded certificates disjoint actions fixed_complement x

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.GeneratorAgreement
