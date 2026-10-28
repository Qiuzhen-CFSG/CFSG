module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks4_0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks4_1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks4_2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks4_3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks4_4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Blocks4_5

/-!
# The exact third-stage generator 4

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

private def parts4 : List (List (List (Fin 31671))) := [cycles4_0, cycles4_1, cycles4_2, cycles4_3, cycles4_4, cycles4_5, cycles4_6, cycles4_7, cycles4_8, cycles4_9, cycles4_10, cycles4_11, cycles4_12, cycles4_13, cycles4_14, cycles4_15, cycles4_16, cycles4_17, cycles4_18, cycles4_19, cycles4_20, cycles4_21, cycles4_22, cycles4_23, cycles4_24, cycles4_25, cycles4_26, cycles4_27, cycles4_28, cycles4_29, cycles4_30, cycles4_31, cycles4_32, cycles4_33, cycles4_34, cycles4_35, cycles4_36, cycles4_37, cycles4_38, cycles4_39, cycles4_40, cycles4_41, cycles4_42, cycles4_43, cycles4_44]
private def masks4 : List Nat := [mask4_0, mask4_1, mask4_2, mask4_3, mask4_4, mask4_5, mask4_6, mask4_7, mask4_8, mask4_9, mask4_10, mask4_11, mask4_12, mask4_13, mask4_14, mask4_15, mask4_16, mask4_17, mask4_18, mask4_19, mask4_20, mask4_21, mask4_22, mask4_23, mask4_24, mask4_25, mask4_26, mask4_27, mask4_28, mask4_29, mask4_30, mask4_31, mask4_32, mask4_33, mask4_34, mask4_35, mask4_36, mask4_37, mask4_38, mask4_39, mask4_40, mask4_41, mask4_42, mask4_43, mask4_44]
private def fullMask4 : Nat := 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff20843c0

private theorem decoded :
    decodeCycleBlocks 31671 KernelData.cycleBlocks4 = parts4.flatten := by
  apply decode_of_blocks
  exact (List.Forall₂.cons cycles4_0_spec (List.Forall₂.cons cycles4_1_spec (List.Forall₂.cons cycles4_2_spec (List.Forall₂.cons cycles4_3_spec (List.Forall₂.cons cycles4_4_spec (List.Forall₂.cons cycles4_5_spec (List.Forall₂.cons cycles4_6_spec (List.Forall₂.cons cycles4_7_spec (List.Forall₂.cons cycles4_8_spec (List.Forall₂.cons cycles4_9_spec (List.Forall₂.cons cycles4_10_spec (List.Forall₂.cons cycles4_11_spec (List.Forall₂.cons cycles4_12_spec (List.Forall₂.cons cycles4_13_spec (List.Forall₂.cons cycles4_14_spec (List.Forall₂.cons cycles4_15_spec (List.Forall₂.cons cycles4_16_spec (List.Forall₂.cons cycles4_17_spec (List.Forall₂.cons cycles4_18_spec (List.Forall₂.cons cycles4_19_spec (List.Forall₂.cons cycles4_20_spec (List.Forall₂.cons cycles4_21_spec (List.Forall₂.cons cycles4_22_spec (List.Forall₂.cons cycles4_23_spec (List.Forall₂.cons cycles4_24_spec (List.Forall₂.cons cycles4_25_spec (List.Forall₂.cons cycles4_26_spec (List.Forall₂.cons cycles4_27_spec (List.Forall₂.cons cycles4_28_spec (List.Forall₂.cons cycles4_29_spec (List.Forall₂.cons cycles4_30_spec (List.Forall₂.cons cycles4_31_spec (List.Forall₂.cons cycles4_32_spec (List.Forall₂.cons cycles4_33_spec (List.Forall₂.cons cycles4_34_spec (List.Forall₂.cons cycles4_35_spec (List.Forall₂.cons cycles4_36_spec (List.Forall₂.cons cycles4_37_spec (List.Forall₂.cons cycles4_38_spec (List.Forall₂.cons cycles4_39_spec (List.Forall₂.cons cycles4_40_spec (List.Forall₂.cons cycles4_41_spec (List.Forall₂.cons cycles4_42_spec (List.Forall₂.cons cycles4_43_spec (List.Forall₂.cons cycles4_44_spec List.Forall₂.nil)))))))))))))))))))))))))))))))))))))))))))))

private theorem certificates :
    List.Forall₂ (fun cs m => Certificate cs.flatten m) parts4 masks4 :=
  (List.Forall₂.cons certificate4_0 (List.Forall₂.cons certificate4_1 (List.Forall₂.cons certificate4_2 (List.Forall₂.cons certificate4_3 (List.Forall₂.cons certificate4_4 (List.Forall₂.cons certificate4_5 (List.Forall₂.cons certificate4_6 (List.Forall₂.cons certificate4_7 (List.Forall₂.cons certificate4_8 (List.Forall₂.cons certificate4_9 (List.Forall₂.cons certificate4_10 (List.Forall₂.cons certificate4_11 (List.Forall₂.cons certificate4_12 (List.Forall₂.cons certificate4_13 (List.Forall₂.cons certificate4_14 (List.Forall₂.cons certificate4_15 (List.Forall₂.cons certificate4_16 (List.Forall₂.cons certificate4_17 (List.Forall₂.cons certificate4_18 (List.Forall₂.cons certificate4_19 (List.Forall₂.cons certificate4_20 (List.Forall₂.cons certificate4_21 (List.Forall₂.cons certificate4_22 (List.Forall₂.cons certificate4_23 (List.Forall₂.cons certificate4_24 (List.Forall₂.cons certificate4_25 (List.Forall₂.cons certificate4_26 (List.Forall₂.cons certificate4_27 (List.Forall₂.cons certificate4_28 (List.Forall₂.cons certificate4_29 (List.Forall₂.cons certificate4_30 (List.Forall₂.cons certificate4_31 (List.Forall₂.cons certificate4_32 (List.Forall₂.cons certificate4_33 (List.Forall₂.cons certificate4_34 (List.Forall₂.cons certificate4_35 (List.Forall₂.cons certificate4_36 (List.Forall₂.cons certificate4_37 (List.Forall₂.cons certificate4_38 (List.Forall₂.cons certificate4_39 (List.Forall₂.cons certificate4_40 (List.Forall₂.cons certificate4_41 (List.Forall₂.cons certificate4_42 (List.Forall₂.cons certificate4_43 (List.Forall₂.cons certificate4_44 List.Forall₂.nil)))))))))))))))))))))))))))))))))))))))))))))

private theorem disjoint : disjointMasks masks4 = true := by decide +kernel

private theorem actions : parts4.all (cycleTest Packed4.forward) = true := by
  simp only [parts4, List.all_cons, List.all_nil, action4_0, action4_1, action4_2, action4_3, action4_4, action4_5, action4_6, action4_7, action4_8, action4_9, action4_10, action4_11, action4_12, action4_13, action4_14, action4_15, action4_16, action4_17, action4_18, action4_19, action4_20, action4_21, action4_22, action4_23, action4_24, action4_25, action4_26, action4_27, action4_28, action4_29, action4_30, action4_31, action4_32, action4_33, action4_34, action4_35, action4_36, action4_37, action4_38, action4_39, action4_40, action4_41, action4_42, action4_43, action4_44, Bool.and_self]

private theorem mask_union : unionMasks masks4 = fullMask4 := by decide +kernel

private theorem fixed0 :
    checkPow (fixedTest Packed4.forward fullMask4) 0 10 = true := by
  decide +kernel

private theorem fixed1 :
    checkPow (fixedTest Packed4.forward fullMask4) 1024 10 = true := by
  decide +kernel

private theorem fixed2 :
    checkPow (fixedTest Packed4.forward fullMask4) 2048 10 = true := by
  decide +kernel

private theorem fixed3 :
    checkPow (fixedTest Packed4.forward fullMask4) 3072 10 = true := by
  decide +kernel

private theorem fixed4 :
    checkPow (fixedTest Packed4.forward fullMask4) 4096 10 = true := by
  decide +kernel

private theorem fixed5 :
    checkPow (fixedTest Packed4.forward fullMask4) 5120 10 = true := by
  decide +kernel

private theorem fixed6 :
    checkPow (fixedTest Packed4.forward fullMask4) 6144 10 = true := by
  decide +kernel

private theorem fixed7 :
    checkPow (fixedTest Packed4.forward fullMask4) 7168 10 = true := by
  decide +kernel

private theorem fixed8 :
    checkPow (fixedTest Packed4.forward fullMask4) 8192 10 = true := by
  decide +kernel

private theorem fixed9 :
    checkPow (fixedTest Packed4.forward fullMask4) 9216 10 = true := by
  decide +kernel

private theorem fixed10 :
    checkPow (fixedTest Packed4.forward fullMask4) 10240 10 = true := by
  decide +kernel

private theorem fixed11 :
    checkPow (fixedTest Packed4.forward fullMask4) 11264 10 = true := by
  decide +kernel

private theorem fixed12 :
    checkPow (fixedTest Packed4.forward fullMask4) 12288 10 = true := by
  decide +kernel

private theorem fixed13 :
    checkPow (fixedTest Packed4.forward fullMask4) 13312 10 = true := by
  decide +kernel

private theorem fixed14 :
    checkPow (fixedTest Packed4.forward fullMask4) 14336 10 = true := by
  decide +kernel

private theorem fixed15 :
    checkPow (fixedTest Packed4.forward fullMask4) 15360 10 = true := by
  decide +kernel

private theorem fixed16 :
    checkPow (fixedTest Packed4.forward fullMask4) 16384 10 = true := by
  decide +kernel

private theorem fixed17 :
    checkPow (fixedTest Packed4.forward fullMask4) 17408 10 = true := by
  decide +kernel

private theorem fixed18 :
    checkPow (fixedTest Packed4.forward fullMask4) 18432 10 = true := by
  decide +kernel

private theorem fixed19 :
    checkPow (fixedTest Packed4.forward fullMask4) 19456 10 = true := by
  decide +kernel

private theorem fixed20 :
    checkPow (fixedTest Packed4.forward fullMask4) 20480 10 = true := by
  decide +kernel

private theorem fixed21 :
    checkPow (fixedTest Packed4.forward fullMask4) 21504 10 = true := by
  decide +kernel

private theorem fixed22 :
    checkPow (fixedTest Packed4.forward fullMask4) 22528 10 = true := by
  decide +kernel

private theorem fixed23 :
    checkPow (fixedTest Packed4.forward fullMask4) 23552 10 = true := by
  decide +kernel

private theorem fixed24 :
    checkPow (fixedTest Packed4.forward fullMask4) 24576 10 = true := by
  decide +kernel

private theorem fixed25 :
    checkPow (fixedTest Packed4.forward fullMask4) 25600 10 = true := by
  decide +kernel

private theorem fixed26 :
    checkPow (fixedTest Packed4.forward fullMask4) 26624 10 = true := by
  decide +kernel

private theorem fixed27 :
    checkPow (fixedTest Packed4.forward fullMask4) 27648 10 = true := by
  decide +kernel

private theorem fixed28 :
    checkPow (fixedTest Packed4.forward fullMask4) 28672 10 = true := by
  decide +kernel

private theorem fixed29 :
    checkPow (fixedTest Packed4.forward fullMask4) 29696 10 = true := by
  decide +kernel

private theorem fixed30 :
    checkPow (fixedTest Packed4.forward fullMask4) 30720 10 = true := by
  decide +kernel

private theorem fixed31 :
    checkPow (fixedTest Packed4.forward fullMask4) 31744 10 = true := by
  decide +kernel

private theorem fixed_complement :
    ∀ x : Fin 31671, (unionMasks masks4).testBit x.val = false → Packed4.forward x = x := by
  rw [mask_union]
  apply fixedTest_sound
  exact (checkPow_join (fixedTest Packed4.forward fullMask4) 14 0
    (checkPow_join (fixedTest Packed4.forward fullMask4) 13 0
    (checkPow_join (fixedTest Packed4.forward fullMask4) 12 0
    (checkPow_join (fixedTest Packed4.forward fullMask4) 11 0
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 0
    fixed0
    fixed1)
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 2048
    fixed2
    fixed3))
    (checkPow_join (fixedTest Packed4.forward fullMask4) 11 4096
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 4096
    fixed4
    fixed5)
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 6144
    fixed6
    fixed7)))
    (checkPow_join (fixedTest Packed4.forward fullMask4) 12 8192
    (checkPow_join (fixedTest Packed4.forward fullMask4) 11 8192
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 8192
    fixed8
    fixed9)
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 10240
    fixed10
    fixed11))
    (checkPow_join (fixedTest Packed4.forward fullMask4) 11 12288
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 12288
    fixed12
    fixed13)
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 14336
    fixed14
    fixed15))))
    (checkPow_join (fixedTest Packed4.forward fullMask4) 13 16384
    (checkPow_join (fixedTest Packed4.forward fullMask4) 12 16384
    (checkPow_join (fixedTest Packed4.forward fullMask4) 11 16384
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 16384
    fixed16
    fixed17)
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 18432
    fixed18
    fixed19))
    (checkPow_join (fixedTest Packed4.forward fullMask4) 11 20480
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 20480
    fixed20
    fixed21)
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 22528
    fixed22
    fixed23)))
    (checkPow_join (fixedTest Packed4.forward fullMask4) 12 24576
    (checkPow_join (fixedTest Packed4.forward fullMask4) 11 24576
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 24576
    fixed24
    fixed25)
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 26624
    fixed26
    fixed27))
    (checkPow_join (fixedTest Packed4.forward fullMask4) 11 28672
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 28672
    fixed28
    fixed29)
    (checkPow_join (fixedTest Packed4.forward fullMask4) 10 30720
    fixed30
    fixed31)))))

/-- Equality with the unchanged, literal inverse cycle product. -/
theorem permutation4_eq : Packed4.permutation = KernelData.generator4 := by
  apply Equiv.ext
  intro x
  exact map_eq_of_certificates Packed4.forward KernelData.cycleBlocks4
    parts4 masks4 decoded certificates disjoint actions fixed_complement x

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.GeneratorAgreement
