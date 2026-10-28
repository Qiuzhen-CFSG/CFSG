module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.DecodedA0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.DecodedA1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.DecodedA2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.DecodedA3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.DecodedA4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.DecodedA5
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.DecodedA6
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.DecodedB0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.DecodedB1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.DecodedB2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.DecodedB3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.DecodedB4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23
public import Theory.SpecificGroups.Fischer.AtlasCarriers.CycleListDecoding

/-!
# Checked decoding of the exact Fi23 generator tables

Each character-list witness is checked against its original ATLAS string using
`String.ofList` and `String.toList_ofList`. The exposed list decoder then proves
the literal cycles by reflexivity. This avoids repeatedly decoding large UTF-8
strings in every permutation calculation. No computation outside Lean is trusted.

These copies serve the Fi23 fixed-letter stabilizer certificate. The source is
ATLAS F23G1-p31671B0, retained beside `Fi23.lean`; the checker follows the existing
Fi22 `InvolutionBlock` certificates. `source/decode.py` reproduces this file.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelCertificate
open AtlasCarriers

set_option maxRecDepth 20000

private theorem decode_of_blocks {n : ℕ} [NeZero n]
    {blocks : List String} {parts : List (List (List (Fin n)))}
    (h : List.Forall₂ (fun b p => decodeCycleBlocks n [b] = p) blocks parts) :
    decodeCycleBlocks n blocks = parts.flatten := by
  induction h with
  | nil => rfl
  | @cons b p bs ps hb _ ih =>
    change _ = p ++ ps.flatten
    rw [← hb, ← ih]
    simp only [decodeCycleBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil]

def cyclesA : List (List (Fin 31671)) :=
  ([cyclesA0, cyclesA1, cyclesA2, cyclesA3, cyclesA4, cyclesA5, cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60]).flatten

theorem cyclesA_spec : decodeCycleBlocks 31671 cycleBlocksA = cyclesA := by
  apply decode_of_blocks (parts := [cyclesA0, cyclesA1, cyclesA2, cyclesA3, cyclesA4, cyclesA5, cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
  exact (List.Forall₂.cons cyclesA0_spec (List.Forall₂.cons cyclesA1_spec (List.Forall₂.cons cyclesA2_spec (List.Forall₂.cons cyclesA3_spec (List.Forall₂.cons cyclesA4_spec (List.Forall₂.cons cyclesA5_spec (List.Forall₂.cons cyclesA6_spec (List.Forall₂.cons cyclesA7_spec (List.Forall₂.cons cyclesA8_spec (List.Forall₂.cons cyclesA9_spec (List.Forall₂.cons cyclesA10_spec (List.Forall₂.cons cyclesA11_spec (List.Forall₂.cons cyclesA12_spec (List.Forall₂.cons cyclesA13_spec (List.Forall₂.cons cyclesA14_spec (List.Forall₂.cons cyclesA15_spec (List.Forall₂.cons cyclesA16_spec (List.Forall₂.cons cyclesA17_spec (List.Forall₂.cons cyclesA18_spec (List.Forall₂.cons cyclesA19_spec (List.Forall₂.cons cyclesA20_spec (List.Forall₂.cons cyclesA21_spec (List.Forall₂.cons cyclesA22_spec (List.Forall₂.cons cyclesA23_spec (List.Forall₂.cons cyclesA24_spec (List.Forall₂.cons cyclesA25_spec (List.Forall₂.cons cyclesA26_spec (List.Forall₂.cons cyclesA27_spec (List.Forall₂.cons cyclesA28_spec (List.Forall₂.cons cyclesA29_spec (List.Forall₂.cons cyclesA30_spec (List.Forall₂.cons cyclesA31_spec (List.Forall₂.cons cyclesA32_spec (List.Forall₂.cons cyclesA33_spec (List.Forall₂.cons cyclesA34_spec (List.Forall₂.cons cyclesA35_spec (List.Forall₂.cons cyclesA36_spec (List.Forall₂.cons cyclesA37_spec (List.Forall₂.cons cyclesA38_spec (List.Forall₂.cons cyclesA39_spec (List.Forall₂.cons cyclesA40_spec (List.Forall₂.cons cyclesA41_spec (List.Forall₂.cons cyclesA42_spec (List.Forall₂.cons cyclesA43_spec (List.Forall₂.cons cyclesA44_spec (List.Forall₂.cons cyclesA45_spec (List.Forall₂.cons cyclesA46_spec (List.Forall₂.cons cyclesA47_spec (List.Forall₂.cons cyclesA48_spec (List.Forall₂.cons cyclesA49_spec (List.Forall₂.cons cyclesA50_spec (List.Forall₂.cons cyclesA51_spec (List.Forall₂.cons cyclesA52_spec (List.Forall₂.cons cyclesA53_spec (List.Forall₂.cons cyclesA54_spec (List.Forall₂.cons cyclesA55_spec (List.Forall₂.cons cyclesA56_spec (List.Forall₂.cons cyclesA57_spec (List.Forall₂.cons cyclesA58_spec (List.Forall₂.cons cyclesA59_spec (List.Forall₂.cons cyclesA60_spec List.Forall₂.nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def cyclesB : List (List (Fin 31671)) :=
  ([cyclesB0, cyclesB1, cyclesB2, cyclesB3, cyclesB4, cyclesB5, cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41]).flatten

theorem cyclesB_spec : decodeCycleBlocks 31671 cycleBlocksB = cyclesB := by
  apply decode_of_blocks (parts := [cyclesB0, cyclesB1, cyclesB2, cyclesB3, cyclesB4, cyclesB5, cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
  exact (List.Forall₂.cons cyclesB0_spec (List.Forall₂.cons cyclesB1_spec (List.Forall₂.cons cyclesB2_spec (List.Forall₂.cons cyclesB3_spec (List.Forall₂.cons cyclesB4_spec (List.Forall₂.cons cyclesB5_spec (List.Forall₂.cons cyclesB6_spec (List.Forall₂.cons cyclesB7_spec (List.Forall₂.cons cyclesB8_spec (List.Forall₂.cons cyclesB9_spec (List.Forall₂.cons cyclesB10_spec (List.Forall₂.cons cyclesB11_spec (List.Forall₂.cons cyclesB12_spec (List.Forall₂.cons cyclesB13_spec (List.Forall₂.cons cyclesB14_spec (List.Forall₂.cons cyclesB15_spec (List.Forall₂.cons cyclesB16_spec (List.Forall₂.cons cyclesB17_spec (List.Forall₂.cons cyclesB18_spec (List.Forall₂.cons cyclesB19_spec (List.Forall₂.cons cyclesB20_spec (List.Forall₂.cons cyclesB21_spec (List.Forall₂.cons cyclesB22_spec (List.Forall₂.cons cyclesB23_spec (List.Forall₂.cons cyclesB24_spec (List.Forall₂.cons cyclesB25_spec (List.Forall₂.cons cyclesB26_spec (List.Forall₂.cons cyclesB27_spec (List.Forall₂.cons cyclesB28_spec (List.Forall₂.cons cyclesB29_spec (List.Forall₂.cons cyclesB30_spec (List.Forall₂.cons cyclesB31_spec (List.Forall₂.cons cyclesB32_spec (List.Forall₂.cons cyclesB33_spec (List.Forall₂.cons cyclesB34_spec (List.Forall₂.cons cyclesB35_spec (List.Forall₂.cons cyclesB36_spec (List.Forall₂.cons cyclesB37_spec (List.Forall₂.cons cyclesB38_spec (List.Forall₂.cons cyclesB39_spec (List.Forall₂.cons cyclesB40_spec (List.Forall₂.cons cyclesB41_spec List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))

end Sporadic.Fischer.Fi23.CentralizerSection.KernelCertificate
