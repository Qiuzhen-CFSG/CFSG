module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideZ3.Part0
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideZ3.Part1
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideZ3.Part2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideZ3.Part3
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideZ3.Part4
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideZ3.Part5
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideZ3.Part6
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideZ3.Part7

/-! Complete expansion bridge for the immutable z3 table. -/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideZ3
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic

def blocks : List (List Nat) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31, block32, block33, block34, block35, block36, block37, block38, block39, block40, block41, block42, block43, block44, block45, block46, block47, block48, block49, block50, block51, block52, block53, block54, block55]

theorem blocks_lengths : ∀ b ∈ blocks, b.length = 32 := by decide +kernel

theorem bridge : blocks.flatten = Data.z3Rows.map (expandFast 448) := by
  symm
  apply flatten_map
  exact .cons block0_bridge.symm (.cons block1_bridge.symm (.cons block2_bridge.symm (.cons block3_bridge.symm (.cons block4_bridge.symm (.cons block5_bridge.symm (.cons block6_bridge.symm (.cons block7_bridge.symm (.cons block8_bridge.symm (.cons block9_bridge.symm (.cons block10_bridge.symm (.cons block11_bridge.symm (.cons block12_bridge.symm (.cons block13_bridge.symm (.cons block14_bridge.symm (.cons block15_bridge.symm (.cons block16_bridge.symm (.cons block17_bridge.symm (.cons block18_bridge.symm (.cons block19_bridge.symm (.cons block20_bridge.symm (.cons block21_bridge.symm (.cons block22_bridge.symm (.cons block23_bridge.symm (.cons block24_bridge.symm (.cons block25_bridge.symm (.cons block26_bridge.symm (.cons block27_bridge.symm (.cons block28_bridge.symm (.cons block29_bridge.symm (.cons block30_bridge.symm (.cons block31_bridge.symm (.cons block32_bridge.symm (.cons block33_bridge.symm (.cons block34_bridge.symm (.cons block35_bridge.symm (.cons block36_bridge.symm (.cons block37_bridge.symm (.cons block38_bridge.symm (.cons block39_bridge.symm (.cons block40_bridge.symm (.cons block41_bridge.symm (.cons block42_bridge.symm (.cons block43_bridge.symm (.cons block44_bridge.symm (.cons block45_bridge.symm (.cons block46_bridge.symm (.cons block47_bridge.symm (.cons block48_bridge.symm (.cons block49_bridge.symm (.cons block50_bridge.symm (.cons block51_bridge.symm (.cons block52_bridge.symm (.cons block53_bridge.symm (.cons block54_bridge.symm (.cons block55_bridge.symm (.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideZ3
