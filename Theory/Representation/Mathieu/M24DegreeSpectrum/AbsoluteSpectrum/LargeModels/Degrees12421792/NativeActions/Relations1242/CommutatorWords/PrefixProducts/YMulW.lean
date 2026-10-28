module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Blocks
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.Y
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.W
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.Z

/-! Kernel-checked rows for the literal product y * w = z.
The existing checker verifies each sparse hint and computes every other row
by XOR. The block certificates assemble to the exact untransposed binary
matrix product. Source: ATLAS M24G1-P1 and M24G1-f2r1242B0;
see `../source/README.md`. -/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.PrefixProducts.YMulW

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked00 : check Data.y.block00 Data.w.rows Data.z.block00
    Data.y.hints00 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked01 : check Data.y.block01 Data.w.rows Data.z.block01
    Data.y.hints01 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked02 : check Data.y.block02 Data.w.rows Data.z.block02
    Data.y.hints02 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked03 : check Data.y.block03 Data.w.rows Data.z.block03
    Data.y.hints03 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked04 : check Data.y.block04 Data.w.rows Data.z.block04
    Data.y.hints04 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked05 : check Data.y.block05 Data.w.rows Data.z.block05
    Data.y.hints05 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked06 : check Data.y.block06 Data.w.rows Data.z.block06
    Data.y.hints06 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked07 : check Data.y.block07 Data.w.rows Data.z.block07
    Data.y.hints07 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked08 : check Data.y.block08 Data.w.rows Data.z.block08
    Data.y.hints08 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked09 : check Data.y.block09 Data.w.rows Data.z.block09
    Data.y.hints09 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked10 : check Data.y.block10 Data.w.rows Data.z.block10
    Data.y.hints10 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked11 : check Data.y.block11 Data.w.rows Data.z.block11
    Data.y.hints11 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked12 : check Data.y.block12 Data.w.rows Data.z.block12
    Data.y.hints12 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked13 : check Data.y.block13 Data.w.rows Data.z.block13
    Data.y.hints13 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked14 : check Data.y.block14 Data.w.rows Data.z.block14
    Data.y.hints14 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked15 : check Data.y.block15 Data.w.rows Data.z.block15
    Data.y.hints15 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked16 : check Data.y.block16 Data.w.rows Data.z.block16
    Data.y.hints16 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked17 : check Data.y.block17 Data.w.rows Data.z.block17
    Data.y.hints17 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked18 : check Data.y.block18 Data.w.rows Data.z.block18
    Data.y.hints18 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked19 : check Data.y.block19 Data.w.rows Data.z.block19
    Data.y.hints19 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked20 : check Data.y.block20 Data.w.rows Data.z.block20
    Data.y.hints20 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked21 : check Data.y.block21 Data.w.rows Data.z.block21
    Data.y.hints21 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked22 : check Data.y.block22 Data.w.rows Data.z.block22
    Data.y.hints22 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked23 : check Data.y.block23 Data.w.rows Data.z.block23
    Data.y.hints23 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked24 : check Data.y.block24 Data.w.rows Data.z.block24
    Data.y.hints24 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked25 : check Data.y.block25 Data.w.rows Data.z.block25
    Data.y.hints25 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked26 : check Data.y.block26 Data.w.rows Data.z.block26
    Data.y.hints26 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked27 : check Data.y.block27 Data.w.rows Data.z.block27
    Data.y.hints27 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked28 : check Data.y.block28 Data.w.rows Data.z.block28
    Data.y.hints28 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked29 : check Data.y.block29 Data.w.rows Data.z.block29
    Data.y.hints29 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked30 : check Data.y.block30 Data.w.rows Data.z.block30
    Data.y.hints30 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked31 : check Data.y.block31 Data.w.rows Data.z.block31
    Data.y.hints31 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked32 : check Data.y.block32 Data.w.rows Data.z.block32
    Data.y.hints32 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked33 : check Data.y.block33 Data.w.rows Data.z.block33
    Data.y.hints33 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked34 : check Data.y.block34 Data.w.rows Data.z.block34
    Data.y.hints34 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked35 : check Data.y.block35 Data.w.rows Data.z.block35
    Data.y.hints35 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked36 : check Data.y.block36 Data.w.rows Data.z.block36
    Data.y.hints36 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked37 : check Data.y.block37 Data.w.rows Data.z.block37
    Data.y.hints37 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked38 : check Data.y.block38 Data.w.rows Data.z.block38
    Data.y.hints38 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked39 : check Data.y.block39 Data.w.rows Data.z.block39
    Data.y.hints39 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked40 : check Data.y.block40 Data.w.rows Data.z.block40
    Data.y.hints40 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked41 : check Data.y.block41 Data.w.rows Data.z.block41
    Data.y.hints41 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked42 : check Data.y.block42 Data.w.rows Data.z.block42
    Data.y.hints42 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked43 : check Data.y.block43 Data.w.rows Data.z.block43
    Data.y.hints43 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked44 : check Data.y.block44 Data.w.rows Data.z.block44
    Data.y.hints44 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked45 : check Data.y.block45 Data.w.rows Data.z.block45
    Data.y.hints45 = true := by decide +kernel

theorem checked : checkChunks Data.y.blocks Data.w.rows Data.z.blocks
    Data.y.hints = true := by
  simp only [Data.y.blocks, Data.z.blocks, Data.y.hints, checkChunks, Bool.and_eq_true]
  exact ⟨checked00, checked01, checked02, checked03, checked04, checked05, checked06, checked07, checked08, checked09, checked10, checked11, checked12, checked13, checked14, checked15, checked16, checked17, checked18, checked19, checked20, checked21, checked22, checked23, checked24, checked25, checked26, checked27, checked28, checked29, checked30, checked31, checked32, checked33, checked34, checked35, checked36, checked37, checked38, checked39, checked40, checked41, checked42, checked43, checked44, checked45, True.intro⟩

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.PrefixProducts.YMulW

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.PrefixProducts

/-- The checked literal prefix product `y * w = z`. -/
theorem y_mul_w : Data.y.matrix * Data.w.matrix = Data.z.matrix :=
  product_of_chunks _ _ _ _ Data.y.length_rows Data.w.length_rows YMulW.checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.PrefixProducts
