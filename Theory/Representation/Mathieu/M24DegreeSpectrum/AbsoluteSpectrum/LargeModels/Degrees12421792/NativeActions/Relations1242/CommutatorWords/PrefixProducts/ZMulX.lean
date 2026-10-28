module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Blocks
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.Z
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.X
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.V

/-! Kernel-checked rows for the literal product z * x = v.
The existing checker verifies each sparse hint and computes every other row
by XOR. The block certificates assemble to the exact untransposed binary
matrix product. Source: ATLAS M24G1-P1 and M24G1-f2r1242B0;
see `../source/README.md`. -/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.PrefixProducts.ZMulX

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked00 : check Data.z.block00 Data.x.rows Data.v.block00
    Data.z.hints00 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked01 : check Data.z.block01 Data.x.rows Data.v.block01
    Data.z.hints01 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked02 : check Data.z.block02 Data.x.rows Data.v.block02
    Data.z.hints02 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked03 : check Data.z.block03 Data.x.rows Data.v.block03
    Data.z.hints03 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked04 : check Data.z.block04 Data.x.rows Data.v.block04
    Data.z.hints04 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked05 : check Data.z.block05 Data.x.rows Data.v.block05
    Data.z.hints05 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked06 : check Data.z.block06 Data.x.rows Data.v.block06
    Data.z.hints06 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked07 : check Data.z.block07 Data.x.rows Data.v.block07
    Data.z.hints07 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked08 : check Data.z.block08 Data.x.rows Data.v.block08
    Data.z.hints08 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked09 : check Data.z.block09 Data.x.rows Data.v.block09
    Data.z.hints09 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked10 : check Data.z.block10 Data.x.rows Data.v.block10
    Data.z.hints10 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked11 : check Data.z.block11 Data.x.rows Data.v.block11
    Data.z.hints11 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked12 : check Data.z.block12 Data.x.rows Data.v.block12
    Data.z.hints12 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked13 : check Data.z.block13 Data.x.rows Data.v.block13
    Data.z.hints13 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked14 : check Data.z.block14 Data.x.rows Data.v.block14
    Data.z.hints14 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked15 : check Data.z.block15 Data.x.rows Data.v.block15
    Data.z.hints15 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked16 : check Data.z.block16 Data.x.rows Data.v.block16
    Data.z.hints16 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked17 : check Data.z.block17 Data.x.rows Data.v.block17
    Data.z.hints17 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked18 : check Data.z.block18 Data.x.rows Data.v.block18
    Data.z.hints18 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked19 : check Data.z.block19 Data.x.rows Data.v.block19
    Data.z.hints19 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked20 : check Data.z.block20 Data.x.rows Data.v.block20
    Data.z.hints20 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked21 : check Data.z.block21 Data.x.rows Data.v.block21
    Data.z.hints21 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked22 : check Data.z.block22 Data.x.rows Data.v.block22
    Data.z.hints22 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked23 : check Data.z.block23 Data.x.rows Data.v.block23
    Data.z.hints23 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked24 : check Data.z.block24 Data.x.rows Data.v.block24
    Data.z.hints24 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked25 : check Data.z.block25 Data.x.rows Data.v.block25
    Data.z.hints25 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked26 : check Data.z.block26 Data.x.rows Data.v.block26
    Data.z.hints26 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked27 : check Data.z.block27 Data.x.rows Data.v.block27
    Data.z.hints27 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked28 : check Data.z.block28 Data.x.rows Data.v.block28
    Data.z.hints28 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked29 : check Data.z.block29 Data.x.rows Data.v.block29
    Data.z.hints29 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked30 : check Data.z.block30 Data.x.rows Data.v.block30
    Data.z.hints30 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked31 : check Data.z.block31 Data.x.rows Data.v.block31
    Data.z.hints31 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked32 : check Data.z.block32 Data.x.rows Data.v.block32
    Data.z.hints32 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked33 : check Data.z.block33 Data.x.rows Data.v.block33
    Data.z.hints33 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked34 : check Data.z.block34 Data.x.rows Data.v.block34
    Data.z.hints34 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked35 : check Data.z.block35 Data.x.rows Data.v.block35
    Data.z.hints35 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked36 : check Data.z.block36 Data.x.rows Data.v.block36
    Data.z.hints36 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked37 : check Data.z.block37 Data.x.rows Data.v.block37
    Data.z.hints37 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked38 : check Data.z.block38 Data.x.rows Data.v.block38
    Data.z.hints38 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked39 : check Data.z.block39 Data.x.rows Data.v.block39
    Data.z.hints39 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked40 : check Data.z.block40 Data.x.rows Data.v.block40
    Data.z.hints40 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked41 : check Data.z.block41 Data.x.rows Data.v.block41
    Data.z.hints41 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked42 : check Data.z.block42 Data.x.rows Data.v.block42
    Data.z.hints42 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked43 : check Data.z.block43 Data.x.rows Data.v.block43
    Data.z.hints43 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked44 : check Data.z.block44 Data.x.rows Data.v.block44
    Data.z.hints44 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem checked45 : check Data.z.block45 Data.x.rows Data.v.block45
    Data.z.hints45 = true := by decide +kernel

theorem checked : checkChunks Data.z.blocks Data.x.rows Data.v.blocks
    Data.z.hints = true := by
  simp only [Data.z.blocks, Data.v.blocks, Data.z.hints, checkChunks, Bool.and_eq_true]
  exact ⟨checked00, checked01, checked02, checked03, checked04, checked05, checked06, checked07, checked08, checked09, checked10, checked11, checked12, checked13, checked14, checked15, checked16, checked17, checked18, checked19, checked20, checked21, checked22, checked23, checked24, checked25, checked26, checked27, checked28, checked29, checked30, checked31, checked32, checked33, checked34, checked35, checked36, checked37, checked38, checked39, checked40, checked41, checked42, checked43, checked44, checked45, True.intro⟩

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.PrefixProducts.ZMulX

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.PrefixProducts

/-- The checked literal prefix product `z * x = v`. -/
theorem z_mul_x : Data.z.matrix * Data.x.matrix = Data.v.matrix :=
  product_of_chunks _ _ _ _ Data.z.length_rows Data.x.length_rows ZMulX.checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.PrefixProducts
