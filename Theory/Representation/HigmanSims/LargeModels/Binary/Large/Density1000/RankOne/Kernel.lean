module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Blocks
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Parity
/-!
# The packed density operator annihilates the image column

Eight sequential checks of 125 rows each verify all dot products against the
literal image bitmap. The balanced blocks are aligned with `Data.dRows`, and
`RowTree.mulVec_zero` transports the checks to ordinary matrix multiplication.
No generator-word identification is assumed or claimed here. The rank-one
assembly must supply that independent equality before using this on the
actual algebra element.

Source: R. A. Wilson et al., ATLAS HSG1-f2r1000B0 and the preserved density
witness. Attribution and rights are retained in `Binary/source/README.md`.
-/

@[expose] public section
open Matrix Thompson.BinaryMatrix
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
open RowArithmetic

theorem dTree_kills_image : dTree.checkZero Data.image = true := by
  have h0 : dTreeBlock0.checkZero Data.image = true := by decide +kernel
  have h1 : dTreeBlock1.checkZero Data.image = true := by decide +kernel
  have h2 : dTreeBlock2.checkZero Data.image = true := by decide +kernel
  have h3 : dTreeBlock3.checkZero Data.image = true := by decide +kernel
  have h4 : dTreeBlock4.checkZero Data.image = true := by decide +kernel
  have h5 : dTreeBlock5.checkZero Data.image = true := by decide +kernel
  have h6 : dTreeBlock6.checkZero Data.image = true := by decide +kernel
  have h7 : dTreeBlock7.checkZero Data.image = true := by decide +kernel
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨h0, h1⟩, Bool.and_eq_true_iff.mpr ⟨h2, h3⟩⟩, Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨h4, h5⟩, Bool.and_eq_true_iff.mpr ⟨h6, h7⟩⟩⟩

theorem d_mul_image : (decode 1000 Data.dRows).mulVec imageVector = 0 :=
  dTree.mulVec_zero Data.dRows dTree_aligned dRows_size Data.image dTree_kills_image

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
