module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.SpecializedData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.TreeData

/-!
# Correctness of the specialized evaluator

The equalities are definitional: the functions perform precisely the balanced
selected-row additions of rowRec. No numerical matrix premise is assumed.
See source/README.md for the exact ATLAS conventions.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts

theorem rowRec_node (k : Nat) (l r : Tree) : rowRec (.node k l r) = evalFork k (rowRec l) (rowRec r) := rfl
theorem aFn0000_eq : aFn0000 = rowRec aTree0000 := by rfl
theorem aFn0064_eq : aFn0064 = rowRec aTree0064 := by rfl
theorem aFn0128_eq : aFn0128 = rowRec aTree0128 := by rfl
theorem aFn0192_eq : aFn0192 = rowRec aTree0192 := by rfl
theorem aFn0256_eq : aFn0256 = rowRec aTree0256 := by rfl
theorem aFn0320_eq : aFn0320 = rowRec aTree0320 := by rfl
theorem aFn0384_eq : aFn0384 = rowRec aTree0384 := by rfl
theorem aFn0448_eq : aFn0448 = rowRec aTree0448 := by rfl
theorem aFn0512_eq : aFn0512 = rowRec aTree0512 := by rfl
theorem aFn0576_eq : aFn0576 = rowRec aTree0576 := by rfl
theorem aFn0640_eq : aFn0640 = rowRec aTree0640 := by rfl
theorem aFn0704_eq : aFn0704 = rowRec aTree0704 := by rfl
theorem aFn0768_eq : aFn0768 = rowRec aTree0768 := by rfl
theorem aFn0832_eq : aFn0832 = rowRec aTree0832 := by rfl
theorem aFn0896_eq : aFn0896 = rowRec aTree0896 := by rfl
theorem aFn0960_eq : aFn0960 = rowRec aTree0960 := by rfl
theorem aFn1024_eq : aFn1024 = rowRec aTree1024 := by rfl
theorem aFn1088_eq : aFn1088 = rowRec aTree1088 := by rfl
theorem aFn1152_eq : aFn1152 = rowRec aTree1152 := by rfl
theorem aFn1216_eq : aFn1216 = rowRec aTree1216 := by rfl
theorem aFn1280_eq : aFn1280 = rowRec aTree1280 := by rfl
theorem aFn1344_eq : aFn1344 = rowRec aTree1344 := by rfl
theorem aFn1408_eq : aFn1408 = rowRec aTree1408 := by rfl
theorem aFn1472_eq : aFn1472 = rowRec aTree1472 := by rfl
theorem aFn1536_eq : aFn1536 = rowRec aTree1536 := by rfl
theorem aFn1600_eq : aFn1600 = rowRec aTree1600 := by rfl
theorem aFn1664_eq : aFn1664 = rowRec aTree1664 := by rfl
theorem aFn1728_eq : aFn1728 = rowRec aTree1728 := by rfl
theorem aFn_eq : aFn = rowRec aTree := by
  simp only [aFn, aTree, rowRec_node, aFn0000_eq, aFn0064_eq, aFn0128_eq, aFn0192_eq, aFn0256_eq, aFn0320_eq, aFn0384_eq, aFn0448_eq, aFn0512_eq, aFn0576_eq, aFn0640_eq, aFn0704_eq, aFn0768_eq, aFn0832_eq, aFn0896_eq, aFn0960_eq, aFn1024_eq, aFn1088_eq, aFn1152_eq, aFn1216_eq, aFn1280_eq, aFn1344_eq, aFn1408_eq, aFn1472_eq, aFn1536_eq, aFn1600_eq, aFn1664_eq, aFn1728_eq]
theorem bFn0000_eq : bFn0000 = rowRec bTree0000 := by rfl
theorem bFn0064_eq : bFn0064 = rowRec bTree0064 := by rfl
theorem bFn0128_eq : bFn0128 = rowRec bTree0128 := by rfl
theorem bFn0192_eq : bFn0192 = rowRec bTree0192 := by rfl
theorem bFn0256_eq : bFn0256 = rowRec bTree0256 := by rfl
theorem bFn0320_eq : bFn0320 = rowRec bTree0320 := by rfl
theorem bFn0384_eq : bFn0384 = rowRec bTree0384 := by rfl
theorem bFn0448_eq : bFn0448 = rowRec bTree0448 := by rfl
theorem bFn0512_eq : bFn0512 = rowRec bTree0512 := by rfl
theorem bFn0576_eq : bFn0576 = rowRec bTree0576 := by rfl
theorem bFn0640_eq : bFn0640 = rowRec bTree0640 := by rfl
theorem bFn0704_eq : bFn0704 = rowRec bTree0704 := by rfl
theorem bFn0768_eq : bFn0768 = rowRec bTree0768 := by rfl
theorem bFn0832_eq : bFn0832 = rowRec bTree0832 := by rfl
theorem bFn0896_eq : bFn0896 = rowRec bTree0896 := by rfl
theorem bFn0960_eq : bFn0960 = rowRec bTree0960 := by rfl
theorem bFn1024_eq : bFn1024 = rowRec bTree1024 := by rfl
theorem bFn1088_eq : bFn1088 = rowRec bTree1088 := by rfl
theorem bFn1152_eq : bFn1152 = rowRec bTree1152 := by rfl
theorem bFn1216_eq : bFn1216 = rowRec bTree1216 := by rfl
theorem bFn1280_eq : bFn1280 = rowRec bTree1280 := by rfl
theorem bFn1344_eq : bFn1344 = rowRec bTree1344 := by rfl
theorem bFn1408_eq : bFn1408 = rowRec bTree1408 := by rfl
theorem bFn1472_eq : bFn1472 = rowRec bTree1472 := by rfl
theorem bFn1536_eq : bFn1536 = rowRec bTree1536 := by rfl
theorem bFn1600_eq : bFn1600 = rowRec bTree1600 := by rfl
theorem bFn1664_eq : bFn1664 = rowRec bTree1664 := by rfl
theorem bFn1728_eq : bFn1728 = rowRec bTree1728 := by rfl
theorem bFn_eq : bFn = rowRec bTree := by
  simp only [bFn, bTree, rowRec_node, bFn0000_eq, bFn0064_eq, bFn0128_eq, bFn0192_eq, bFn0256_eq, bFn0320_eq, bFn0384_eq, bFn0448_eq, bFn0512_eq, bFn0576_eq, bFn0640_eq, bFn0704_eq, bFn0768_eq, bFn0832_eq, bFn0896_eq, bFn0960_eq, bFn1024_eq, bFn1088_eq, bFn1152_eq, bFn1216_eq, bFn1280_eq, bFn1344_eq, bFn1408_eq, bFn1472_eq, bFn1536_eq, bFn1600_eq, bFn1664_eq, bFn1728_eq]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
