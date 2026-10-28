module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.TreeData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Evaluation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.WideFirst
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.WideSecond

/-!
# Balanced trees of the literal expanded generators

These trees duplicate the numerical witnesses only to balance kernel reduction.
The flattening equalities connect every leaf to the unchanged published tables;
no matrix expansion or product claim is assumed. See `../source/README.md`.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts

theorem checkTree_node (k : Nat) (l r : Tree) : checkTree (.node k l r) = ((checkTree l).1 + (checkTree r).1, ((checkTree l).1 == k) && (checkTree l).2 && (checkTree r).2) := rfl
theorem flattenRec_node (k : Nat) (l r : Tree) : flattenRec (.node k l r) = flattenRec l ++ flattenRec r := rfl
private theorem aCheck0000 : checkTree aTree0000 = (64, true) := by rfl
private theorem aCheck0064 : checkTree aTree0064 = (64, true) := by rfl
private theorem aCheck0128 : checkTree aTree0128 = (64, true) := by rfl
private theorem aCheck0192 : checkTree aTree0192 = (64, true) := by rfl
private theorem aCheck0256 : checkTree aTree0256 = (64, true) := by rfl
private theorem aCheck0320 : checkTree aTree0320 = (64, true) := by rfl
private theorem aCheck0384 : checkTree aTree0384 = (64, true) := by rfl
private theorem aCheck0448 : checkTree aTree0448 = (64, true) := by rfl
private theorem aCheck0512 : checkTree aTree0512 = (64, true) := by rfl
private theorem aCheck0576 : checkTree aTree0576 = (64, true) := by rfl
private theorem aCheck0640 : checkTree aTree0640 = (64, true) := by rfl
private theorem aCheck0704 : checkTree aTree0704 = (64, true) := by rfl
private theorem aCheck0768 : checkTree aTree0768 = (64, true) := by rfl
private theorem aCheck0832 : checkTree aTree0832 = (64, true) := by rfl
private theorem aCheck0896 : checkTree aTree0896 = (64, true) := by rfl
private theorem aCheck0960 : checkTree aTree0960 = (64, true) := by rfl
private theorem aCheck1024 : checkTree aTree1024 = (64, true) := by rfl
private theorem aCheck1088 : checkTree aTree1088 = (64, true) := by rfl
private theorem aCheck1152 : checkTree aTree1152 = (64, true) := by rfl
private theorem aCheck1216 : checkTree aTree1216 = (64, true) := by rfl
private theorem aCheck1280 : checkTree aTree1280 = (64, true) := by rfl
private theorem aCheck1344 : checkTree aTree1344 = (64, true) := by rfl
private theorem aCheck1408 : checkTree aTree1408 = (64, true) := by rfl
private theorem aCheck1472 : checkTree aTree1472 = (64, true) := by rfl
private theorem aCheck1536 : checkTree aTree1536 = (64, true) := by rfl
private theorem aCheck1600 : checkTree aTree1600 = (64, true) := by rfl
private theorem aCheck1664 : checkTree aTree1664 = (64, true) := by rfl
private theorem aCheck1728 : checkTree aTree1728 = (64, true) := by rfl
private theorem aCheck : checkTree aTree = (1792, true) := by
  simp only [aTree, checkTree_node, aCheck0000, aCheck0064, aCheck0128, aCheck0192, aCheck0256, aCheck0320, aCheck0384, aCheck0448, aCheck0512, aCheck0576, aCheck0640, aCheck0704, aCheck0768, aCheck0832, aCheck0896, aCheck0960, aCheck1024, aCheck1088, aCheck1152, aCheck1216, aCheck1280, aCheck1344, aCheck1408, aCheck1472, aCheck1536, aCheck1600, aCheck1664, aCheck1728]
  rfl
theorem aValid : Valid aTree := checkTree_valid _ (congrArg Prod.snd aCheck)
private theorem aFlat0000 : flattenRec aTree0000 ++ flattenRec aTree0064 = RightCertificate.wideFirst0000 := by rfl
private theorem aFlat0128 : flattenRec aTree0128 ++ flattenRec aTree0192 = RightCertificate.wideFirst0128 := by rfl
private theorem aFlat0256 : flattenRec aTree0256 ++ flattenRec aTree0320 = RightCertificate.wideFirst0256 := by rfl
private theorem aFlat0384 : flattenRec aTree0384 ++ flattenRec aTree0448 = RightCertificate.wideFirst0384 := by rfl
private theorem aFlat0512 : flattenRec aTree0512 ++ flattenRec aTree0576 = RightCertificate.wideFirst0512 := by rfl
private theorem aFlat0640 : flattenRec aTree0640 ++ flattenRec aTree0704 = RightCertificate.wideFirst0640 := by rfl
private theorem aFlat0768 : flattenRec aTree0768 ++ flattenRec aTree0832 = RightCertificate.wideFirst0768 := by rfl
private theorem aFlat0896 : flattenRec aTree0896 ++ flattenRec aTree0960 = RightCertificate.wideFirst0896 := by rfl
private theorem aFlat1024 : flattenRec aTree1024 ++ flattenRec aTree1088 = RightCertificate.wideFirst1024 := by rfl
private theorem aFlat1152 : flattenRec aTree1152 ++ flattenRec aTree1216 = RightCertificate.wideFirst1152 := by rfl
private theorem aFlat1280 : flattenRec aTree1280 ++ flattenRec aTree1344 = RightCertificate.wideFirst1280 := by rfl
private theorem aFlat1408 : flattenRec aTree1408 ++ flattenRec aTree1472 = RightCertificate.wideFirst1408 := by rfl
private theorem aFlat1536 : flattenRec aTree1536 ++ flattenRec aTree1600 = RightCertificate.wideFirst1536 := by rfl
private theorem aFlat1664 : flattenRec aTree1664 ++ flattenRec aTree1728 = RightCertificate.wideFirst1664 := by rfl
theorem aFlatten : flatten aTree = RightCertificate.wideFirst := by
  rw [← flattenRec_eq]
  calc
    flattenRec aTree = (flattenRec aTree0000 ++ flattenRec aTree0064) ++ (flattenRec aTree0128 ++ flattenRec aTree0192) ++ (flattenRec aTree0256 ++ flattenRec aTree0320) ++ (flattenRec aTree0384 ++ flattenRec aTree0448) ++ (flattenRec aTree0512 ++ flattenRec aTree0576) ++ (flattenRec aTree0640 ++ flattenRec aTree0704) ++ (flattenRec aTree0768 ++ flattenRec aTree0832) ++ (flattenRec aTree0896 ++ flattenRec aTree0960) ++ (flattenRec aTree1024 ++ flattenRec aTree1088) ++ (flattenRec aTree1152 ++ flattenRec aTree1216) ++ (flattenRec aTree1280 ++ flattenRec aTree1344) ++ (flattenRec aTree1408 ++ flattenRec aTree1472) ++ (flattenRec aTree1536 ++ flattenRec aTree1600) ++ (flattenRec aTree1664 ++ flattenRec aTree1728) := by
      simp only [aTree, flattenRec_node, List.append_assoc]
    _ = _ := by
      rw [aFlat0000, aFlat0128, aFlat0256, aFlat0384, aFlat0512, aFlat0640, aFlat0768, aFlat0896, aFlat1024, aFlat1152, aFlat1280, aFlat1408, aFlat1536, aFlat1664]
      rfl
private theorem bCheck0000 : checkTree bTree0000 = (64, true) := by rfl
private theorem bCheck0064 : checkTree bTree0064 = (64, true) := by rfl
private theorem bCheck0128 : checkTree bTree0128 = (64, true) := by rfl
private theorem bCheck0192 : checkTree bTree0192 = (64, true) := by rfl
private theorem bCheck0256 : checkTree bTree0256 = (64, true) := by rfl
private theorem bCheck0320 : checkTree bTree0320 = (64, true) := by rfl
private theorem bCheck0384 : checkTree bTree0384 = (64, true) := by rfl
private theorem bCheck0448 : checkTree bTree0448 = (64, true) := by rfl
private theorem bCheck0512 : checkTree bTree0512 = (64, true) := by rfl
private theorem bCheck0576 : checkTree bTree0576 = (64, true) := by rfl
private theorem bCheck0640 : checkTree bTree0640 = (64, true) := by rfl
private theorem bCheck0704 : checkTree bTree0704 = (64, true) := by rfl
private theorem bCheck0768 : checkTree bTree0768 = (64, true) := by rfl
private theorem bCheck0832 : checkTree bTree0832 = (64, true) := by rfl
private theorem bCheck0896 : checkTree bTree0896 = (64, true) := by rfl
private theorem bCheck0960 : checkTree bTree0960 = (64, true) := by rfl
private theorem bCheck1024 : checkTree bTree1024 = (64, true) := by rfl
private theorem bCheck1088 : checkTree bTree1088 = (64, true) := by rfl
private theorem bCheck1152 : checkTree bTree1152 = (64, true) := by rfl
private theorem bCheck1216 : checkTree bTree1216 = (64, true) := by rfl
private theorem bCheck1280 : checkTree bTree1280 = (64, true) := by rfl
private theorem bCheck1344 : checkTree bTree1344 = (64, true) := by rfl
private theorem bCheck1408 : checkTree bTree1408 = (64, true) := by rfl
private theorem bCheck1472 : checkTree bTree1472 = (64, true) := by rfl
private theorem bCheck1536 : checkTree bTree1536 = (64, true) := by rfl
private theorem bCheck1600 : checkTree bTree1600 = (64, true) := by rfl
private theorem bCheck1664 : checkTree bTree1664 = (64, true) := by rfl
private theorem bCheck1728 : checkTree bTree1728 = (64, true) := by rfl
private theorem bCheck : checkTree bTree = (1792, true) := by
  simp only [bTree, checkTree_node, bCheck0000, bCheck0064, bCheck0128, bCheck0192, bCheck0256, bCheck0320, bCheck0384, bCheck0448, bCheck0512, bCheck0576, bCheck0640, bCheck0704, bCheck0768, bCheck0832, bCheck0896, bCheck0960, bCheck1024, bCheck1088, bCheck1152, bCheck1216, bCheck1280, bCheck1344, bCheck1408, bCheck1472, bCheck1536, bCheck1600, bCheck1664, bCheck1728]
  rfl
theorem bValid : Valid bTree := checkTree_valid _ (congrArg Prod.snd bCheck)
private theorem bFlat0000 : flattenRec bTree0000 ++ flattenRec bTree0064 = RightCertificate.wideSecond0000 := by rfl
private theorem bFlat0128 : flattenRec bTree0128 ++ flattenRec bTree0192 = RightCertificate.wideSecond0128 := by rfl
private theorem bFlat0256 : flattenRec bTree0256 ++ flattenRec bTree0320 = RightCertificate.wideSecond0256 := by rfl
private theorem bFlat0384 : flattenRec bTree0384 ++ flattenRec bTree0448 = RightCertificate.wideSecond0384 := by rfl
private theorem bFlat0512 : flattenRec bTree0512 ++ flattenRec bTree0576 = RightCertificate.wideSecond0512 := by rfl
private theorem bFlat0640 : flattenRec bTree0640 ++ flattenRec bTree0704 = RightCertificate.wideSecond0640 := by rfl
private theorem bFlat0768 : flattenRec bTree0768 ++ flattenRec bTree0832 = RightCertificate.wideSecond0768 := by rfl
private theorem bFlat0896 : flattenRec bTree0896 ++ flattenRec bTree0960 = RightCertificate.wideSecond0896 := by rfl
private theorem bFlat1024 : flattenRec bTree1024 ++ flattenRec bTree1088 = RightCertificate.wideSecond1024 := by rfl
private theorem bFlat1152 : flattenRec bTree1152 ++ flattenRec bTree1216 = RightCertificate.wideSecond1152 := by rfl
private theorem bFlat1280 : flattenRec bTree1280 ++ flattenRec bTree1344 = RightCertificate.wideSecond1280 := by rfl
private theorem bFlat1408 : flattenRec bTree1408 ++ flattenRec bTree1472 = RightCertificate.wideSecond1408 := by rfl
private theorem bFlat1536 : flattenRec bTree1536 ++ flattenRec bTree1600 = RightCertificate.wideSecond1536 := by rfl
private theorem bFlat1664 : flattenRec bTree1664 ++ flattenRec bTree1728 = RightCertificate.wideSecond1664 := by rfl
theorem bFlatten : flatten bTree = RightCertificate.wideSecond := by
  rw [← flattenRec_eq]
  calc
    flattenRec bTree = (flattenRec bTree0000 ++ flattenRec bTree0064) ++ (flattenRec bTree0128 ++ flattenRec bTree0192) ++ (flattenRec bTree0256 ++ flattenRec bTree0320) ++ (flattenRec bTree0384 ++ flattenRec bTree0448) ++ (flattenRec bTree0512 ++ flattenRec bTree0576) ++ (flattenRec bTree0640 ++ flattenRec bTree0704) ++ (flattenRec bTree0768 ++ flattenRec bTree0832) ++ (flattenRec bTree0896 ++ flattenRec bTree0960) ++ (flattenRec bTree1024 ++ flattenRec bTree1088) ++ (flattenRec bTree1152 ++ flattenRec bTree1216) ++ (flattenRec bTree1280 ++ flattenRec bTree1344) ++ (flattenRec bTree1408 ++ flattenRec bTree1472) ++ (flattenRec bTree1536 ++ flattenRec bTree1600) ++ (flattenRec bTree1664 ++ flattenRec bTree1728) := by
      simp only [bTree, flattenRec_node, List.append_assoc]
    _ = _ := by
      rw [bFlat0000, bFlat0128, bFlat0256, bFlat0384, bFlat0512, bFlat0640, bFlat0768, bFlat0896, bFlat1024, bFlat1152, bFlat1280, bFlat1408, bFlat1536, bFlat1664]
      rfl
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
