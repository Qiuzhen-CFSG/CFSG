module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Product00
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Product01
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Product02
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Product03
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Product04
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Product05
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Product06
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Product07
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Square00
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Square01
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Square02
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Square03
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Square04
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Square05
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Square06
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Square07

/-!
# Two exact products in the nested fourth-power circuit

The checked numerical blocks cover all 1792 rows in their original order.
The certified base-2048 expansions and the product soundness theorem turn
these into unconditional equalities of the immutable matrices. These
discharge the `ht` and `ht2` premises of `MixedWords.nested_fourth_of_products`.
Source: John Bray’s ATLAS M24G1-P1; see `TProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts

private theorem product_rows :
    Data.xRows.map (fun a => Hybrid.row a Data.z3Rows WideZ3.blocks) = Data.tRows := by
  apply Arithmetic.flatten_map
  exact .cons product_block0 (.cons product_block1 (.cons product_block2 (.cons product_block3 (.cons product_block4 (.cons product_block5 (.cons product_block6 (.cons product_block7 (.cons product_block8 (.cons product_block9 (.cons product_block10 (.cons product_block11 (.cons product_block12 (.cons product_block13 (.cons product_block14 (.cons product_block15 (.cons product_block16 (.cons product_block17 (.cons product_block18 (.cons product_block19 (.cons product_block20 (.cons product_block21 (.cons product_block22 (.cons product_block23 (.cons product_block24 (.cons product_block25 (.cons product_block26 (.cons product_block27 (.cons product_block28 (.cons product_block29 (.cons product_block30 (.cons product_block31 (.cons product_block32 (.cons product_block33 (.cons product_block34 (.cons product_block35 (.cons product_block36 (.cons product_block37 (.cons product_block38 (.cons product_block39 (.cons product_block40 (.cons product_block41 (.cons product_block42 (.cons product_block43 (.cons product_block44 (.cons product_block45 (.cons product_block46 (.cons product_block47 (.cons product_block48 (.cons product_block49 (.cons product_block50 (.cons product_block51 (.cons product_block52 (.cons product_block53 (.cons product_block54 (.cons product_block55 (.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The full literal x · z3 product, with no additional premises. -/
theorem t_product : Data.x * Data.z3 = Data.t := by
  exact Hybrid.product Data.xRows Data.z3Rows Data.tRows WideZ3.blocks
    Data.xRows_length Data.z3Rows_length WideZ3.bridge WideZ3.blocks_lengths
    product_rows

private theorem square_rows :
    Data.tRows.map (fun a => Arithmetic.row a WideT.blocks) = Data.t2Rows := by
  apply Arithmetic.flatten_map
  exact .cons square_block0 (.cons square_block1 (.cons square_block2 (.cons square_block3 (.cons square_block4 (.cons square_block5 (.cons square_block6 (.cons square_block7 (.cons square_block8 (.cons square_block9 (.cons square_block10 (.cons square_block11 (.cons square_block12 (.cons square_block13 (.cons square_block14 (.cons square_block15 (.cons square_block16 (.cons square_block17 (.cons square_block18 (.cons square_block19 (.cons square_block20 (.cons square_block21 (.cons square_block22 (.cons square_block23 (.cons square_block24 (.cons square_block25 (.cons square_block26 (.cons square_block27 (.cons square_block28 (.cons square_block29 (.cons square_block30 (.cons square_block31 (.cons square_block32 (.cons square_block33 (.cons square_block34 (.cons square_block35 (.cons square_block36 (.cons square_block37 (.cons square_block38 (.cons square_block39 (.cons square_block40 (.cons square_block41 (.cons square_block42 (.cons square_block43 (.cons square_block44 (.cons square_block45 (.cons square_block46 (.cons square_block47 (.cons square_block48 (.cons square_block49 (.cons square_block50 (.cons square_block51 (.cons square_block52 (.cons square_block53 (.cons square_block54 (.cons square_block55 (.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The full literal t · t product, with no additional premises. -/
theorem t_square : Data.t * Data.t = Data.t2 := by
  exact Arithmetic.product Data.tRows Data.tRows Data.t2Rows WideT.blocks
    Data.tRows_length Data.tRows_length WideT.bridge WideT.blocks_lengths
    square_rows

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts
