module

public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.Data

/-! Checked products for the ATLAS matrices. See `Data` and `source/README.md`. -/

namespace Rudvalis.Multiplier.DoubleCover
public section

theorem product_0 : matrixA * matrixA = matrixNegOne := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_1 : matrixB * matrixB = b2 := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_2 : b2 * b2 = matrixOne := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_3 : matrixA * matrixB = ab := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_4 : ab * ab = ab2 := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_5 : ab2 * ab2 = ab4 := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_6 : ab4 * ab4 = ab8 := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_7 : ab8 * ab4 = ab12 := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_8 : ab12 * ab = matrixOne := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_9 : ab * matrixA = aba := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_10 : aba * matrixB = abab := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_11 : abab * matrixB = w := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_12 : w * w = w2 := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_13 : w2 * w2 = w4 := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_14 : w4 * w4 = w8 := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_15 : w8 * w8 = w16 := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_16 : w16 * w8 = w24 := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_17 : w24 * w4 = w28 := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

theorem product_18 : w28 * w = matrixOne := by
  exact checkProduct_sound _ _ _ (by decide +kernel)

end
end Rudvalis.Multiplier.DoubleCover
