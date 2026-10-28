module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Products
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.Data.AB
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.Data.AB4

/-!
# Reusing the shared literal HS products

Gates 0, 1, 2 and 6 of the existing shared product circuit check B·B, A·B²,
A·B and (A·B²)·B². They therefore identify both mixed factors needed here.
The two equality checks below compare the literal candidate data, preserving
the original row and coefficient order. No long-word relator is assumed.

The numerical producer remains `qt-k04-hs-896-long-shared-products`. Its gates
are still explicit hypotheses; this module does not assert they are proved.
Source: the retained HSG1-f4r896aB0 matrices and `LongWords/source/circuit.json`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree
open Certificates

set_option maxRecDepth 4096 in
theorem shared_ab_rows : LongWords.rows04 = rowsAB := by decide +kernel

set_option maxRecDepth 4096 in
theorem shared_ab_fourth_rows : LongWords.rows08 = rowsAB4 := by decide +kernel

/-- Only these four shared numerical gates are used, not any long-word identity. -/
theorem mixed_products_of_shared_gates
    (h0 : LongWords.ProductCheck 0) (h1 : LongWords.ProductCheck 1)
    (h2 : LongWords.ProductCheck 2) (h6 : LongWords.ProductCheck 6) :
    (Packed.eval 896 generatorRowsA * (Packed.eval 896 generatorRowsB) ^ 4 =
      Packed.eval 896 rowsAB4) ∧
    (Packed.eval 896 generatorRowsA * Packed.eval 896 generatorRowsB =
      Packed.eval 896 rowsAB) := by
  change Packed.eval 896 generatorRowsB * Packed.eval 896 generatorRowsB =
    Packed.eval 896 LongWords.rows02 at h0
  change Packed.eval 896 generatorRowsA * Packed.eval 896 LongWords.rows02 =
    Packed.eval 896 LongWords.rows03 at h1
  change Packed.eval 896 generatorRowsA * Packed.eval 896 generatorRowsB =
    Packed.eval 896 LongWords.rows04 at h2
  change Packed.eval 896 LongWords.rows03 * Packed.eval 896 LongWords.rows02 =
    Packed.eval 896 LongWords.rows08 at h6
  constructor
  · calc
      _ = (Packed.eval 896 generatorRowsA *
          (Packed.eval 896 generatorRowsB * Packed.eval 896 generatorRowsB)) *
          (Packed.eval 896 generatorRowsB * Packed.eval 896 generatorRowsB) := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = Packed.eval 896 rowsAB4 := by rw [h0, h1, h6, shared_ab_fourth_rows]
  · simpa only [shared_ab_rows] using h2

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree
