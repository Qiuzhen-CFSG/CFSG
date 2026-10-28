module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Arithmetic
import Mathlib.Tactic.FinCases

/-!
# Sixteen checked rows of the R1 square

Rows 880--895 of candidate 18 squared are the corresponding identity rows.
Each arithmetic equality checks all 896 output coordinates, using the literal
candidate matrix and the sound accumulator of `MiddleTwo.Arithmetic`.
`product_33_of_head` applies these certificates to the actual gate 33, leaving
exactly the first 880 rows explicit. It does not claim the whole square is checked.
Source and circuit conventions: `LongWords/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo
open Certificates Packed

private theorem row880 : product (rows18.getD (880) (0,0)).1 (rows18.getD (880) (0,0)).2 rows18 0 0 = identityRows.getD (880) (0,0) := by decide +kernel

private theorem row881 : product (rows18.getD (881) (0,0)).1 (rows18.getD (881) (0,0)).2 rows18 0 0 = identityRows.getD (881) (0,0) := by decide +kernel

private theorem row882 : product (rows18.getD (882) (0,0)).1 (rows18.getD (882) (0,0)).2 rows18 0 0 = identityRows.getD (882) (0,0) := by decide +kernel

private theorem row883 : product (rows18.getD (883) (0,0)).1 (rows18.getD (883) (0,0)).2 rows18 0 0 = identityRows.getD (883) (0,0) := by decide +kernel

private theorem row884 : product (rows18.getD (884) (0,0)).1 (rows18.getD (884) (0,0)).2 rows18 0 0 = identityRows.getD (884) (0,0) := by decide +kernel

private theorem row885 : product (rows18.getD (885) (0,0)).1 (rows18.getD (885) (0,0)).2 rows18 0 0 = identityRows.getD (885) (0,0) := by decide +kernel

private theorem row886 : product (rows18.getD (886) (0,0)).1 (rows18.getD (886) (0,0)).2 rows18 0 0 = identityRows.getD (886) (0,0) := by decide +kernel

private theorem row887 : product (rows18.getD (887) (0,0)).1 (rows18.getD (887) (0,0)).2 rows18 0 0 = identityRows.getD (887) (0,0) := by decide +kernel

private theorem row888 : product (rows18.getD (888) (0,0)).1 (rows18.getD (888) (0,0)).2 rows18 0 0 = identityRows.getD (888) (0,0) := by decide +kernel

private theorem row889 : product (rows18.getD (889) (0,0)).1 (rows18.getD (889) (0,0)).2 rows18 0 0 = identityRows.getD (889) (0,0) := by decide +kernel

private theorem row890 : product (rows18.getD (890) (0,0)).1 (rows18.getD (890) (0,0)).2 rows18 0 0 = identityRows.getD (890) (0,0) := by decide +kernel

private theorem row891 : product (rows18.getD (891) (0,0)).1 (rows18.getD (891) (0,0)).2 rows18 0 0 = identityRows.getD (891) (0,0) := by decide +kernel

private theorem row892 : product (rows18.getD (892) (0,0)).1 (rows18.getD (892) (0,0)).2 rows18 0 0 = identityRows.getD (892) (0,0) := by decide +kernel

private theorem row893 : product (rows18.getD (893) (0,0)).1 (rows18.getD (893) (0,0)).2 rows18 0 0 = identityRows.getD (893) (0,0) := by decide +kernel

private theorem row894 : product (rows18.getD (894) (0,0)).1 (rows18.getD (894) (0,0)).2 rows18 0 0 = identityRows.getD (894) (0,0) := by decide +kernel

private theorem row895 : product (rows18.getD (895) (0,0)).1 (rows18.getD (895) (0,0)).2 rows18 0 0 = identityRows.getD (895) (0,0) := by decide +kernel

private theorem tail_rows (r : Fin 16) :
    product (rows18.getD (880 + r.val) (0,0)).1 (rows18.getD (880 + r.val) (0,0)).2 rows18 0 0 = identityRows.getD (880 + r.val) (0,0) := by
  fin_cases r
  · exact row880
  · exact row881
  · exact row882
  · exact row883
  · exact row884
  · exact row885
  · exact row886
  · exact row887
  · exact row888
  · exact row889
  · exact row890
  · exact row891
  · exact row892
  · exact row893
  · exact row894
  · exact row895

/-- The last sixteen numerical rows of the literal candidate-18 square. -/
theorem gate33_tail (r : Fin 896) (hr : 880 ≤ r.val) :
    rowProduct (rows18.getD r.val (0,0)) rows18 = identityRows.getD r.val (0,0) := by
  rw [← rowProduct_eq]
  have h := tail_rows ⟨r.val - 880, by omega⟩
  have he : 880 + (r.val - 880) = r.val := by omega
  simpa only [he] using h

/-- Apply the checked tail to gate 33; precisely the other 880 rows remain. -/
theorem product_33_of_head
    (hhead : ∀ r : Fin 896, r.val < 880 →
      rowProduct (rows18.getD r.val (0,0)) rows18 = identityRows.getD r.val (0,0)) :
    ProductCheck 33 := by
  apply productCheck_of_rows
  intro r
  by_cases hr : r.val < 880
  · exact hhead r hr
  · exact gate33_tail r (by omega)

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo
