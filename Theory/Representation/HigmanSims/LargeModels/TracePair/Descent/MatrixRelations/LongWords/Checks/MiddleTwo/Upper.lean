module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Upper.Gate30
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Upper.Gate31
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Upper.Gate32
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Upper.Gate33

/-!
# The four upper middle products of the HS long-word circuit

The checked products have candidate indices (28,29,32), (30,31,33),
(32,33,34), and (18,18,35). Candidates 34 and 35 are the actual identity.
All numerical rows are kernel checked; the last sixteen rows of the final
square reuse `MiddleTwo.Tail`. No earlier product or word interpretation is
assumed. Source and reproduction: `Upper/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo

/-- Unconditional certification of the four fixed product gates 30--33. -/
theorem upper_products (i : Fin 46) (hlo : 30 ≤ i.val) (hhi : i.val < 34) :
    ProductCheck i := by
  have hi : i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 := by
    simp only [Fin.ext_iff]
    omega
  rcases hi with rfl | rfl | rfl | rfl
  · exact Upper.gate30_checked
  · exact Upper.gate31_checked
  · exact Upper.gate32_checked
  · exact Upper.gate33_checked

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo
