module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo.Checker

/-!
# Sixteen complete rows of the first remaining HS product

This numerical certificate checks rows 880 through 895 of candidate 12 times
candidate 13, against candidate 19. It uses the literal shared matrices and
kernel reduction only. It is a reusable part of gate 17, not a whole gate.
See `source/README.md` for measurements and source conventions.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.FirstTwo

set_option Elab.async false in
/-- The final sixteen actual row checks of gate 17. -/
theorem gate17_last16 : CheckedRange 17 880 16 :=
  checkedRange_of_check 17 880 16 (by decide +kernel)

/-- Apply the checked range to all entries of the actual matrix-product rows. -/
theorem gate17_last_rows (r : Fin 896) (hr : 880 ≤ r.val) :
    (candidate 12 * candidate 13) r = candidate 19 r :=
  row_eq_of_check 17 r (gate17_last16 r.val hr r.isLt)

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.FirstTwo
