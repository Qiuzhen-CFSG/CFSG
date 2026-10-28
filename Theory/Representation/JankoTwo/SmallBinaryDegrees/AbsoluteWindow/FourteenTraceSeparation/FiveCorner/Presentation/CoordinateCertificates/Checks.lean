module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.Arithmetic

/-!
# List-scan checks for the fixed coordinate arrays

The nine source arrays have exactly 1008 rows. Their list scans therefore
compute precisely `action`, avoiding repeated array lookup inside its defining
row sum. Numerical action certificates use `action_of_listProduct` and can
then be joined by `runWord_append_step` from the arithmetic module.

Source and bit convention: `Presentation/source/README.md`.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates
open PackedBinaryRows

lemma rows_size (k : Fin 9) : (rows k).size = 1008 := by
  fin_cases k <;> decide +kernel

lemma action_eq_listProduct (k : Fin 9) (x : ℕ) :
    action k x = listProduct x 0 (rows k).toList := by
  exact rowRange_eq_blockProduct x (fun i => (rows k)[i]!) 0 1008 (rows k)
    (rows_size k) (fun i => by rw [Nat.zero_add])

lemma action_of_listProduct {k : Fin 9} {x y : ℕ}
    (h : listProduct x 0 (rows k).toList = y) : action k x = y :=
  (action_eq_listProduct k x).trans h

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates
