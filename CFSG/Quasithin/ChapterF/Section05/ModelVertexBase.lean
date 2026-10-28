module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.Complete
public import Theory.SpecificGroups.ClassicalOrthogonal.OddFiveComparison

/-!
# The simple group in the F.5 model vertex

The literal projective unitary carrier in the marked source extension is
identified with the concrete elementary odd-five orthogonal group over F₃.
Both bounds in the exceptional unitary–symplectic comparison have been proved;
no order or recognition premise remains in this simple-group comparison.
The embedding into the six-space vertex and the outer involution are separate
markings, and are not inferred from an abstract equality of orders.

Source: Aschbacher–Smith F.5.1(1), printed p.300.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05

open GreenBook.LieModels
open Theory.SpecificGroups.HigherClassicalCovers

/-- The exact unitary base of the source extension has the actual odd-five model. -/
def modelUnitaryBaseEquivFive :
    UnitaryFour.ProjectiveGroup 1 (Nat.le_refl 1) ≃*
      ClassicalOrthogonal.OmegaOdd 2 (ZMod 3) :=
  ((UnitaryTwo.projectiveEquivStandard
      (UnitaryFour.standardForm 1 (Nat.le_refl 1))
      (by simpa using UnitaryFour.matrixField_card 1 (Nat.le_refl 1))
      (by intro x; exact UnitaryFour.fieldConj_apply 1 x)).trans
    UnitaryTwo.standardEquivPSp).trans
      (ClassicalOrthogonal.OddFiveComparison.pspEquivElementary (by decide))

end CFSG.Quasithin.ChapterF.Section05
