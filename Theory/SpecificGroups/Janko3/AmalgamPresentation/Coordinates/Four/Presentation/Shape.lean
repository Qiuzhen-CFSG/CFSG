module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.Presentation.Output
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.Presentation.Check03

/-! Kernel-checked five-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/AmalgamPresentation/Coordinates/Four/Presentation/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.FourCoordinates.Presentation.Certificate
open Subgroup.CosetWordCertificate

theorem shape_0 : allBlock shapeAt 8 0 = true := by decide +kernel

theorem shape_256 : allBlock shapeAt 8 256 = true := by decide +kernel

theorem shapeAt_true (i : Nat) (hi : i < 480) : shapeAt i = true := by
  by_cases h0 : i < 256
  · exact allBlock_spec shapeAt 8 0 shape_0 i (by omega) h0
  exact allBlock_spec shapeAt 8 256 shape_256 i (by omega) (by omega)

/-- Every selected output is literally the required signed singleton transition. -/
theorem shape (i : Fin 480) (a : Letter Bool) :
    facts (output i a) = ⟨survivor i, [a], survivor (dest i a)⟩ := by
  have h := shapeAt_true i.val i.isLt
  simp only [shapeAt, dif_pos i.isLt] at h
  apply (factBEq_eq_true_iff _ _).mp
  apply List.all_eq_true.mp h a
  rcases a with ⟨b, sign⟩
  cases b <;> cases sign <;> decide

end Sporadic.Janko3.AmalgamPresentation.FourCoordinates.Presentation.Certificate
