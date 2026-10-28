module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.LocalBound.Output
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.LocalBound.Check07

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/AmalgamPresentation/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.LocalBound.Certificate
open Subgroup.CosetWordCertificate

theorem shape_0 : allBlock shapeAt 8 0 = true := by decide +kernel

theorem shape_256 : allBlock shapeAt 8 256 = true := by decide +kernel

theorem shape_512 : allBlock shapeAt 8 512 = true := by decide +kernel

theorem shape_768 : allBlock shapeAt 8 768 = true := by decide +kernel

theorem shape_1024 : allBlock shapeAt 8 1024 = true := by decide +kernel

theorem shape_1280 : allBlock shapeAt 8 1280 = true := by decide +kernel

theorem shape_1536 : allBlock shapeAt 8 1536 = true := by decide +kernel

theorem shape_1792 : allBlock shapeAt 8 1792 = true := by decide +kernel

theorem shapeAt_true (i : Nat) (hi : i < 1632) : shapeAt i = true := by
  by_cases h0 : i < 256
  · exact allBlock_spec shapeAt 8 0 shape_0 i (by omega) h0
  by_cases h256 : i < 512
  · exact allBlock_spec shapeAt 8 256 shape_256 i (by omega) h256
  by_cases h512 : i < 768
  · exact allBlock_spec shapeAt 8 512 shape_512 i (by omega) h512
  by_cases h768 : i < 1024
  · exact allBlock_spec shapeAt 8 768 shape_768 i (by omega) h768
  by_cases h1024 : i < 1280
  · exact allBlock_spec shapeAt 8 1024 shape_1024 i (by omega) h1024
  by_cases h1280 : i < 1536
  · exact allBlock_spec shapeAt 8 1280 shape_1280 i (by omega) h1280
  by_cases h1536 : i < 1792
  · exact allBlock_spec shapeAt 8 1536 shape_1536 i (by omega) h1536
  exact allBlock_spec shapeAt 8 1792 shape_1792 i (by omega) (by omega)

/-- Every selected output is literally the required signed singleton transition. -/
theorem shape (i : Fin 1632) (a : Letter Bool) :
    facts (output i a) = ⟨survivor i, [a], survivor (dest i a)⟩ := by
  have h := shapeAt_true i.val i.isLt
  simp only [shapeAt, dif_pos i.isLt] at h
  apply (factBEq_eq_true_iff _ _).mp
  apply List.all_eq_true.mp h a
  rcases a with ⟨b, sign⟩
  cases b <;> cases sign <;> decide

end Sporadic.Janko3.AmalgamPresentation.LocalBound.Certificate
