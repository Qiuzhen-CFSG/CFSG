module

public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Orbits.Checks
public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Orbits.Extension
/-!
# The two literal maps preserve the actual alternating quartic

The finite certificates have the same values on all increasing basis
quadruples. Their proved evaluator bridge identifies these values with the
sum of coordinate determinants in `Basic.lean`; alternation and multilinearity
then give preservation for arbitrary four arguments. No orbit or stabilizer
identification enters the proof.
-/

public section

namespace BinaryQuarticMathieu.RankRecognition.Orbits
attribute [local irreducible] quartic

theorem quartic_basis_value (i : Fin 210) :
    quartic (fun j => basisVector (quadruple i j)) =
      bitField (coefficientWord.testBit i.val) := by
  have h := congrArg bitField (basis_values i)
  rw [bitField_boolQuartic] at h
  simpa only [fastQuad_eq, ← basisVector_word] using h

theorem generatorA_preserves : Preserves quartic generatorA := by
  apply preserves_of_quadruple
  intro i
  calc
    quartic (fun j => generatorA (basisVector (quadruple i j))) =
        bitField (coefficientWord.testBit i.val) := by
      have h := congrArg bitField (generatorA_values i)
      rw [bitField_boolQuartic] at h
      have he : (fun j => generatorA (basisVector (quadruple i j))) =
          (fun j => vector (columnsA (fastQuad i j))) := by
        funext j
        rw [fastQuad_eq]
        exact generatorA_columns _
      rw [he]
      exact h
    _ = quartic (fun j => basisVector (quadruple i j)) := (quartic_basis_value i).symm

theorem generatorB_preserves : Preserves quartic generatorB := by
  apply preserves_of_quadruple
  intro i
  calc
    quartic (fun j => generatorB (basisVector (quadruple i j))) =
        bitField (coefficientWord.testBit i.val) := by
      have h := congrArg bitField (generatorB_values i)
      rw [bitField_boolQuartic] at h
      have he : (fun j => generatorB (basisVector (quadruple i j))) =
          (fun j => vector (columnsB (fastQuad i j))) := by
        funext j
        rw [fastQuad_eq]
        exact generatorB_columns _
      rw [he]
      exact h
    _ = quartic (fun j => basisVector (quadruple i j)) := (quartic_basis_value i).symm
end BinaryQuarticMathieu.RankRecognition.Orbits
