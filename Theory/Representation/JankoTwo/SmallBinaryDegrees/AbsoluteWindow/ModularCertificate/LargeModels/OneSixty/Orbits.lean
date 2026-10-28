module
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.Checks
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.OrbitArithmetic
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Binary160Basis

/-!
# The two literal degree-160 orbit bases

Each row-orbit step is checked against the earlier prefix recorded by the
untrusted ATLAS discovery. The left orbit uses transposed generators; the
transpose lemma reverses the words for the original column action. The left
basis is exactly the shared `Binary160Basis.leftBasis`. The remaining right
inverse is checked here, with every identity transported to any characteristic-
two field. Source: ATLAS J2G1-f2r160B0, `../source/README.md`.
-/
@[expose] public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty
open Data

private theorem transposeChecks :
    checkTranspose 160 a aTranspose = true ∧
    checkTranspose 160 b bTranspose = true ∧
    checkTranspose 160 Binary160Basis.leftBasis leftColumns = true := by
  exact ⟨Checks.transpose_a_check, Checks.transpose_b_check, Checks.transpose_basis_check⟩

private theorem orbitChecks :
    checkOrbit 160 aTranspose bTranspose column leftColumns leftParents leftLetters leftWords = true ∧
    checkOrbit 160 a b covector rightBasis rightParents rightLetters rightWords = true := by
  exact ⟨Checks.left_orbit_check, Checks.right_orbit_check⟩

private theorem rightInverseCheck : checkInverse 160 rightInverse rightBasis = true := by
  exact Checks.right_inverse_check

variable (F : Type*) [Field F] [CharP F 2]

/-- The saved left words are reversed for the original column action. -/
theorem left_orbit_identity (i : Fin 160) :
    (wordValue (Binary.eval F 160 a) (Binary.eval F 160 b) leftWords[i.val]!.reverse).mulVec
      (vector F 160 column) = fun k => Binary.eval F 160 Binary160Basis.leftBasis k i := by
  have h := orbit_sound F 160 aTranspose bTranspose column leftColumns leftParents
    leftLetters leftWords orbitChecks.1 i
  rw [← transpose_sound F 160 a aTranspose transposeChecks.1,
    ← transpose_sound F 160 b bTranspose transposeChecks.2.1,
    ← transpose_word, Matrix.vecMul_transpose] at h
  rw [h]
  funext k
  have ht := congrFun (congrFun
    (transpose_sound F 160 Binary160Basis.leftBasis leftColumns transposeChecks.2.2) i) k
  exact ht.symm

/-- The saved right words retain their displayed order. -/
theorem right_orbit_identity (i : Fin 160) :
    Matrix.vecMul (vector F 160 covector)
      (wordValue (Binary.eval F 160 a) (Binary.eval F 160 b) rightWords[i.val]!) =
      Binary.eval F 160 rightBasis i :=
  orbit_sound F 160 a b covector rightBasis rightParents rightLetters rightWords orbitChecks.2 i

/-- The second, previously unchecked, one-sided basis inverse. -/
theorem right_inverse_mul_basis :
    Binary.eval F 160 rightInverse * Binary.eval F 160 rightBasis = 1 :=
  Binary.eval_inverse F 160 rightInverse rightBasis (inverse_sound 160 _ _ rightInverseCheck)

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty
