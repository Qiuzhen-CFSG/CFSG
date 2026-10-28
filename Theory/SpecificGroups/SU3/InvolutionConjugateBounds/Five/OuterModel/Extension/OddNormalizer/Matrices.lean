module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.InnerModel.Embedding.Matrices
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.UnitaryConjugation

/-!
# A unitary Frobenius intertwiner for the Suzuki matrices

An explicit basis changes the existing A₇ matrices to the antidiagonal
Hermitian form. In this basis a single unitary matrix, followed by fifth
power on coefficients, inverts all five Suzuki generators. The tail
generators are involutions only projectively; the calculation retains their
actual special-unitary lifts and does not discard their cubic scalar defects.

These small matrix identities supply the Frobenius calculation used in
Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3, pp.10–11.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer.OddNormalizer
open Matrix BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Embedding
open OddPrimeSylow.NormalizedOuter.FormTransport

abbrev fieldForm := standardForm matrixForm

/-- A basis carrying the existing Gram matrix to the antidiagonal one. -/
def basisMatrix : Matrix (Fin 3) (Fin 3) F25 :=
  !![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩;
    ⟨1, 0⟩, ⟨4, 4⟩, ⟨3, 0⟩;
    ⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩]

def inverseBasisMatrix : Matrix (Fin 3) (Fin 3) F25 :=
  !![⟨3, 1⟩, ⟨2, 0⟩, ⟨4, 0⟩;
    ⟨3, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨2, 2⟩, ⟨3, 0⟩, ⟨2, 0⟩]

def basisUnit : GL (Fin 3) F25 where
  val := basisMatrix
  inv := inverseBasisMatrix
  val_inv := by decide
  inv_val := by decide

theorem basisUnit_form :
    matrixForm.conjTranspose basisUnit.val * matrixForm.form * basisUnit.val =
      fieldForm.form := by decide

def intertwinerMatrix : Matrix (Fin 3) (Fin 3) F25 :=
  !![⟨2, 1⟩, ⟨3, 4⟩, ⟨0, 2⟩;
    ⟨0, 1⟩, ⟨4, 2⟩, ⟨3, 4⟩;
    ⟨4, 3⟩, ⟨0, 1⟩, ⟨2, 1⟩]

def intertwinerUnit : GL (Fin 3) F25 where
  val := intertwinerMatrix
  inv := !![⟨3, 4⟩, ⟨2, 1⟩, ⟨2, 3⟩;
    ⟨1, 4⟩, ⟨1, 3⟩, ⟨2, 1⟩;
    ⟨2, 2⟩, ⟨1, 4⟩, ⟨3, 4⟩]
  val_inv := by decide
  inv_val := by decide

def intertwiner : fieldForm.unitarySubgroup :=
  ⟨intertwinerUnit, by rw [mem_unitarySubgroup_iff]; decide⟩

/-- The original lifts in the antidiagonal basis. -/
def transportedGenerator (i : Fin 5) : fieldForm.specialSubgroup :=
  specialEquiv matrixForm basisUnit basisUnit_form (specialGenerator i)

/-- The identity has no suppressed scalar: Frobenius followed by the
intertwiner sends each actual lift to its inverse. -/
theorem generator_intertwining (i : Fin 5) :
    (transportedGenerator i).val * intertwiner.val *
      GeneralLinearGroup.map fieldForm.conj.toRingHom (transportedGenerator i).val =
        intertwiner.val := by
  simp only [transportedGenerator, specialEquiv_apply]
  apply Units.ext
  change (inverseBasisMatrix * generatorMatrix i * basisMatrix) * intertwinerMatrix *
    (inverseBasisMatrix * generatorMatrix i * basisMatrix).map F25.conjugation =
      intertwinerMatrix
  revert i
  decide

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer.OddNormalizer
