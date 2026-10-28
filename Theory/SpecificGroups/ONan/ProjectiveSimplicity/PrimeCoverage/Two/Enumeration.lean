module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Enumeration.Transport

/-!
# Assembly of the O'Nan binary normal-form certificates

Three independent finite certificates suffice: evaluation of the nine fixed
words, collection of right multiplication by each basis matrix, and separation
of the first rows of binary products up to nonzero scalar. The transport proof
uses the actual projective matrix model. The explicit inputs and their ATLAS
provenance are recorded in `Two/source/README.md` and `Enumeration/BasisData.lean`.
-/

namespace ONan.Simplicity.TwoCertificate

open Enumeration

/-- Assemble the two normal-form conclusions from concrete matrix certificates. -/
public theorem normalForms_of_matrix_certificates
    (heval : ∀ i, (linearGenerators i : Mat) = basisMatrices i)
    (hstep : ∀ v i, ∃ w,
      matrixForm basisMatrices w = matrixForm basisMatrices v * basisMatrices i)
    (hsep : ∀ v w (u : (ZMod 7)ˣ),
      (∀ j, matrixForm basisMatrices v 0 j * u.val = matrixForm basisMatrices w 0 j) →
        v = w) :
    Subgroup.BinaryNormalForm.DivisionClosed generators ∧ Function.Injective normalForm :=
  ⟨divisionClosed_of_matrix_steps basisMatrices heval hstep,
    injective_of_matrix_separation basisMatrices heval hsep⟩

end ONan.Simplicity.TwoCertificate
