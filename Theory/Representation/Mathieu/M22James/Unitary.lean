module

public import Theory.Representation.Mathieu.M22James.Unitary.Realization

/-!
# The genuine triple Mathieu unitary module

The native twelve-dimensional binary module has a nondegenerate invariant
Hermitian form for the scalars supplied by its actual central element. Its
diagonal defines an invariant binary quadratic form. The checked coordinates
give a faithful realization in the literal special unitary group SU₆(2), with
both the group action and the specified field scalars explicitly intertwined.

The construction uses the native ATLAS generators, finite coordinate
certificates, and their proved generating closure; it assumes no character
table or existence of a form. `invariant_forms_exist` assembles the native
form assertion of Aschbacher–Smith H.12.1(2), printed pp.393–394. The actual
embedding and coordinate equivalence are `unitaryAction` and
`standardCoordinates`. Arbitrary triple-cover transport remains with the
chapter's recognition assembly.
-/

@[expose] public section
noncomputable section

namespace Sporadic.Mathieu.M22TripleCover.Unitary

open Representation.SL2FourNatural
open Uniqueness.PointRestriction (fieldModule)

local instance : Module F BinarySpace :=
  fieldModule binaryRepresentation binaryRepresentation_faithful

/-- The invariant Hermitian form and its binary quadratic diagonal on the actual module. -/
theorem invariant_forms_exist :
    ∃ (f : BinarySpace →ₗ[F] BinarySpace →ₛₗ[fieldFrobenius.toRingHom] F)
      (q : QuadraticForm (ZMod 2) BinarySpace),
      f.Nondegenerate ∧
      (∀ v w, fieldFrobenius (f v w) = f w v) ∧
      (∀ g v w, f (binaryRepresentation g v) (binaryRepresentation g w) = f v w) ∧
      (∀ v, algebraMap (ZMod 2) F (q v) = f v v) ∧
      (∀ g v, q (binaryRepresentation g v) = q v) :=
  ⟨hermitianForm, quadraticForm, hermitianForm_nondegenerate,
    hermitianForm_symmetry, hermitianForm_invariant, quadraticForm_diagonal,
    quadraticForm_invariant⟩

end Sporadic.Mathieu.M22TripleCover.Unitary
