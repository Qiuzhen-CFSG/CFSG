module

public import Theory.Representation.Mathieu.M22James.Irreducible
public import Theory.Representation.Quotient

/-!
# The constructed binary module for 3.M₂₂

The genuine triple cover has a faithful irreducible binary representation
of dimension twelve. An actual group isomorphism transports this module,
including its distinguished central scalar action, to another carrier.

This is the existence construction used for James (1973), Lemma 8.3, as
cited in Aschbacher–Smith H.12.1(1), printed pp.393–394. It does not yet
identify an arbitrary quasisimple triple cover with the concrete carrier,
prove the degree lower bound, or classify the modules of degree twelve.
Those are separate mathematical obligations, not assumptions hidden in
the carrier or in the representation.
-/

@[expose] public section

namespace Sporadic.Mathieu.M22TripleCover

variable {L : Type*} [Group L]

/-- Transport the constructed action through an actual group isomorphism. -/
noncomputable def representationOfEquiv (e : L ≃* M22TripleCover) :
    Representation (ZMod 2) L BinarySpace :=
  binaryRepresentation.comp e.toMonoidHom

theorem representationOfEquiv_faithful (e : L ≃* M22TripleCover) :
    Function.Injective (representationOfEquiv e) :=
  binaryRepresentation_faithful.comp e.injective

instance representationOfEquiv_irreducible (e : L ≃* M22TripleCover) :
    Representation.IsIrreducible (representationOfEquiv e) :=
  (Representation.irreducible_comp_surjective_iff e.toMonoidHom e.surjective
    binaryRepresentation).mpr binaryRepresentation_irreducible

theorem representationOfEquiv_scalar (e : L ≃* M22TripleCover) :
    representationOfEquiv e (e.symm scalar) = binaryRepresentation scalar := by
  change binaryRepresentation (e (e.symm scalar)) = _
  rw [e.apply_symm_apply]

theorem exists_faithful_irreducible_twelve_of_equiv (e : L ≃* M22TripleCover) :
    ∃ ρ : Representation (ZMod 2) L BinarySpace,
      Function.Injective ρ ∧ Representation.IsIrreducible ρ ∧
      Module.finrank (ZMod 2) BinarySpace = 12 :=
  ⟨representationOfEquiv e, representationOfEquiv_faithful e,
    representationOfEquiv_irreducible e, binarySpace_finrank⟩

end Sporadic.Mathieu.M22TripleCover
