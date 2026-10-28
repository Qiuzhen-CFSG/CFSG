module

public import Theory.Representation.Mathieu.M22James.Uniqueness.Reduction
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.CentralField
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.ExtensionExclusion

/-!
# Recognition on the Mathieu point stabilizer

Every faithful irreducible twelve-dimensional binary module for the triple
cover restricts to the literal point representation. The actual central scalar
satisfies the quadratic relation, so transport through the marked subgroup
isomorphism puts the entire restriction in the complete SL₃(4) catalogue.
The full-group extension equations exclude the competing entries, and the
surviving whole-module equivalence transports back to the point stabilizer.

The field-reduction interface also identifies binary recognition with
recognition over the four-element field supplied by the actual central
element. No irreducibility or semisimplicity of the restriction is assumed.

This is the restriction step for James (1973), Lemma 8.3, as used in
Aschbacher–Smith H.12.1(1), printed pp.393–394. Full-group uniqueness is
assembled separately with rigidity of extensions of this fixed action.
-/

public section

namespace Sporadic.Mathieu.M22TripleCover.Uniqueness

open Representation
open PointRestriction

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) M22TripleCover W) [ρ.IsIrreducible]
  (hf : Function.Injective ρ)

/-- The exact restricted-module target can be checked over its canonical
central field, with the original point stabilizer and scalar retained. -/
theorem point_equiv_iff_field :
    Nonempty (Representation.Equiv (ρ.comp pointStabilizer.subtype) pointRepresentation) ↔
      (letI := fieldModule ρ hf
       letI := fieldModule binaryRepresentation binaryRepresentation_faithful
       Nonempty (Representation.Equiv (pointFieldRepresentation ρ hf)
         (pointFieldRepresentation binaryRepresentation binaryRepresentation_faithful))) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨pointEquivOverField ρ hf e⟩
  · rintro ⟨e⟩
    exact ⟨pointEquivOfField ρ hf e⟩

/-! The next reduction supplies the catalogue input to local recognition.
Transporting the literal restriction through the actual subgroup equivalence
puts it in the finite SL₃(4) catalogue. The final theorem selects the reference
module using the proved full-group extension exclusion.
-/

open PointRestriction.PointModel
open Representation.SL3FourLocalCatalogue

/-- The transported point restriction is one of the explicit central-quadratic
SL₃(4) catalogue entries.  This keeps the actual subgroup equivalence and the
central scalar marking; it does not identify which entry extends to the full
triple cover. -/
theorem exists_point_catalogue_entry
    (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 12) :
    ∃ i : CatalogueEntry,
      let σ : Representation (ZMod 2) PointModel.Reference.SL W :=
        (ρ.comp pointStabilizer.subtype).comp pointStabilizerEquiv.symm.toMonoidHom
      Nonempty (σ.Equiv (catalogueRepresentation i)) := by
  let e : pointStabilizer ≃* PointModel.Reference.SL := pointStabilizerEquiv
  let σ : Representation (ZMod 2) PointModel.Reference.SL W :=
    (ρ.comp pointStabilizer.subtype).comp e.symm.toMonoidHom
  have hq : CentralQuadratic σ := by
    change σ SL3FourNaturalDual.centralScalar ^ 2 +
      σ SL3FourNaturalDual.centralScalar + 1 = 0
    have hs : (e.symm SL3FourNaturalDual.centralScalar : pointStabilizer) =
        pointScalar := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact pointStabilizerEquiv_pointScalar.symm
    have h := scalar_quadratic ρ hf
    change ρ ((e.symm SL3FourNaturalDual.centralScalar : pointStabilizer) :
        M22TripleCover) ^ 2 +
      ρ ((e.symm SL3FourNaturalDual.centralScalar : pointStabilizer) :
        M22TripleCover) + 1 = 0
    rw [hs]
    exact h
  obtain ⟨i, hi⟩ := classify σ hq hd
  exact ⟨i, hi⟩

/-- Every faithful irreducible twelve-dimensional binary module restricts to
the entire literal point representation, including its nonsplit extension
structure and its distinguished central action. -/
theorem point_equiv_of_finrank_twelve
    (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 12) :
    Nonempty (Representation.Equiv (ρ.comp pointStabilizer.subtype) pointRepresentation) := by
  obtain ⟨i, ⟨e⟩⟩ := exists_point_catalogue_entry ρ hf hd
  exact ExtensionExclusion.point_equiv_of_catalogue ρ i e

end Sporadic.Mathieu.M22TripleCover.Uniqueness
