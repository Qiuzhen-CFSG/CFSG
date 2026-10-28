module

public import Theory.Representation.Mathieu.M22James.Uniqueness.Reduction
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointExtension
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction

/-!
# Uniqueness of the binary 3.M₂₂ module

A module equivalence on the actual point stabilizer supplies binary
coordinates in which the two point-stabilizer actions agree literally.
Rigidity of extensions of that fixed action then yields a full intertwining
linear equivalence.

The final theorem is James (1973), Lemma 8.3, in the form used by
Aschbacher–Smith H.12.1(1), printed pp.393–394. The two substantive inputs are
proved in the point-restriction and point-extension modules.
-/

public section

namespace Sporadic.Mathieu.M22TripleCover.Uniqueness

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Conditional assembly from recognition on the point stabilizer and rigidity
of extensions of its concrete action. Both premises must be discharged before
this gives the source uniqueness theorem. -/
theorem equiv_of_pointStabilizer_inputs
    (ρ : Representation (ZMod 2) M22TripleCover W) [ρ.IsIrreducible]
    (hf : Function.Injective ρ)
    (hrestriction : Nonempty
      (Representation.Equiv (ρ.comp pointStabilizer.subtype) pointRepresentation))
    (hextension : ∀ τ : Representation (ZMod 2) M22TripleCover BinarySpace,
      Function.Injective τ → τ.IsIrreducible →
      (∀ g : pointStabilizer, τ g = binaryRepresentation g) →
      Nonempty (Representation.Equiv τ binaryRepresentation)) :
    Nonempty (Representation.Equiv ρ binaryRepresentation) := by
  obtain ⟨e⟩ := hrestriction
  obtain ⟨f⟩ := hextension (coordinateRepresentation ρ e.toLinearEquiv)
    (coordinateRepresentation_faithful ρ hf e.toLinearEquiv)
    (coordinateRepresentation_irreducible ρ e.toLinearEquiv)
    (coordinateRepresentation_on_pointStabilizer ρ e)
  exact ⟨(coordinateEquiv ρ e.toLinearEquiv).trans f⟩

/-- Every faithful irreducible twelve-dimensional binary module of the genuine
triple cover is equivalent to the constructed binary module.

This is the source uniqueness assertion in James (1973), Lemma 8.3, used in
Aschbacher–Smith H.12.1(1), printed pp.393–394. -/
theorem equiv_of_finrank_twelve
    (ρ : Representation (ZMod 2) M22TripleCover W) [ρ.IsIrreducible]
    (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 12) :
    Nonempty (Representation.Equiv ρ binaryRepresentation) := by
  apply equiv_of_pointStabilizer_inputs ρ hf
  · exact point_equiv_of_finrank_twelve ρ hf hd
  · intro τ hτf hτi hag
    exact PointExtension.extension_equiv τ hτf hτi hag

end Sporadic.Mathieu.M22TripleCover.Uniqueness
