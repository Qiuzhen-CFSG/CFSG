module

public import Theory.Representation.G2.RestrictedModules.Adjoint.Irreducible
public import Theory.Representation.G2.RestrictedModules.Adjoint.HighestWeight
public import Theory.Representation.G2.RestrictedModules.Adjoint.FieldTransport

/-!
# The actual characteristic-two G₂ adjoint factor

The carrier consists of all Leibniz derivations of the literal split-octonion
multiplication, acted on by conjugation by the actual octonion automorphism group.
It has the explicit fourteen-element `basis`, is absolutely irreducible, and
remains irreducible after every scalar extension. These statements hold over
every characteristic-two field, hence in particular over fields of order 2ⁿ
with n ≥ 2.

The highest derivation is x ↦ [x₆,x₇,0,0,0,0,0,0]. Its line is exactly the
positive-unipotent fixed space. Its torus character l*m has short/long coroot
pairings (0,1), namely GLS3's λ₁. Coefficient conjugation gives an actual
semilinear equivalence, intertwining the group's field automorphism, including
Frobenius and arbitrary scalar extensions. The coordinate interface re-exported
here includes formulas for all six root groups, both Weyl maps, and the torus.

Source: GLS3, Examples 1.14.9(c), 2.8.10(g); Aschbacher–Smith, G.9.3,
printed pp.354,356–357. This supplies the adjoint factor; the four-factor catalogue
and tensor-product classification are separate assembly results.
-/

@[expose] public section

namespace Atlas.G2.Restricted.Adjoint

variable (F : Type*) [Field F] [CharP F 2]

/-- The actual split-octonion derivation space is fourteen-dimensional. -/
theorem finrank : Module.finrank F (Space F) = 14 := Coordinates.finrank F

/-- Absolute irreducibility of the actual adjoint factor. -/
theorem absolutelyIrreducible :
    Representation.IsAbsolutelyIrreducible (F := F) (V := Space F) (action F) :=
  Coordinates.adjoint_absolutelyIrreducible F

/-- Irreducibility is retained after arbitrary field extension. -/
theorem irreducible_extendScalars (K : Type*) [Field K] [Algebra F K] :
    Representation.IsIrreducible
      (Representation.extendScalars (F := F) (V := Space F) K (action F)) :=
  Coordinates.adjoint_irreducible_extendScalars F K

end Atlas.G2.Restricted.Adjoint
