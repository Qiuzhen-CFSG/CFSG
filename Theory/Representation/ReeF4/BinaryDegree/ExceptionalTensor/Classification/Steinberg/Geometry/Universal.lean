module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Coroots

/-!
# The character-lattice step toward universality of the concrete F4 carrier

The actual F4 root model realizes every integral weight by a torus character.
Its four standard coroots consequently define a morphism with surjective
character pullback. Once those coroots separate characters, their product is
an algebraic isomorphism onto the maximal torus.

The two remaining geometric obligations are character separation from
semisimplicity and construction of a reverse isogeny from this coroot-torus
isomorphism. No universality conclusion is asserted before those are proved.
In particular, a reverse isogeny need not be a regular inverse to an incoming
inseparable map. Sources: GLS3, Sections 1.10 and 1.12, especially 1.12.5(b).
-/

public section

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry

universe u

variable {F : Type u} [Field F] [IsAlgClosed F]

/-- The torus part of the universal-version criterion on the literal carrier,
with its remaining geometric character-separation input explicit. -/
theorem f4_corootProduct_iso_of_character_separation
    (model : RootSystemModel typeF4RootPairingULift (F4Chevalley.Carrier (k := F)))
    (hsep : Function.Injective model.f4CorootCoordinates) :
    letI := model.torus.carrierAlgebraicGroup
    ∃ e : Theory.AlgebraicGroup.Iso (dVariety F 4) model.torus.carrierVariety,
      e.hom = model.f4CorootProduct :=
  model.f4CorootProduct_iso_of_coordinates_injective hsep

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
