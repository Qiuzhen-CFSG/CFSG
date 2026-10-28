module

public import Theory.Representation.QuadraticFourGroup.Recognition.Burnside.FieldCoordinates.LocalAction
public import Theory.Representation.QuadraticFourGroup.Recognition.Burnside.Coordinates

/-!
# Scalar coordinates for a marked pair of Sylow subgroups

`ScalarCoordinates P Q K` identifies the root group P with the additive
group of K and the actual two-point stabilizer with its units, compatibly
with conjugation. It is an intermediate construction contract, not a
hypothesis of an unconditional recognition theorem. Its existence must be
proved from the abelian regular action in `LocalAction`.

Unlike `SylowCoordinates`, this record contains no projective-line action,
reciprocal permutation, or assertion about the whole group image. The orbit
construction in `Additive` extends its additive equivalence to actual points.

Source: Burnside (1900), pp. 274–276,
`refs/original/burnside-1900.pdf`.
-/

@[expose] public section
namespace Representation.QuadraticFourGroup.Burnside

open Theory.GroupTheory.InvolutionOddSpectrum

variable {G K : Type*} [Group G] [Field K]

/-- Additive and multiplicative coordinates compatible with actual conjugation.
The field on the right is to be constructed from the regular abelian action. -/
structure ScalarCoordinates (P Q : Sylow 2 G) (K : Type*) [Field K] where
  additive : Additive P ≃+ K
  scalars : twoPoint P Q ≃* Kˣ
  conjugation : ∀ (d : twoPoint P Q) (x : P),
    additive (Additive.ofMul (twoPointConj P Q d x)) =
      (scalars d : K) * additive (Additive.ofMul x)

end Representation.QuadraticFourGroup.Burnside
end
