module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Contracts
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Density.Orbit

/-!
# Full matrix-algebra density of the degree-sixteen generators

The literal ATLAS matrices generate the full matrix algebra over every
characteristic-two field containing a root of `X⁴+X+1`. A checked polynomial
in their product is rank one. Its left and right generator orbits each have
sixteen vectors, with checked inverse matrices, so their outer products span
all matrices. The finite arithmetic is interpreted in the given field;
neither a group action nor irreducibility is assumed.

This discharges exactly `SixteenModels.GeneratorDensity`, independently of
the native-action certificate. The application to `irreducible_of_realizes`
is in `Density.Irreducibility`.

Source: ATLAS L33G1-f16r16aB0, with the coefficient convention and attribution
in `SixteenModels.Data`; GM02 Proposition 4.2, manuscript pp.9–10.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels
universe v

/-- The literal two generator matrices span the full algebra, in every field universe. -/
theorem generatorDensity : GeneratorDensity.{v} := by
  intro F _ _ t ht
  apply Density.subalgebra_eq_top t ht
  · exact Algebra.subset_adjoin (by simp)
  · exact Algebra.subset_adjoin (by simp)

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels
