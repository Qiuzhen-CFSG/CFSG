module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ChevalleySplitTorus
public import Theory.AlgebraicGroup.Variety.AffineSpace
public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues.Coordinates

/-!
# The literal F4 torus and root parameter space

The explicit enumeration of the Euclidean F4 roots identifies the actual root
index with 48 coordinates. Together with the actual split torus, these affine
coordinates form the parameter space for the geometric dimension argument.
No dominance or Bruhat coverage is asserted here.

Source: GLS3, §§1.11–1.12, `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section

namespace Theory.AlgebraicGroup.F4Chevalley

/-- The literal root subtype has 48 elements. -/
theorem concreteRoot_card : Fintype.card Root = 48 := by
  simpa using
    (Fintype.card_congr ReeF4.Cartan.FieldSeparation.TraceValues.rootEquiv).symm

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- One actual split-torus factor and one affine coordinate for each literal
root. The lift only matches the coordinate universe to the coefficient field. -/
@[expose] noncomputable def concreteRootParameterSpace : Variety k :=
  Variety.prod (splitTorus (k := k)).carrierVariety
    (affineSpaceVariety k (ULift.{u} Root))

end Theory.AlgebraicGroup.F4Chevalley
