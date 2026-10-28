module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Theory.AlgebraicGroup.ClosedSubgroup.Invariant

universe u

/-! Noetherian descent for the right-invariant coordinate ring. -/

namespace Theory.AlgebraicGroup

/-- Faithful flatness of the ambient coordinate ring makes the invariant
coordinate ring Noetherian. -/
public theorem rightInvariantCoordinateRing_isNoetherian_of_faithfullyFlat
    {k : Type u} [Field k] {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G)
    [Module.FaithfullyFlat
      (AlgebraicGroup.rightInvariantCoordinateRing H)
      (Variety.PolynomialFunction G)] :
    IsNoetherianRing (AlgebraicGroup.rightInvariantCoordinateRing H) := by
  let B := AlgebraicGroup.rightInvariantCoordinateRing H
  let A := Variety.PolynomialFunction G
  let : Algebra.FiniteType k A := polynomialFunction_finiteType G
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  rw [isNoetherianRing_iff]
  apply Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
    (R := B) (M := B) (A := A)
  exact isNoetherian_of_linearEquiv
    (Algebra.TensorProduct.rid B A A).symm.toLinearEquiv

end Theory.AlgebraicGroup
