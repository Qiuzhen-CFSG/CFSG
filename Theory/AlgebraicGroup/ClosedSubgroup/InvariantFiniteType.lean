module

public import Theory.AlgebraicGroup.Bor1.ExactKernelClosedImageSeparableProjection
public import Theory.AlgebraicGroup.Bor1.InvariantPullbackSurjective

/-!
# Finite generation of normal invariant coordinates

For a normal closed subgroup `H` of an affine algebraic group `G` over an
algebraically closed field, the algebra of polynomial functions on `G` that
are invariant under right translation by `H` is finite type over the base
field.  This supplies the finite-generation input for the affine quotient
construction in `ClosedSubgroup.InvariantQuotient`.

The proof follows the normal-subgroup case of Bor1, Theorem 6.8, using the
exact point-and-differential-kernel representation constructed from Chevalley
weight spaces.  Its closed image is an affine algebraic group, and the induced
projection is surjective both on points and on the identity tangent space.
Faithfully flat invariant descent identifies the full invariant-coordinate
ring as a quotient of the closed image's finite-type coordinate ring.
-/

namespace Theory.AlgebraicGroup

universe u

set_option linter.style.haveILetI false

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The right-invariant coordinate ring of a normal closed subgroup is a
finite-type algebra over the base field. -/
public theorem ClosedSubgroup.rightInvariantCoordinateRing_finiteType
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    Algebra.FiniteType k (AlgebraicGroup.rightInvariantCoordinateRing H) := by
  obtain ⟨P⟩ :=
    Bor1.ClosedSubgroup.chevalleyWeightBlockExactDifferentialKernel_nonempty H hN
  letI : AddCommGroup P.V := P.addCommGroup
  letI : Module k P.V := P.module
  letI : FiniteDimensional k P.V := P.finiteDimensional
  let Q := P.morphism.imageClosedSubgroup
  letI : AlgebraicGroup Q.carrierVariety := Q.carrierAlgebraicGroup
  obtain ⟨pi, hpiSurj, hpiKer, -, hpiDifferential⟩ :=
    P.closedImageProjection_exactTangentKernel_surjective_exists H
  let pullback := pi.pullbackToRightInvariantCoordinateRing H (by rw [hpiKer])
  have hpullback : Function.Surjective pullback :=
    Bor1.pullbackToRightInvariantCoordinateRing_surjective
      H pi hpiSurj hpiKer hpiDifferential
  letI : Algebra.FiniteType k (Variety.PolynomialFunction Q.carrierVariety) :=
    polynomialFunction_finiteType Q.carrierVariety
  exact Algebra.FiniteType.of_surjective pullback hpullback

end Theory.AlgebraicGroup
