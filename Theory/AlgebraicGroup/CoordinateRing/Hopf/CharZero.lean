module

public import Mathlib.Algebra.CharZero.Infinite
public import Theory.AlgebraicGroup.Bor1.SmoothReduced
public import Theory.AlgebraicGroup.Bor1.CoordinateRingSmooth
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.CharZeroSmooth
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Invariant
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.FiniteLocal
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Presentation

universe u v

namespace Theory.AlgebraicGroup

/-!
Finite-type commutative Hopf algebras over a characteristic-zero field are
smooth, by the affine Cartier theorem, and hence reduced.  The smoothness
endpoint is imported from `Hopf.CharZeroSmooth`; the reducedness endpoint
below transports it through the field-smooth reducedness theorem, and the
nilradical endpoint records the same result in ideal form for quotient
consumers.  The module also retains the reduced-input smoothness API for
invariant coordinate rings of normal closed subgroups.

The finite-local Hopf theorem is re-exported for zero-dimensional local
applications.  The global result does not require an algebraically closed
field or a quotient by the reduced subgroup.
-/

variable {k A : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [CommRing A] [HopfAlgebra k A]

set_option linter.style.haveILetI false in
/-- Every finite-type commutative Hopf algebra over a characteristic-zero
field is reduced. -/
public theorem finiteType_commutativeHopfAlgebra_isReduced
    (k : Type u) (A : Type v) [Field k] [CharZero k]
    [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A] :
    IsReduced A := by
  let _ : Algebra.Smooth k A :=
    finiteType_commutativeHopfAlgebra_smooth k A
  exact Bor1.isReduced_of_smooth_of_field (K := k) (A := A)

/-- The nilradical of a finite-type commutative Hopf algebra over a
characteristic-zero field vanishes. -/
public theorem finiteType_commutativeHopfAlgebra_nilradical_eq_bot
    (k : Type u) (A : Type v) [Field k] [CharZero k]
    [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A] :
    nilradical A = ⊥ :=
  nilradical_eq_bot_iff.mpr
    (finiteType_commutativeHopfAlgebra_isReduced k A)

set_option linter.unusedSectionVars false in
/-- Smoothness of a finite-type Hopf algebra once its reducedness is known.

The finite radical presentation identifies the algebra with the polynomial
function ring of an affine algebraic group, and smoothness is transported
back across that algebra equivalence. -/
public theorem finiteTypeHopfAlgebra_smooth_of_isReduced
    [Algebra.FiniteType k A] [IsReduced A] :
    Algebra.Smooth k A := by
  have _hchar : Function.Injective (Nat.cast : ℕ → k) := CharZero.cast_injective
  obtain ⟨P⟩ := ReducedFiniteTypeAlgebraPresentation.exists k A
  let _ := P.algebraicGroup
  have hP : Algebra.Smooth k (Variety.PolynomialFunction P.toVariety) :=
    Bor1.polynomialFunction_smooth_of_algebraicGroup P.toVariety
  exact hP.of_equiv P.polynomialFunctionAlgEquiv.symm

set_option linter.style.haveILetI false in
set_option linter.unusedSectionVars false in
/-- The invariant coordinate Hopf algebra of a finite-type normal closed
subgroup is smooth over the base field. -/
public theorem rightInvariantCoordinateRing_smooth_of_finiteType
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal)
    [Algebra.FiniteType k (rightInvariantCoordinateRing H)] :
    Algebra.Smooth k (rightInvariantCoordinateRing H) := by
  have _hchar : Function.Injective (Nat.cast : ℕ → k) := CharZero.cast_injective
  letI : HopfAlgebra k (rightInvariantCoordinateRing H) :=
    rightInvariantCoordinateHopfAlgebra H hN
  letI : IsReduced (rightInvariantCoordinateRing H) :=
    rightInvariantCoordinateRing_isReduced H
  exact finiteTypeHopfAlgebra_smooth_of_isReduced

end Theory.AlgebraicGroup
