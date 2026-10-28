module

public import Theory.AlgebraicGroup.ClosedSubgroup.IntersectionHopf
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.CharZero

/-!
# Characteristic-zero closed-subgroup intersections

For closed algebraic subgroups `B` and `C`, their scheme-theoretic
intersection has coordinate algebra obtained by quotienting by the sum of
their vanishing ideals.  `IntersectionHopf` gives this quotient its canonical
finite-type Hopf algebra structure.  Cartier reducedness in characteristic
zero therefore shows that the quotient is reduced.

The algebraically closed hypothesis is retained at this assembly boundary so
that the result feeds directly into the Nullstellensatz comparison between
the quotient ideal and the vanishing ideal of the pointwise intersection.
The resulting ideal equality control is the algebraic input for exact
tangent-intersection results.
-/

universe u

namespace Theory.AlgebraicGroup

set_option linter.style.haveILetI false in
/-- The scheme-theoretic intersection of two closed algebraic subgroups over
an algebraically closed characteristic-zero field has reduced coordinate
algebra. -/
public theorem ClosedSubgroup.intersectionQuotient_isReduced_charZero
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {G : Variety k} [AlgebraicGroup G] (B C : ClosedSubgroup G) :
    IsReduced
      (G.PolynomialFunction ⧸
        (B.vanishingIdeal ⊔ C.vanishingIdeal)) := by
  let hHopf : HopfAlgebra k
      (G.PolynomialFunction ⧸
        (B.vanishingIdeal ⊔ C.vanishingIdeal)) :=
    B.intersectionQuotientHopfAlgebra C
  letI : Algebra k
      (G.PolynomialFunction ⧸
        (B.vanishingIdeal ⊔ C.vanishingIdeal)) :=
    hHopf.toAlgebra
  letI : HopfAlgebra k
      (G.PolynomialFunction ⧸
        (B.vanishingIdeal ⊔ C.vanishingIdeal)) :=
    hHopf
  letI : Algebra.FiniteType k
      (G.PolynomialFunction ⧸
        (B.vanishingIdeal ⊔ C.vanishingIdeal)) :=
    B.intersectionQuotientHopfAlgebra_finiteType C
  exact finiteType_commutativeHopfAlgebra_isReduced k _

/-- Over an algebraically closed characteristic-zero field, the vanishing
ideal of a pointwise intersection is contained in the sum of the two subgroup
vanishing ideals. -/
public theorem ClosedSubgroup.inter_vanishingIdeal_le_sup_charZero
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {G : Variety k} [AlgebraicGroup G] (B C : ClosedSubgroup G) :
    (B.inter C).vanishingIdeal ≤
      B.vanishingIdeal ⊔ C.vanishingIdeal := by
  exact B.inter_vanishingIdeal_le_sup_of_isReduced C
    (B.intersectionQuotient_isReduced_charZero C)

end Theory.AlgebraicGroup
