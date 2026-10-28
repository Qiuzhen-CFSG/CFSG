module

public import Theory.AlgebraicGroup.CoordinateRing.CharZeroSmooth
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Kaehler

/-!
# Smoothness of finite-type commutative Hopf algebras in characteristic zero

A finite-type commutative Hopf algebra over a characteristic-zero field is
smooth.  Translation identifies its Kahler differentials with the scalar
extension of the cotangent space at the counit, so they form a free module.
The characteristic-zero free-differential criterion then gives smoothness.

This is the affine-algebra form of the Cartier smoothness theorem, Stacks
Project Lemma 39.8.2 (tag 047N).  The two inputs formalize the translation
argument of tag 047I and the local-to-global smoothness argument of tags 00TX
and 04QN.  In particular, the proof needs neither reducedness nor algebraic
closedness and does not construct a quotient by the reduced subgroup.
-/

universe u v

namespace Theory.AlgebraicGroup

/-- Every finite-type commutative Hopf algebra over a characteristic-zero
field is smooth.  This is Stacks Project tag 047N. -/
public theorem finiteType_commutativeHopfAlgebra_smooth
    (k : Type u) (A : Type v) [Field k] [CharZero k]
    [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A] :
    Algebra.Smooth k A := by
  let _ : Nontrivial A :=
    (Bialgebra.counit_surjective (R := k) (A := A)).nontrivial
  let _ : Module.Free A Ω[A⁄k] :=
    commutativeHopfAlgebra_kaehlerDifferential_free k A
  exact finiteType_charZero_smooth_of_kaehlerDifferential_free k A

end Theory.AlgebraicGroup
