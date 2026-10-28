module

public import Theory.AlgebraicGroup.CoordinateRing.Hopf.PrimitiveCurveSeparableCoreCharP
public import Theory.FieldTheory.PurelyInseparableRationalFunctionField

/-!
# Rationality of primitive Hopf-curve function fields in positive characteristic

Let `t` be a transcendental primitive element of a normal affine Hopf curve over
an algebraically closed field of characteristic `p`.  This module proves that
the curve's fraction field is a one-variable rational function field over the
base field.

The proof is the final assembly of the positive-characteristic argument in
Borel, *Linear Algebraic Groups*, Theorem 10.9 and the algebraic sketch after
Corollary 11.6.  The primitive coordinate first gives a finite embedding
`k(t) -> Frac(A)`.  Inside the fraction field, its separable closure is rational:
the finite translation kernel is a `p`-group, and normal index-`p`
Artin--Schreier layers successively replace the primitive parameter until the
kernel is trivial.  The remaining extension from that separable core to the
full fraction field is finite and purely inseparable.  A sufficiently high
Frobenius power embeds it back into the rational separable core, and Luroth's
theorem supplies a generator which Frobenius injectivity pulls back to the full
field.

Normality is used by the finite primitive-map and translation-kernel results;
finite type and transcendence degree one make the primitive fraction map
finite.  The proof does not use an affine-line classification, a primitive
generator theorem, or the parent function-field rationality theorem.
-/

namespace Theory.AlgebraicGroup

universe u v

set_option linter.style.haveILetI false

variable {k : Type u} {A : Type v}
variable [Field k] [IsAlgClosed k] [CommRing A] [HopfAlgebra k A]
variable [IsDomain A] [Algebra.FiniteType k A] [IsIntegrallyClosed A]

/-- The fraction field of a normal transcendence-degree-one Hopf algebra with
a transcendental primitive element is rational in positive characteristic. -/
public theorem primitive_hopf_curve_fraction_field_is_rational_of_charP
    {p : Nat} [CharP k p] [Fact p.Prime]
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) :
    exists z : FractionRing A, Transcendental k z ∧
      IntermediateField.adjoin k ({z} : Set (FractionRing A)) = ⊤ := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have hfinite : Module.Finite (RatFunc k) (FractionRing A) := by
    simpa [AlgHom.Finite, RingHom.Finite] using
      primitive_hopf_curve_fraction_map_finite htrdeg t ht hprimitive
  letI : Module.Finite (RatFunc k) (FractionRing A) := hfinite
  let F := separableClosure (RatFunc k) (FractionRing A)
  haveI : Module.Finite F (FractionRing A) :=
    Module.Finite.of_restrictScalars_finite
      (RatFunc k) F (FractionRing A)
  haveI : IsPurelyInseparable F (FractionRing A) := by
    infer_instance
  haveI : IsScalarTower k F (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply Theory.IsRationalFunctionField.of_finite_purelyInseparable
    k F (FractionRing A) p
  exact primitive_hopf_curve_separable_core_is_rational_of_charP
    htrdeg t ht hprimitive

end Theory.AlgebraicGroup
