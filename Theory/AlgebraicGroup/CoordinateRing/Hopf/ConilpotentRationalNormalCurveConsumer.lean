module

public import Theory.AlgebraicGroup.CoordinateRing.Hopf.ConilpotentRationalNormalCurve

/-!
# Cross-universe consumer for rational normal Hopf-curve recovery

This module checks the public affine-parameter theorem with the ground field
and coordinate ring in independent universes.  It is deliberately a thin
consumer of the lower owner module.
-/

universe u v

namespace Theory.AlgebraicGroup

public theorem normal_rational_conilpotent_hopf_curve_cross_universe_consumer
    {k : Type u} {A : Type v}
    [Field k] [IsAlgClosed k] [CommRing A] [HopfAlgebra k A]
    [IsDomain A] [Algebra.FiniteType k A] [IsIntegrallyClosed A]
    [HasOrderedConilpotentGenerators (k := k) (A := A)]
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (hrat : ∃ z : FractionRing A, Transcendental k z ∧
      IntermediateField.adjoin k ({z} : Set (FractionRing A)) = ⊤) :
    ∃ s : A, Transcendental k s ∧ Algebra.adjoin k ({s} : Set A) = ⊤ :=
  normal_rational_conilpotent_hopf_curve_exists_affine_parameter
    htrdeg t ht hprimitive hrat

end Theory.AlgebraicGroup
