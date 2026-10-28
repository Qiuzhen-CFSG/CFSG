module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.PrimitiveCurveFinite

/-!
# The fraction-field map of a primitive Hopf curve

This module passes the finite polynomial map associated to a transcendental
primitive element to fraction fields.  Evaluation at `t` followed by the
canonical map into `FractionRing A` is injective, so the universal property of
`RatFunc k` gives a canonical embedding into `FractionRing A`.  Finiteness of
the polynomial evaluation map localizes to this embedding; the only comparison
needed is the standard equivalence between `RatFunc k` and the fraction ring of
`Polynomial k`.  An application lemma records the image of a polynomial
fraction without exposing the implementation of the canonical embedding.

This is the function-field form of the finite-isogeny step in Borel's algebraic
sketch following Corollary 11.6, used for GLS3 Proposition 1.3.5(c).  The input
that the primitive polynomial map is finite is supplied by
`primitive_hopf_curve_aeval_finite`.  No affine-line parameter, primitive
generator classification, or one-parameter subgroup classification is used.
-/

namespace Theory.AlgebraicGroup

universe u v

set_option linter.style.haveILetI false

variable {k : Type u} {A : Type v}

section FractionMap

variable [Field k] [CommRing A] [Algebra k A]

/-- Evaluation at `t`, followed by the canonical inclusion of `A` into its
fraction ring. -/
public noncomputable def primitivePolynomialMap (t : A) :
    Polynomial k →ₐ[k] FractionRing A :=
  (IsScalarTower.toAlgHom k A (FractionRing A)).comp (Polynomial.aeval t)

/-- The polynomial-to-fraction map induced by a transcendental element is
injective. -/
public theorem primitivePolynomialMap_injective (t : A)
    (ht : Transcendental k t) :
    Function.Injective (primitivePolynomialMap (k := k) t) :=
  (IsFractionRing.injective A (FractionRing A)).comp
    (transcendental_iff_injective.mp ht)

variable [IsDomain A]

/-- The canonical map from rational functions to the fraction ring induced by
a transcendental element. -/
public noncomputable def primitiveFractionMap (t : A)
    (ht : Transcendental k t) : RatFunc k →ₐ[k] FractionRing A :=
  RatFunc.liftAlgHom (primitivePolynomialMap (k := k) t)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (primitivePolynomialMap_injective (k := k) t ht))

/-- The primitive fraction map evaluates a polynomial numerator and
denominator in `A` and then includes them in its fraction ring. -/
public theorem primitiveFractionMap_apply_div (t : A)
    (ht : Transcendental k t) (p q : Polynomial k) :
    primitiveFractionMap t ht
        (algebraMap (Polynomial k) (RatFunc k) p /
          algebraMap (Polynomial k) (RatFunc k) q) =
      algebraMap A (FractionRing A) (Polynomial.aeval t p) /
        algebraMap A (FractionRing A) (Polynomial.aeval t q) := by
  unfold primitiveFractionMap
  rw [RatFunc.liftAlgHom_apply_div]
  rfl

/-- The canonical rational-function map induced by a transcendental element is
injective. -/
public theorem primitiveFractionMap_injective (t : A)
    (ht : Transcendental k t) :
    Function.Injective (primitiveFractionMap t ht) := by
  unfold primitiveFractionMap
  exact RatFunc.liftAlgHom_injective _
    (primitivePolynomialMap_injective (k := k) t ht)

/-- Finiteness of polynomial evaluation passes to the induced map on fraction
fields. -/
public theorem primitiveFractionMap_finite
    (t : A) (ht : Transcendental k t)
    (hfinite : (Polynomial.aeval t : Polynomial k →ₐ[k] A).Finite) :
    (primitiveFractionMap t ht).Finite := by
  letI : Algebra (RatFunc k) (FractionRing A) :=
    (primitiveFractionMap t ht).toRingHom.toAlgebra
  change Module.Finite (RatFunc k) (FractionRing A)
  letI : Algebra (Polynomial k) A := (Polynomial.aeval t).toRingHom.toAlgebra
  letI : IsScalarTower (Polynomial k) A (FractionRing A) :=
    OreLocalization.instIsScalarTower
  haveI : Module.IsTorsionFree (Polynomial k) A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (transcendental_iff_injective.mp ht)
  haveI : Module.Finite (Polynomial k) A := by
    simpa [AlgHom.Finite, RingHom.Finite] using hfinite
  haveI : FaithfulSMul (Polynomial k) (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      ((IsFractionRing.injective A (FractionRing A)).comp
        (transcendental_iff_injective.mp ht))
  letI : Algebra (FractionRing (Polynomial k)) (FractionRing A) :=
    FractionRing.liftAlgebra (Polynomial k) (FractionRing A)
  haveI : Module.Finite (FractionRing (Polynomial k)) (FractionRing A) := inferInstance
  apply Module.Finite.of_equiv_equiv
      (RatFunc.toFractionRingAlgEquiv k k).symm.toRingEquiv
      (RingEquiv.refl (FractionRing A))
  apply IsFractionRing.ringHom_ext (A := Polynomial k)
  intro p
  have hinv :
      (RatFunc.toFractionRingAlgEquiv k k).symm
          (algebraMap (Polynomial k) (FractionRing (Polynomial k)) p) =
        algebraMap (Polynomial k) (RatFunc k) p := by
    apply (RatFunc.toFractionRingAlgEquiv k k).injective
    simpa using congrArg RatFunc.toFractionRing
      (RatFunc.ofFractionRing_algebraMap p)
  have hinv' :
      (RatFunc.toFractionRingAlgEquiv k k).symm.toRingEquiv
          (algebraMap (Polynomial k) (FractionRing (Polynomial k)) p) =
        algebraMap (Polynomial k) (RatFunc k) p := hinv
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
    RingEquiv.refl_apply]
  rw [hinv', RingHom.algebraMap_toAlgebra]
  rw [show algebraMap (Polynomial k) (RatFunc k) p =
      algebraMap (Polynomial k) (RatFunc k) p /
        algebraMap (Polynomial k) (RatFunc k) 1 by simp]
  change primitiveFractionMap t ht
      (algebraMap (Polynomial k) (RatFunc k) p /
        algebraMap (Polynomial k) (RatFunc k) 1) = _
  unfold primitiveFractionMap
  rw [RatFunc.liftAlgHom_apply_div]
  simp [primitivePolynomialMap, FractionRing.algebraMap_liftAlgebra,
    IsFractionRing.lift_algebraMap]
  exact (IsScalarTower.algebraMap_apply (Polynomial k) A (FractionRing A) p).symm

end FractionMap

section Hopf

variable [Field k] [IsAlgClosed k] [CommRing A] [HopfAlgebra k A]
variable [IsDomain A] [Algebra.FiniteType k A]

/-- A transcendental primitive coordinate on a finite-type Hopf curve induces a
finite embedding of rational function fields. -/
public theorem primitive_hopf_curve_fraction_map_finite
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) :
    (primitiveFractionMap t ht).Finite :=
  primitiveFractionMap_finite t ht
    (primitive_hopf_curve_aeval_finite htrdeg t ht hprimitive)

end Hopf

end Theory.AlgebraicGroup
