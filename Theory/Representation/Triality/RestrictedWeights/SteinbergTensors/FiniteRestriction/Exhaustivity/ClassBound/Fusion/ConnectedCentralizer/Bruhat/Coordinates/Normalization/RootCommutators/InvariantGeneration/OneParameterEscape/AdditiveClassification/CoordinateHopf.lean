module

public import Theory.AlgebraicGroup.Unipotent.OneParameterCore
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Bialgebra
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.ConilpotentCurve
public import Theory.AlgebraicGroup.Bor1.CoordinateRingSmooth
public import Theory.AlgebraicGroup.Dimension.AffineCurveNormalization

/-!
# Coordinate Hopf algebra of a connected unipotent curve

These lemmas supply the actual coordinate-ring inputs to the algebraic proof of
Borel's Theorem 10.9, sketched after Corollary 11.6. Connectedness supplies a
domain of transcendence degree one. Smoothness of affine algebraic groups and
the regularity of smooth curves supply integral closedness. The surjective
additive character gives a transcendental primitive coordinate, with its
coproduct proved from the actual group multiplication.

No assertion that this primitive coordinate generates the coordinate ring is
made here: positive-characteristic finite kernels prevent that shortcut.
-/

open scoped TensorProduct

namespace Theory.AlgebraicGroup.AdditiveClassification

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (Y : Variety k) [AlgebraicGroup Y]

omit [IsAlgClosed k] in
/-- Connectedness identifies geometric dimension with the transcendence degree
of the actual polynomial-function algebra. -/
public theorem coordinate_trdeg_of_connected_curve
    (hc : Variety.IsConnected Y) (hd : Variety.dimension Y = 1) :
    Algebra.trdeg k (Variety.PolynomialFunction Y) = 1 := by
  have hirr := connectedAlgebraicGroup_irreducible Y hc
  let : IsDomain (coordinateRing Y) :=
    isDomain_coordinateRing_of_isIrreducible Y hirr
  rw [dimension_eq_fractionRing_of_isIrreducible Y hirr,
    trdeg_fractionRing_eq] at hd
  rw [← (coordinateRingAlgEquivPolynomialFunction Y).trdeg_eq]
  exact hd

/-- Smoothness of the actual connected algebraic curve gives integral
closedness of its polynomial-function algebra. -/
public theorem coordinate_normal_of_connected_curve
    (hc : Variety.IsConnected Y) (hd : Variety.dimension Y = 1) :
    IsIntegrallyClosed (Variety.PolynomialFunction Y) := by
  let : IsDomain (coordinateRing Y) :=
    isDomain_coordinateRing_of_isIrreducible Y
      (connectedAlgebraicGroup_irreducible Y hc)
  let : IsDomain (Variety.PolynomialFunction Y) :=
    (coordinateRingAlgEquivPolynomialFunction Y).toRingEquiv.isDomain_iff.mp
      inferInstance
  let : Algebra.Smooth k (Variety.PolynomialFunction Y) :=
    Bor1.polynomialFunction_smooth_of_algebraicGroup Y
  exact isIntegrallyClosed_of_smooth_trdeg_eq_one k _
    (coordinate_trdeg_of_connected_curve Y hc hd)

/-- The surjective additive character provides a transcendental primitive
element of the actual coordinate Hopf algebra. -/
public theorem exists_transcendental_primitive_coordinate
    (hc : Variety.IsConnected Y) (hd : Variety.dimension Y = 1)
    (hu : IsUnipotentAlgebraicGroup Y) :
    let : HopfAlgebra k (Variety.PolynomialFunction Y) := coordinateHopfAlgebra Y
    ∃ t : Variety.PolynomialFunction Y,
      Transcendental k t ∧ reducedComultiplication (k := k) t = 0 := by
  let : HopfAlgebra k (Variety.PolynomialFunction Y) := coordinateHopfAlgebra Y
  obtain ⟨f, hf, -⟩ := exists_surjective_morphism_toKPlus_finiteKernel hc hd hu
  let t := f.toVariety.pullbackAlgHom
    (Variety.PolynomialFunction.ofPolynomial (KPlus k) (MvPolynomial.X PUnit.unit))
  have htval (y : Variety.Point Y) : t y = (f.onPoints y).val PUnit.unit := by
    change evalPolynomial (f.onPoints y).val (MvPolynomial.X PUnit.unit) = _
    rw [evalPolynomial_X]
  have hsurj : Function.Surjective t := by
    intro a
    obtain ⟨y, hy⟩ := hf (kPlusPoint a)
    refine ⟨y, ?_⟩
    rw [htval, hy]
    rfl
  refine ⟨t, ?_, ?_⟩
  · rw [transcendental_iff_injective]
    intro P Q hpq
    apply Polynomial.funext
    intro a
    obtain ⟨y, rfl⟩ := hsurj a
    have h := congrArg (polynomialFunctionPointAlgHom Y y) hpq
    simpa only [← Polynomial.aeval_algHom_apply, polynomialFunctionPointAlgHom_apply,
      Polynomial.coe_aeval_eq_eval] using h
  · rw [reducedComultiplication_eq_zero_iff]
    change coordinateComultiplication Y t = t ⊗ₜ[k] 1 + 1 ⊗ₜ[k] t
    apply polynomialFunctionTensor_injective Y Y
    apply Variety.PolynomialFunction.ext
    intro z
    obtain ⟨x, y, rfl⟩ : ∃ x y, z = (Variety.prodPointEquiv Y Y).symm (x,y) :=
      ⟨_, _, (Variety.prodPointEquiv Y Y).symm_apply_apply z |>.symm⟩
    rw [coordinateComultiplication_apply, map_add, polynomialFunctionTensor_tmul,
      polynomialFunctionTensor_tmul]
    change t (x * y) = t x * 1 + 1 * t y
    rw [mul_one, one_mul]
    rw [htval, htval, htval, map_mul, kPlusPoint_coordinate_mul]

end Theory.AlgebraicGroup.AdditiveClassification
