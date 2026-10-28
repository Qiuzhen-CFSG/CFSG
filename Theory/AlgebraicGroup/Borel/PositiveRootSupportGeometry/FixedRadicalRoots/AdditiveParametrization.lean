module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.InvariantGeneration.OneParameterEscape.AdditiveClassification.CoordinateHopf
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.InvariantGeneration.OneParameterEscape.AdditiveClassification.PolynomialCoordinate
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.InvariantGeneration.OneParameterEscape.AdditiveClassification.NormalRecovery
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.PrimitiveCurveZeroFibreSeparableDegree
public import Theory.AlgebraicGroup.Jordan.FiniteOrder
public import Theory.AlgebraicGroup.Jordan.Intersection

/-!
# Additive parametrizations of connected unipotent curves

A connected one-dimensional unipotent algebraic group over an algebraically
closed field is isomorphic to the additive group, in arbitrary characteristic.
This supplies the additive parametrizations of rank-one centralizer radicals
used in Borel 13.14, before the comparison of their full torus characters.

In prime characteristic, the normal primitive Hopf-curve theorem proves that
the actual coordinate algebra has a polynomial generator. In characteristic
zero, a surjective additive character has trivial finite kernel: each kernel
point is both semisimple and unipotent. Its coordinate is therefore bijective.
The zero-fibre/separable-degree theorem and characteristic-zero separability
make the function-field extension degree one. Normal recovery then supplies a
polynomial coordinate in the actual affine algebra. In both cases, normalizing
that coordinate at the identity gives the additive law and a regular inverse.

Sources: GLS3, Definition 1.3.4 and Proposition 1.3.5(c)
(`refs/KGroup/GLS3/Chapter1.tex`); Borel, Theorem 10.9 and the algebraic sketch
following Corollary 11.6 (`refs/KGroup/Bor1/Chapter3.tex`, `Chapter4.tex`).
The characteristic-zero argument uses separability only after deriving it from
the field characteristic. The prime-characteristic argument retains finite
kernels and inseparability throughout the checked normal-recovery route.
-/

open scoped TensorProduct

namespace Theory.AlgebraicGroup
universe u v

private theorem injective_of_finiteKernel_of_unipotent_charZero
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {Y Z : Variety k} [AlgebraicGroup Y] [AlgebraicGroup Z]
    (f : Morphism Y Z) [Finite f.kernel]
    (hu : IsUnipotentAlgebraicGroup Y) : Function.Injective f.onPoints := by
  apply (MonoidHom.ker_eq_bot_iff f.onPoints).mp
  apply bot_unique
  intro y hy
  change y = 1
  let x : f.kernel := ⟨y, hy⟩
  have hn : 0 < orderOf x := orderOf_pos x
  have hpow : y ^ orderOf x = 1 := congrArg Subtype.val (pow_orderOf_eq_one x)
  apply semisimple_unipotent_eq_one y _ (hu y)
  apply finiteOrder_coprimeChar_implies_semisimple y (orderOf x) hn _ hpow
  rw [ringChar.eq_zero, zero_dvd_iff]
  exact Nat.ne_of_gt hn

private theorem exists_bijective_primitive_coordinate
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Variety k} [AlgebraicGroup Y]
    (f : Morphism Y (KPlus k)) (hf : Function.Bijective f.onPoints) :
    let : HopfAlgebra k (Variety.PolynomialFunction Y) := coordinateHopfAlgebra Y
    ∃ t : Variety.PolynomialFunction Y, Function.Bijective t ∧
      Transcendental k t ∧ reducedComultiplication (k := k) t = 0 := by
  let : HopfAlgebra k (Variety.PolynomialFunction Y) := coordinateHopfAlgebra Y
  let t := f.toVariety.pullbackAlgHom
    (Variety.PolynomialFunction.ofPolynomial (KPlus k) (MvPolynomial.X PUnit.unit))
  have htval (y : Variety.Point Y) : t y = (f.onPoints y).val PUnit.unit := by
    change evalPolynomial (f.onPoints y).val (MvPolynomial.X PUnit.unit) = _
    rw [evalPolynomial_X]
  have hsurj : Function.Surjective t := by
    intro a
    obtain ⟨y, hy⟩ := hf.2 (kPlusPoint a)
    exact ⟨y, by rw [htval, hy]; rfl⟩
  refine ⟨t, ⟨?_, hsurj⟩, ?_, ?_⟩
  · intro x y hxy
    apply hf.1
    apply Variety.Point.ext
    funext i
    exact (htval x).symm.trans (hxy.trans (htval y))
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
    rw [mul_one, one_mul, htval, htval, htval, map_mul, kPlusPoint_coordinate_mul]

private theorem zero_fibre_card_one_of_bijective_coordinate
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Variety k} (t : Variety.PolynomialFunction Y)
    (hb : Function.Bijective t) :
    Nat.card {q : Variety.PolynomialFunction Y →ₐ[k] k // q t = 0} = 1 := by
  obtain ⟨z, hz⟩ := hb.2 0
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨polynomialFunctionPointAlgHom Y z, hz⟩, ?_⟩
  intro q
  apply Subtype.ext
  obtain ⟨x, hx, -⟩ := polynomialFunctionPointAlgHom_existsUnique Y q.val
  have hx0 : t x = 0 := by
    change polynomialFunctionPointAlgHom Y x t = 0
    rw [hx]
    exact q.property
  have hxz : x = z := hb.1 (hx0.trans hz.symm)
  rw [← hx, hxz]

private theorem fraction_rational_of_zero_fibre_card_one
    {k : Type u} {A : Type v}
    [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [HopfAlgebra k A]
    [IsDomain A] [Algebra.FiniteType k A] [IsIntegrallyClosed A]
    (htrdeg : Algebra.trdeg k A = 1) (t : A) (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (hzero : Nat.card {q : A →ₐ[k] k // q t = 0} = 1) :
    ∃ z : FractionRing A, Transcendental k z ∧
      IntermediateField.adjoin k ({z} : Set (FractionRing A)) = ⊤ := by
  let f := primitiveFractionMap (k := k) t ht
  let : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  let : IsScalarTower k (RatFunc k) (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let : Module.Finite (RatFunc k) (FractionRing A) := by
    simpa [AlgHom.Finite, RingHom.Finite] using
      primitive_hopf_curve_fraction_map_finite htrdeg t ht hprimitive
  have hdegree := primitive_hopf_curve_zero_fibre_card_eq_separable_finrank
    htrdeg t ht hprimitive
  change Nat.card {q : A →ₐ[k] k // q t = 0} =
    Module.finrank (RatFunc k) (separableClosure (RatFunc k) (FractionRing A)) at hdegree
  rw [hzero, (separableClosure.eq_top_iff (RatFunc k) (FractionRing A)).mpr
    (inferInstance : Algebra.IsSeparable (RatFunc k) (FractionRing A)),
    IntermediateField.finrank_top'] at hdegree
  have hsurj : Function.Surjective f :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdegree.symm).2
  refine ⟨f RatFunc.X, ?_, ?_⟩
  · exact fun h => RatFunc.transcendental_X
      ((isAlgebraic_algHom_iff f f.injective).mp h)
  · rw [← Set.image_singleton, ← IntermediateField.adjoin_map, RatFunc.adjoin_X]
    apply top_unique
    intro z _
    obtain ⟨x, rfl⟩ := hsurj z
    exact ⟨x, IntermediateField.mem_top, rfl⟩

/-- A connected unipotent curve in characteristic zero admits an additive
parametrization with regular inverse. -/
public theorem connectedUnipotentCurve_isOneParameter_charZero
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Variety k} [AlgebraicGroup Y]
    (hc : Variety.IsConnected Y) (hd : Variety.dimension Y = 1)
    (hu : IsUnipotentAlgebraicGroup Y) : IsOneParameterGroup Y := by
  obtain ⟨f, hsurj, hfinite⟩ := exists_surjective_morphism_toKPlus_finiteKernel hc hd hu
  let : Finite f.kernel := hfinite
  have hinj := injective_of_finiteKernel_of_unipotent_charZero f hu
  let : HopfAlgebra k (Variety.PolynomialFunction Y) := coordinateHopfAlgebra Y
  let : IsDomain (coordinateRing Y) :=
    isDomain_coordinateRing_of_isIrreducible Y
      (connectedAlgebraicGroup_irreducible Y hc)
  let : IsDomain (Variety.PolynomialFunction Y) :=
    (coordinateRingAlgEquivPolynomialFunction Y).toRingEquiv.isDomain_iff.mp
      inferInstance
  let : Algebra.FiniteType k (Variety.PolynomialFunction Y) :=
    polynomialFunction_finiteType Y
  let : IsIntegrallyClosed (Variety.PolynomialFunction Y) :=
    AdditiveClassification.coordinate_normal_of_connected_curve Y hc hd
  have htrdeg := AdditiveClassification.coordinate_trdeg_of_connected_curve Y hc hd
  obtain ⟨t, hb, ht, hprimitive⟩ := exists_bijective_primitive_coordinate f ⟨hinj, hsurj⟩
  have hrat := fraction_rational_of_zero_fibre_card_one htrdeg t ht hprimitive
    (zero_fibre_card_one_of_bijective_coordinate t hb)
  obtain ⟨s, hs, hgen⟩ :=
    AdditiveClassification.normal_rational_hopf_curve_exists_affine_parameter
      htrdeg t ht hprimitive hrat
  exact AdditiveClassification.isOneParameter_of_polynomial_coordinate s hs hgen

/-- The converse direction of GLS3 Proposition 1.3.5(c), over every
algebraically closed field, with no characteristic or splitting premise. -/
public theorem connectedUnipotentCurve_isOneParameter
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Variety k} [AlgebraicGroup Y]
    (hc : Variety.IsConnected Y) (hd : Variety.dimension Y = 1)
    (hu : IsUnipotentAlgebraicGroup Y) : IsOneParameterGroup Y := by
  by_cases hchar : ringChar k = 0
  · let : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp hchar
    exact connectedUnipotentCurve_isOneParameter_charZero hc hd hu
  · let p := ringChar k
    let : CharP k p := ringChar.charP k
    let : Fact p.Prime :=
      ⟨(CharP.char_is_prime_or_zero k p).resolve_right hchar⟩
    let : HopfAlgebra k (Variety.PolynomialFunction Y) := coordinateHopfAlgebra Y
    let : IsDomain (coordinateRing Y) :=
      isDomain_coordinateRing_of_isIrreducible Y
        (connectedAlgebraicGroup_irreducible Y hc)
    let : IsDomain (Variety.PolynomialFunction Y) :=
      (coordinateRingAlgEquivPolynomialFunction Y).toRingEquiv.isDomain_iff.mp
        inferInstance
    let : Algebra.FiniteType k (Variety.PolynomialFunction Y) :=
      polynomialFunction_finiteType Y
    let : IsIntegrallyClosed (Variety.PolynomialFunction Y) :=
      AdditiveClassification.coordinate_normal_of_connected_curve Y hc hd
    have htrdeg := AdditiveClassification.coordinate_trdeg_of_connected_curve Y hc hd
    obtain ⟨t, ht, hprimitive⟩ :=
      AdditiveClassification.exists_transcendental_primitive_coordinate Y hc hd hu
    obtain ⟨s, hs, hgen⟩ :=
      AdditiveClassification.normal_primitive_hopf_curve_exists_affine_parameter_of_charP
        (p := p) htrdeg t ht hprimitive
    exact AdditiveClassification.isOneParameter_of_polynomial_coordinate s hs hgen

/-- An actual additive parametrization, including its regular inverse, of a
connected one-dimensional unipotent group. Applied to the intrinsic unipotent
radical in Borel 13.14, this is the source's isomorphism from the additive group. -/
public noncomputable def connectedUnipotentCurve_additiveParametrization
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Variety k} [AlgebraicGroup Y]
    (hc : Variety.IsConnected Y) (hd : Variety.dimension Y = 1)
    (hu : IsUnipotentAlgebraicGroup Y) : AlgebraicGroup.Iso (KPlus k) Y :=
  Classical.choice (connectedUnipotentCurve_isOneParameter hc hd hu)

end Theory.AlgebraicGroup
