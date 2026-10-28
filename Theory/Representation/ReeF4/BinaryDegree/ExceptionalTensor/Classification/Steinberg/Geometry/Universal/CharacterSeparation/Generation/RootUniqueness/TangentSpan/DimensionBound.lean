module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentLines
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.Parameters
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters
public import Theory.AlgebraicGroup.Bor1.TangentDimension
public import Theory.AlgebraicGroup.Dimension.Torus

/-!
# Geometric dimension bound for the literal F4 tangent space

The split torus has tangent dimension four, and the literal root index has 48
elements. The product of that torus with one affine coordinate per root is
irreducible of dimension 52. Any dominant morphism from this space to the
literal Chevalley carrier bounds its dimension by 52, by injectivity of
pullback on polynomial functions. Smoothness of algebraic groups then gives
the required bound on identity derivations.

In characteristic two, the concrete Bruhat cells supply the dominant
parametrization, discharging the geometric input. Thus the identity tangent
dimension is at most the split-torus tangent dimension plus the number of
literal roots. This holds over every algebraically closed field of
characteristic two; semisimplicity and maximality of the split torus are not
needed for this concrete bound. No differential spanning is inferred from
point generation.

Source: the concrete dimension argument for GLS3, Theorem 1.9.5(b) and
§§1.11–1.12, `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section

namespace Theory.AlgebraicGroup.F4Chevalley

open scoped Cardinal

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

noncomputable section

local instance : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
  (splitTorus (k := k)).carrierAlgebraicGroup

/-- The split torus of the literal carrier has geometric dimension four. -/
theorem concreteSplitTorus_dimension :
    Variety.dimension (splitTorus (k := k)).carrierVariety = 4 := by
  rw [← algebraicGroupIso_dimension_eq (splitTorusIso (k := k)),
    dVariety_dimension_eq]
  norm_num

/-- The canonical split-torus identity tangent has dimension four. -/
theorem concreteSplitTorus_tangent_finrank :
    Module.finrank k
      (IdentityPointDerivation (splitTorus (k := k)).carrierVariety) = 4 := by
  rw [Bor1.identityPointDerivation_finrank_eq_dimension, concreteSplitTorus_dimension,
    Cardinal.toNat_ofNat]

private lemma affineSpace_isIrreducible (σ : Type u) [Finite σ] :
    IsIrreducible (Set.univ : Set (Variety.Point (affineSpaceVariety k σ))) := by
  let : Nonempty (Variety.Point (affineSpaceVariety k σ)) :=
    ⟨affineSpacePoint (fun _ => 0)⟩
  apply isIrreducible_univ_of_prime_vanishingIdeal
  rw [affineSpaceVariety_vanishingIdeal_eq_bot]
  exact Ideal.isPrime_bot

private theorem affineSpace_dimension (σ : Type u) [Finite σ] :
    Variety.dimension (affineSpaceVariety k σ) = Cardinal.mk σ := by
  let : Nonempty (Variety.Point (affineSpaceVariety k σ)) :=
    ⟨affineSpacePoint (fun _ => 0)⟩
  let : IsDomain (coordinateRing (affineSpaceVariety k σ)) :=
    (Ideal.Quotient.isDomain_iff_prime
      (I := vanishingIdeal (Set.univ : Set
        (Variety.Point (affineSpaceVariety k σ))))).mpr (by
          rw [affineSpaceVariety_vanishingIdeal_eq_bot]
          exact Ideal.isPrime_bot)
  rw [dimension_eq_fractionRing_of_isIrreducible
    (affineSpaceVariety k σ) (affineSpace_isIrreducible σ), trdeg_fractionRing_eq]
  change Algebra.trdeg k (MvPolynomial σ k ⧸
    vanishingIdeal (Set.univ : Set
      (Variety.Point (affineSpaceVariety k σ)))) = Cardinal.mk σ
  rw [affineSpaceVariety_vanishingIdeal_eq_bot]
  calc
    Algebra.trdeg k (MvPolynomial σ k ⧸ (⊥ : Ideal (MvPolynomial σ k))) =
        Algebra.trdeg k (MvPolynomial σ k) :=
      (AlgEquiv.quotientBot k (MvPolynomial σ k)).trdeg_eq
    _ = Cardinal.mk σ := by
      simpa only [Cardinal.lift_id] using
        (MvPolynomial.trdeg_of_isDomain :
          Algebra.trdeg k (MvPolynomial σ k) = Cardinal.lift.{u} #σ)

/-- The parameter space is irreducible. -/
theorem concreteRootParameterSpace_isIrreducible :
    IsIrreducible
      (Set.univ : Set (Variety.Point (concreteRootParameterSpace (k := k)))) := by
  unfold concreteRootParameterSpace
  have ht := connectedAlgebraicGroup_irreducible
    (splitTorus (k := k)).carrierVariety
    (splitTorus_isSubtorus (k := k)).isConnected
  have ha := affineSpace_isIrreducible (k := k) (ULift.{u} Root)
  simpa [Variety.prodSet] using
    prodSet_irreducible_of_irreducible ht ha

/-- The actual torus and the 48 affine root coordinates give dimension 52. -/
theorem concreteRootParameterSpace_dimension :
    Variety.dimension (concreteRootParameterSpace (k := k)) = 52 := by
  let : Nonempty (Variety.Point (affineSpaceVariety k (ULift.{u} Root))) :=
    ⟨affineSpacePoint (fun _ => 0)⟩
  rw [concreteRootParameterSpace, dimension_product_additive,
    concreteSplitTorus_dimension, affineSpace_dimension, Cardinal.mk_fintype,
    Fintype.card_ulift, concreteRoot_card]
  norm_num

omit [IsAlgClosed k] in
private lemma dimension_eq_trdeg_polynomialFunction
    (V : Variety k) (hV : IsIrreducible (Set.univ : Set (Variety.Point V))) :
    Variety.dimension V = Algebra.trdeg k (Variety.PolynomialFunction V) := by
  let : IsDomain (coordinateRing V) :=
    isDomain_coordinateRing_of_isIrreducible V hV
  let : IsDomain (Variety.PolynomialFunction V) :=
    (coordinateRingAlgEquivPolynomialFunction V).toRingEquiv.isDomain_iff.mp
      inferInstance
  rw [dimension_eq_fractionRing_of_isIrreducible V hV, trdeg_fractionRing_eq]
  exact (coordinateRingAlgEquivPolynomialFunction V).trdeg_eq

omit [IsAlgClosed k] in
private lemma dimension_le_of_dense_morphism
    {U W : Variety k} (f : Variety.Morphism U W)
    (hU : IsIrreducible (Set.univ : Set (Variety.Point U)))
    (hW : IsIrreducible (Set.univ : Set (Variety.Point W)))
    (hf : Dense (Set.range f.toFun)) :
    Variety.dimension W ≤ Variety.dimension U := by
  rw [dimension_eq_trdeg_polynomialFunction W hW,
    dimension_eq_trdeg_polynomialFunction U hU]
  apply trdeg_le_of_injective f.pullbackAlgHom
  intro p q hpq
  rcases p.representedBy with ⟨pp, hpp⟩
  rcases q.representedBy with ⟨qq, hqq⟩
  let Z : Set (Variety.Point W) := {y | evalPolynomial y.val (pp - qq) = 0}
  have hZclosed : IsClosed Z := by
    rw [Variety.isClosed_iff_isZariskiClosed]
    refine ⟨{pp - qq}, ?_⟩
    ext y
    simp [Z]
  have hrange : Set.range f.toFun ⊆ Z := by
    rintro y ⟨x, rfl⟩
    have hxy := congrArg (fun r : Variety.PolynomialFunction U => r x) hpq
    change p (f.toFun x) = q (f.toFun x) at hxy
    have hxy' : evalPolynomial (f.toFun x).val pp =
        evalPolynomial (f.toFun x).val qq := by
      rw [← hpp, ← hqq]
      exact hxy
    simpa [Z, evalPolynomial] using sub_eq_zero.mpr hxy'
  apply Variety.PolynomialFunction.ext
  intro y
  rw [hpp y, hqq y]
  apply sub_eq_zero.mp
  have hyZ : y ∈ Z :=
    closure_minimal hrange hZclosed (hf.closure_eq ▸ Set.mem_univ y)
  simpa [Z, evalPolynomial] using hyZ

/-- Dominant root parameters bound the literal carrier's geometric dimension. -/
theorem concreteCarrier_dimension_le_of_dense_root_parameters
    (f : Variety.Morphism (concreteRootParameterSpace (k := k)) (Carrier (k := k)))
    (hf : Dense (Set.range f.toFun)) :
    Variety.dimension (Carrier (k := k)) ≤ 52 := by
  have hG := connectedAlgebraicGroup_irreducible (Carrier (k := k)) carrier_isConnected
  exact (dimension_le_of_dense_morphism f
    concreteRootParameterSpace_isIrreducible hG hf).trans_eq
      concreteRootParameterSpace_dimension

/-- A dominant parametrization supplies the geometric upper bound used by
the tangent-spanning assembly. Its existence remains a separate input. -/
theorem concreteIdentityTangent_finrank_le_of_dense_root_parameters
    (f : Variety.Morphism (concreteRootParameterSpace (k := k)) (Carrier (k := k)))
    (hf : Dense (Set.range f.toFun)) :
    Module.finrank k (IdentityPointDerivation (Carrier (k := k))) ≤
      Module.finrank k
        (IdentityPointDerivation (splitTorus (k := k)).carrierVariety) +
          Fintype.card Root := by
  rw [concreteSplitTorus_tangent_finrank, concreteRoot_card,
    Bor1.identityPointDerivation_finrank_eq_dimension]
  apply (Cardinal.toNat_le_iff_of_lt_aleph0 52
    (variety_dimension_lt_aleph0 (Carrier (k := k)))).2
  exact concreteCarrier_dimension_le_of_dense_root_parameters f hf

/-- The literal F4 identity tangent has dimension at most the split-torus
tangent dimension plus the number of roots. The concrete dominant
parametrization discharges the geometric premise in characteristic two.
In particular, this gives the bound over the algebraic closure of any finite
characteristic-two field required by the tangent-spanning assembly. -/
theorem concreteIdentityTangent_finrank_le_torus_add_card_root [CharP k 2] :
    Module.finrank k (IdentityPointDerivation (Carrier (k := k))) ≤
      Module.finrank k
        (IdentityPointDerivation (splitTorus (k := k)).carrierVariety) +
          Fintype.card Root := by
  obtain ⟨f, hf⟩ := exists_concrete_dense_root_parameters (k := k)
  exact concreteIdentityTangent_finrank_le_of_dense_root_parameters f hf

end
end Theory.AlgebraicGroup.F4Chevalley
