module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.PositivePrimitivesLeft.Pairing

/-!
# Rational duality and opposition for the primitive-line argument

The contragredient action is taken on the actual linear dual, with its proved
rationality and irreducibility. An equivalence with this dual supplies an
invariant bilinear form. Twisting the second argument by a group element
which interchanges opposite root groups gives root adjointness. Polynomial
uniqueness then gives adjointness of the actual first coefficients.

`Opposition` records the geometric identities needed of that group element.
This module proves the conditional construction, not existence of opposition
or the dual's highest weight. Those are separate inputs to final assembly.

Source: rational contravariant duality supporting Steinberg, *Representations
of Algebraic Groups* (1963), §§2, 4 and 11.1. The coefficient argument follows
the checked F4 `PositivePrimitives/ContravariantForm.lean` pattern.
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity
@[expose] public noncomputable section
universe u v w
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
namespace PositivePrimitivesLeft

/-- A genuine root-negating representative in the given algebraic group.
Both fields are equations of its actual point action. -/
structure Opposition (S : D4Geometry K) where
  point : Variety.Point K
  root_commute : ∀ α t, S.chevalley.x α t * point =
    point * S.chevalley.x (S.roots.neg α) t
  torus_commute : ∀ t : Variety.Point S.torus.carrierVariety,
    S.torus.includePoint t * point = point * S.torus.includePoint t⁻¹

/-- The rational contragredient on the actual dual carrier. -/
def dualRepresentation (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ) :
    RationalRepresentation K (Module.Dual k V) :=
  (rationalRepresentation_dual_exists ρ hρ).choose

/-- Its action evaluates a covector on the inverse original action. -/
theorem dualRepresentation_spec (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ) :
    IsDualRepresentation ρ (dualRepresentation ρ hρ) :=
  (rationalRepresentation_dual_exists ρ hρ).choose_spec.1

/-- The actual contragredient is rational. -/
theorem dualRepresentation_rational (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ) :
    IsRationalRepresentation (dualRepresentation ρ hρ) :=
  (rationalRepresentation_dual_exists ρ hρ).choose_spec.2

/-- Rational duality preserves irreducibility on arbitrary carrier universes. -/
theorem dualRepresentation_irreducible (ρ : RationalRepresentation K V)
    (hρ : IsIrreducibleRepresentation ρ) :
    IsIrreducibleRepresentation (dualRepresentation ρ hρ.1) :=
  dualRepresentation_isIrreducible ρ _ (dualRepresentation_spec ρ hρ.1) hρ
    (dualRepresentation_rational ρ hρ.1)

/-- Adjointness of root groups implies adjointness of the first coefficients. -/
theorem rootOperator_adjoint_of_root_adjoint (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (e : V →ₗ[k] Module.Dual k V) (r s : S.roots.Root)
    (h : ∀ (t : k) (x y : V),
      e ((ρ.action (S.chevalley.x r t)).val x) y =
        e x ((ρ.action (S.chevalley.x s t)).val y)) (x y : V) :
    e (rootOperator S ρ hρ r x) y = e x (rootOperator S ρ hρ s y) := by
  have hp : curvePolynomial ρ hρ (rootMorphism S r) (e.flip y) x =
      curvePolynomial ρ hρ (rootMorphism S s) (e x) y := by
    apply Polynomial.funext
    intro t
    simpa only [curvePolynomial_eval, rootMorphism_apply, LinearMap.flip_apply] using h t x y
  change (e.flip y) (curveOperator ρ hρ (rootMorphism S r) x) =
    (e x) (curveOperator ρ hρ (rootMorphism S s) y)
  rw [dual_curveOperator, dual_curveOperator, hp]

omit [IsAlgClosed k] in
/-- The given pinned additive root groups consist of involutions in characteristic two. -/
theorem rootElement_inv [CharP k 2] (S : D4Geometry K) (r : S.roots.Root) (t : k) :
    (S.chevalley.x r t)⁻¹ = S.chevalley.x r t := by
  have ht : (kPlusPoint t)⁻¹ = kPlusPoint (-t) := by
    apply (additiveGroupPointEquiv k).injective
    rfl
  rw [← rootMorphism_apply, ← map_inv, ht, CharTwo.neg_eq]

/-- Rational self-duality, twisted by actual opposition, supplies the required form. -/
theorem pairing_of_equivalent_dual [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (O : Opposition S)
    (τ : RationalRepresentation K (Module.Dual k V)) (hτ : IsDualRepresentation ρ τ)
    (hself : AreEquivalentRepresentations ρ τ) : HasContravariantPairing S ρ hρ := by
  obtain ⟨e, he⟩ := hself
  let N := LinearMap.GeneralLinearGroup.generalLinearEquiv k V (ρ.action O.point)
  let E : V ≃ₗ[k] Module.Dual k V := e.trans N.dualMap
  refine ⟨E.toLinearMap, E.injective, ?_⟩
  intro r x y
  apply rootOperator_adjoint_of_root_adjoint S ρ hρ E.toLinearMap r.val
    (S.roots.neg r.val) _ x y
  intro t a b
  change e ((ρ.action (S.chevalley.x r.val t)).val a) (N b) =
    e a (N ((ρ.action (S.chevalley.x (S.roots.neg r.val) t)).val b))
  have he' : e ((ρ.action (S.chevalley.x r.val t)).val a) =
      (τ.action (S.chevalley.x r.val t)).val (e a) := he _ a
  rw [he', hτ, rootElement_inv]
  congr 1
  change (ρ.action (S.chevalley.x r.val t)).val ((ρ.action O.point).val b) =
    (ρ.action O.point).val ((ρ.action (S.chevalley.x (S.roots.neg r.val) t)).val b)
  have hh := congrArg (fun g => (ρ.action g).val b) (O.root_commute r.val t)
  simpa only [map_mul, Units.val_mul, Module.End.mul_apply] using hh

section Transport
variable {W : Type w} [AddCommGroup W] [Module k W] [FiniteDimensional k W]

private def transportedAction (ρ : RationalRepresentation K V) (e : V ≃ₗ[k] W) :
    RationalRepresentation K W :=
  ⟨(LinearMap.GeneralLinearGroup.congrLinearEquiv e).toMonoidHom.comp ρ.action⟩

private theorem transportedAction_rational (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) (e : V ≃ₗ[k] W) :
    IsRationalRepresentation (transportedAction ρ e) := by
  obtain ⟨b₀, f₀, hf₀⟩ := hρ
  let b := Module.finBasis k W
  let c := fun i j => rationalRepresentationLinearMatrixCoefficient ρ b₀ f₀
    ((b.coord i).comp e.toLinearMap) (e.symm (b j))
  have hc : ∀ i j g, c i j g = b.repr (((transportedAction ρ e).action g).val (b j)) i := by
    intro i j g
    rw [show c i j = rationalRepresentationLinearMatrixCoefficient ρ b₀ f₀
      ((b.coord i).comp e.toLinearMap) (e.symm (b j)) from rfl,
      rationalRepresentationLinearMatrixCoefficient_apply ρ b₀ f₀ hf₀]
    rfl
  let ci := fun i j => Variety.PolynomialFunction.pullback
    (Theory.AlgebraicGroup.invMorphism K) (c i j)
  have hci : ∀ i j g, ci i j g =
      b.repr ((((transportedAction ρ e).action g)⁻¹).val (b j)) i := by
    intro i j g
    change c i j g⁻¹ = _
    rw [hc, map_inv]
  let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient b
    (transportedAction ρ e).action c ci hc hci
  refine ⟨b, f, ?_⟩
  intro g
  exact glPointEquivOf_generalLinearRepresentationPoint b ((transportedAction ρ e).action g)

private theorem transportedAction_irreducible (ρ : RationalRepresentation K V)
    (hρ : IsIrreducibleRepresentation ρ) (e : V ≃ₗ[k] W) :
    IsIrreducibleRepresentation (transportedAction ρ e) := by
  refine ⟨transportedAction_rational ρ hρ.1 e, ?_⟩
  apply algebraicallyIrreducible_of_equiv _ ρ e.symm _ hρ.2
  intro g w
  exact e.symm_apply_apply _

omit [IsAlgClosed k] [FiniteDimensional k V] [FiniteDimensional k W] in
private theorem transportedAction_highWeight (ρ : RationalRepresentation K V)
    (e : V ≃ₗ[k] W) (B T : ClosedSubgroup K) {v : V} {χ : TorusWeight T}
    (hv : HasHighWeight ρ B T v χ) :
    HasHighWeight (transportedAction ρ e) B T (e v) χ := by
  have he0 : e v ≠ 0 := fun h => hv.1.1 (e.injective (h.trans e.map_zero.symm))
  refine ⟨⟨he0, ?_⟩, he0, ?_⟩
  · intro g hg
    obtain ⟨c, hc⟩ := hv.1.2 g hg
    refine ⟨c, ?_⟩
    change e ((ρ.action g).val (e.symm (e v))) = _
    rw [e.symm_apply_apply, hc, map_smul]
  · intro t
    change e ((ρ.action (T.includePoint t)).val (e.symm (e v))) = _
    rw [e.symm_apply_apply, hv.2.2, map_smul]
end Transport

/-- Highest-weight uniqueness constructs the form once opposition and the
dual's genuine highest weight have been supplied. -/
theorem pairing_of_dual_highWeight [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsIrreducibleRepresentation ρ)
    (O : Opposition S) {χ : TorusWeight S.torus} {v : V}
    (hv : HasHighWeight ρ S.borel S.torus v χ)
    (hdual : ∃ f, HasHighWeight (dualRepresentation ρ hρ.1) S.borel S.torus f χ) :
    HasContravariantPairing S ρ hρ.1 := by
  obtain ⟨f, hf⟩ := hdual
  apply pairing_of_equivalent_dual S ρ hρ.1 O _ (dualRepresentation_spec ρ hρ.1)
  -- The checked uniqueness API has both carriers in the same universe.
  -- Transport the dual to V through a basis equivalence before applying it.
  let d : Module.Dual k V ≃ₗ[k] V := (Module.finBasis k V).toDualEquiv.symm
  let τ := dualRepresentation ρ hρ.1
  obtain ⟨e, he⟩ := irreducible_highWeight_equivalent_of_oppositeBorelBigCell
    S.bigCell S.maximalTorus ρ (transportedAction τ d) hρ
    (transportedAction_irreducible τ (dualRepresentation_irreducible ρ hρ) d)
    v (d f) χ hv (transportedAction_highWeight τ d S.borel S.torus hf)
  refine ⟨e.trans d.symm, ?_⟩
  intro g x
  change d.symm (e ((ρ.action g).val x)) = (τ.action g).val (d.symm (e x))
  exact (congrArg d.symm (he g x)).trans (d.symm_apply_apply _)

end PositivePrimitivesLeft
end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity
