module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.Coordinates

/-!
# Recovering Spin coroot coordinates from a Clifford coefficient

The ordinary diagonal coordinates recover `t₀` and `t₁` regularly. A single
polynomial function with value `t₃` on the coroot product also recovers
`t₂ = d₃ t₃`; inversion supplies all four reciprocal coordinates. This constructs
the regular inverse to the point parametrization. Combined with a regular
forward product it gives an algebraic-group isomorphism.

This is a conditional construction: the Clifford coefficient and the regular
forward map are explicit inputs, not consequences of point bijectivity.
Source: the algebraic-isomorphism requirement in GLS3, Theorem 1.12.5(b),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
noncomputable section
namespace Triality.SimplyConnected.Pinning.CorootTorus
open Theory Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The entry or inverse entry of the regular ordinary-coordinate map. -/
private def ordinaryScalar (inverse : Bool) (i : Fin 4) :
    Variety.PolynomialFunction (closedSubgroup k).carrierVariety :=
  Variety.PolynomialFunction.pullback (ordinaryCoordinates k).toVariety
    (Variety.PolynomialFunction.ofPolynomial (dVariety k 4)
      (MvPolynomial.X (if inverse then Sum.inr (ULift.up i) else Sum.inl (ULift.up i))))

private theorem ordinaryScalar_parameter (inverse : Bool) (i : Fin 4)
    (t : Fin 4 → kˣ) :
    ordinaryScalar k inverse i (parameterPoint k t) =
      if inverse then (((diagonal k t i)⁻¹ : kˣ) : k) else (diagonal k t i : k) := by
  change evalPolynomial ((ordinaryCoordinates k).onPoints (parameterPoint k t)).val _ = _
  rw [ordinaryCoordinates_parameter, evalPolynomial_X]
  cases inverse <;> rfl

/-- All four Spin parameters recovered from one Spin coefficient and the
ordinary diagonal coordinates. The supplied polynomial is required to recover
`t₃`; its construction is the substantive remaining Clifford calculation. -/
def recoveryScalar (σ : Variety.PolynomialFunction (groupVariety k)) :
    Fin 4 → Variety.PolynomialFunction (closedSubgroup k).carrierVariety :=
  let spin := Variety.PolynomialFunction.pullback (closedSubgroup k).inclusion.toVariety σ
  ![ordinaryScalar k true 0,
    ordinaryScalar k true 0 * ordinaryScalar k true 1,
    ordinaryScalar k false 3 * spin, spin]

/-- One Clifford coefficient suffices to recover every fundamental coordinate. -/
theorem recoveryScalar_parameter
    (σ : Variety.PolynomialFunction (groupVariety k))
    (hσ : ∀ t, σ (parameter k t) = (t 3 : k))
    (t : Fin 4 → kˣ) (i : Fin 4) :
    recoveryScalar k σ i (parameterPoint k t) = (t i : k) := by
  have hspin : (Variety.PolynomialFunction.pullback
      (closedSubgroup k).inclusion.toVariety σ) (parameterPoint k t) = (t 3 : k) := by
    change σ ((closedSubgroup k).inclusion.onPoints (parameterPoint k t)) = _
    rw [inclusion_parameterPoint, hσ]
  fin_cases i
  · change ordinaryScalar k true 0 (parameterPoint k t) = _
    rw [ordinaryScalar_parameter]
    simp [diagonal]
  · change (ordinaryScalar k true 0 * ordinaryScalar k true 1) (parameterPoint k t) = _
    rw [polynomialFunction_mul_apply, ordinaryScalar_parameter, ordinaryScalar_parameter]
    simp [diagonal, mul_comm, mul_assoc]
  · change (ordinaryScalar k false 3 *
      Variety.PolynomialFunction.pullback (closedSubgroup k).inclusion.toVariety σ)
        (parameterPoint k t) = _
    rw [polynomialFunction_mul_apply, ordinaryScalar_parameter, hspin]
    simp [diagonal, mul_assoc]
  · exact hspin

private theorem recoveryScalar_inverse_parameter
    (σ : Variety.PolynomialFunction (groupVariety k))
    (hσ : ∀ t, σ (parameter k t) = (t 3 : k))
    (t : Fin 4 → kˣ) (i : Fin 4) :
    (Variety.PolynomialFunction.pullback (invMorphism (closedSubgroup k).carrierVariety)
      (recoveryScalar k σ i)) (parameterPoint k t) = ((t i)⁻¹ : kˣ) := by
  change recoveryScalar k σ i ((parameterPoint k t)⁻¹) = _
  have hinv : (parameterPoint k t)⁻¹ = parameterPoint k t⁻¹ := by
    apply (closedSubgroup k).inclusion_injective
    rw [map_inv, inclusion_parameterPoint, inclusion_parameterPoint]
    exact (map_inv (pointHom k) t).symm
  rw [hinv, recoveryScalar_parameter k σ hσ]
  rfl

/-- Polynomiality of the actual inverse point map, conditional only on a
single explicitly specified Clifford coefficient. -/
def inverseMorphismOfSpinCoefficient
    (σ : Variety.PolynomialFunction (groupVariety k))
    (hσ : ∀ t, σ (parameter k t) = (t 3 : k)) :
    AlgebraicGroup.Morphism (closedSubgroup k).carrierVariety (dVariety k 4) where
  toVariety :=
    { toFun := (coordinateEquiv k).symm
      regular := by
        intro c
        cases c with
        | inl i =>
          obtain ⟨p, hp⟩ := (recoveryScalar k σ i.down).representedBy
          refine ⟨p, ?_⟩
          intro x
          obtain ⟨y, rfl⟩ := (coordinateEquiv k).surjective x
          rw [MulEquiv.symm_apply_apply]
          rw [coordinateEquiv_apply]
          rw [← hp, recoveryScalar_parameter k σ hσ]
          rfl
        | inr i =>
          obtain ⟨p, hp⟩ := (Variety.PolynomialFunction.pullback
            (invMorphism (closedSubgroup k).carrierVariety)
            (recoveryScalar k σ i.down)).representedBy
          refine ⟨p, ?_⟩
          intro x
          obtain ⟨y, rfl⟩ := (coordinateEquiv k).surjective x
          rw [MulEquiv.symm_apply_apply]
          rw [coordinateEquiv_apply]
          rw [← hp, recoveryScalar_inverse_parameter k σ hσ]
          rfl }
  map_one := (coordinateEquiv k).symm.map_one
  map_mul := (coordinateEquiv k).symm.map_mul

/-- The inverse constructed from the Spin coefficient is inverse to the
published coroot product on points. -/
@[simp] theorem inverseMorphismOfSpinCoefficient_parameter
    (σ : Variety.PolynomialFunction (groupVariety k))
    (hσ : ∀ t, σ (parameter k t) = (t 3 : k))
    (x : Variety.Point (dVariety k 4)) :
    (inverseMorphismOfSpinCoefficient k σ hσ).onPoints
      (parameterPoint k (dPointEquiv 4 x)) = x :=
  (coordinateEquiv k).symm_apply_apply x


/-- Codomain restriction of a regular coroot product to the closed preimage. -/
def parametrizationOfMorphism
    (f : AlgebraicGroup.Morphism (dVariety k 4) (groupVariety k))
    (hf : ∀ x, f.onPoints x = parameter k (dPointEquiv 4 x)) :
    AlgebraicGroup.Morphism (dVariety k 4) (closedSubgroup k).carrierVariety :=
  f.codRestrictClosedSubgroup (closedSubgroup k) (fun x => by
    rw [hf]
    exact parameter_mem k _)

@[simp] theorem parametrizationOfMorphism_apply
    (f : AlgebraicGroup.Morphism (dVariety k 4) (groupVariety k))
    (hf : ∀ x, f.onPoints x = parameter k (dPointEquiv 4 x))
    (x : Variety.Point (dVariety k 4)) :
    (parametrizationOfMorphism k f hf).onPoints x =
      parameterPoint k (dPointEquiv 4 x) := by
  apply (closedSubgroup k).inclusion_injective
  rw [inclusion_parameterPoint]
  exact hf x

/-- Algebraic assembly: a regular product and one Clifford coefficient give
an algebraic isomorphism, including its regular inverse. -/
def isoOfRegularParameter
    (f : AlgebraicGroup.Morphism (dVariety k 4) (groupVariety k))
    (hf : ∀ x, f.onPoints x = parameter k (dPointEquiv 4 x))
    (σ : Variety.PolynomialFunction (groupVariety k))
    (hσ : ∀ t, σ (parameter k t) = (t 3 : k)) :
    AlgebraicGroup.Iso (dVariety k 4) (closedSubgroup k).carrierVariety where
  hom := parametrizationOfMorphism k f hf
  inv := inverseMorphismOfSpinCoefficient k σ hσ
  hom_inv_id x := by
    rw [parametrizationOfMorphism_apply]
    exact inverseMorphismOfSpinCoefficient_parameter k σ hσ x
  inv_hom_id y := by
    rw [parametrizationOfMorphism_apply]
    exact (coordinateEquiv k).apply_symm_apply y

/-- The assembled isomorphism has exactly the source coroot-word formula. -/
theorem isoOfRegularParameter_inclusion
    (f : AlgebraicGroup.Morphism (dVariety k 4) (groupVariety k))
    (hf : ∀ x, f.onPoints x = parameter k (dPointEquiv 4 x))
    (σ : Variety.PolynomialFunction (groupVariety k))
    (hσ : ∀ t, σ (parameter k t) = (t 3 : k))
    (x : Variety.Point (dVariety k 4)) :
    (closedSubgroup k).inclusion.onPoints
        ((isoOfRegularParameter k f hf σ hσ).hom.onPoints x) =
      (List.ofFn fun i : Fin 4 => simpleCoroot k i (dPointEquiv 4 x i)).prod := hf x

/-- The closed diagonal preimage is a torus once these two geometric inputs
have been constructed. -/
theorem isSubtorus_of_regularParameter
    (f : AlgebraicGroup.Morphism (dVariety k 4) (groupVariety k))
    (hf : ∀ x, f.onPoints x = parameter k (dPointEquiv 4 x))
    (σ : Variety.PolynomialFunction (groupVariety k))
    (hσ : ∀ t, σ (parameter k t) = (t 3 : k)) :
    IsSubtorus (closedSubgroup k) :=
  ⟨4, ⟨isoOfRegularParameter k f hf σ hσ⟩⟩

end Triality.SimplyConnected.Pinning.CorootTorus
