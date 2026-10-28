module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalInput
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.Coordinates
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenSpinIsogeny

/-!
# The first highest vector in the concrete Spin natural action

The ambient Clifford action is a regular map to GL. Transport it along a
linear equivalence from four hyperbolic planes to eight scalar coordinates;
regular matrix coefficients prove rationality in the new coordinates.

The vector is the first vector in the first hyperbolic summand. Positive-root
induction in the original standard D4 base makes its first root coordinate
nonnegative, and the explicit root matrices then fix this vector. The source
coroot product acts by the inverse of its zeroth parameter. This sign is
retained in characteristic two.

These are facts about the concrete Spin carrier. Transport to arbitrary
Geometry requires the separate compatible algebraic-group comparison.

Sources: GLS3, Theorem 1.12.1 and Example 1.14.9(d),
`refs/KGroup/GLS3/Chapter1.tex`; Steinberg (6.1) and §13,
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions.NaturalConstruction
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

private def spinRepresentation : RationalRepresentation (groupVariety k) (QuadraticSpace k) :=
  ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv k _).symm.toMonoidHom.comp
    ((quadraticIsometrySubgroup (quadraticForm k)).subtype.comp (naturalAction k))⟩

omit [CharP k 2] in
private theorem spinRepresentation_rational : IsRationalRepresentation (spinRepresentation k) := by
  refine ⟨Module.finBasis k _, evenSpinAmbientActionMorphism _ (standardHyperbolicSplit 4), ?_⟩
  intro g
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k _).injective
  change _ = (naturalAction k g).1
  exact (evenSpinAmbientActionMorphism_linear_points
    (quadraticForm k) (standardHyperbolicSplit 4) g).trans
      (congrArg Subtype.val (toOmega_val k g).symm)

private def highestVector : QuadraticSpace k := (Pi.single 0 1, 0)

omit [IsAlgClosed k] [CharP k 2] in
private theorem highestVector_ne_zero : highestVector k ≠ 0 := by
  intro h
  have := congrArg (fun v : QuadraticSpace k => v.1 0) h
  simp [highestVector] at this

private theorem highestVector_parameter (t : Fin 4 → kˣ) :
    (naturalAction k (CorootTorus.parameter k t)).1 (highestVector k) =
      ((t 0 : k)⁻¹) • highestVector k := by
  rw [CorootTorus.naturalAction_parameter]
  apply Prod.ext <;> funext i
  · by_cases hi : i = 0
    · subst i
      simp [highestVector, hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry,
        hyperbolicDiagonalLinearEquiv, CorootTorus.diagonal]
    · simp [highestVector, hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry,
        hyperbolicDiagonalLinearEquiv, Pi.single_apply, hi]
  · simp [highestVector, hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry,
      hyperbolicDiagonalLinearEquiv]

private theorem simple_first_nonneg (r : TypeDRootIndex 4)
    (hr : r ∈ (typeDRootPairing_base 2).support) :
    0 ≤ typeDRootVector 4 r 0 := by
  rw [← SetLike.mem_coe, typeDRootPairing_base_support] at hr
  obtain ⟨i, rfl⟩ := hr
  fin_cases i <;> norm_num [typeDSimpleRootIndex, typeDRootVector, basisVector]

private theorem positive_first_nonneg (r : TypeDRootIndex 4)
    (hr : (typeDRootPairing_base 2).IsPos r) :
    0 ≤ typeDRootVector 4 r 0 := by
  refine hr.induction_on_add simple_first_nonneg ?_
  intro r s t h hr hs
  have he := congrArg (fun x : typeDRootSpan 4 => (x : Vec 4) 0) h
  change typeDRootVector 4 t 0 = typeDRootVector 4 r 0 + typeDRootVector 4 s 0 at he
  rw [he]
  exact add_nonneg hr (simple_first_nonneg s hs)

set_option linter.unusedSimpArgs false in
private theorem highestVector_root (r : TypeDRootIndex 4)
    (hr : (typeDRootPairing_base 2).IsPos r) (a : k) :
    (naturalAction k (rootPoint k r a)).1 (highestVector k) = highestVector k := by
  rw [naturalAction_rootPoint]
  have hfirst := positive_first_nonneg r hr
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  have hj : j ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le i) hij)
  have hsi : s = -1 → i ≠ 0 := by
    intro hs hi
    subst i
    norm_num [typeDRootVector, basisVector, hs, hj, Ne.symm hj] at hfirst
  rcases hs with hs | hs <;> rcases ht with ht | ht <;> subst s <;> subst t
  all_goals
    norm_num only [evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      reduceDIte]
    apply Prod.ext <;> funext p
  all_goals
    try have hi : i ≠ 0 := hsi rfl
  all_goals
    simp_all [highestVector, hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv, hyperbolicSkewUpperRoot,
      hyperbolicSkewUpperRootLinearEquiv, Pi.single_apply]

private def coordinates : QuadraticSpace k ≃ₗ[k] (Fin 8 → k) :=
  LinearEquiv.ofFinrankEq (R := k) _ _
    (by simp [QuadraticSpace, HyperbolicSpace, Module.finrank_prod])

/-- The regular Clifford natural action transported to eight scalar coordinates. -/
def coordinateAction : RationalRepresentation (groupVariety k) (Fin 8 → k) :=
  ⟨(LinearMap.GeneralLinearGroup.congrLinearEquiv (coordinates k)).toMonoidHom.comp
    (spinRepresentation k).action⟩

omit [CharP k 2] in
/-- The coordinate action is conjugate to the actual Clifford action. -/
private theorem coordinateAction_apply (g : Points k) (v : Fin 8 → k) :
    ((coordinateAction k).action g).1 v =
      coordinates k ((naturalAction k g).1 ((coordinates k).symm v)) := rfl

omit [CharP k 2] in
/-- Regularity follows from the ambient Spin morphism and its matrix coefficients. -/
theorem coordinateAction_rational : IsRationalRepresentation (coordinateAction k) := by
  obtain ⟨b₀, f₀, hf₀⟩ := spinRepresentation_rational k
  let b := Module.finBasis k (Fin 8 → k)
  let c := fun i j => rationalRepresentationLinearMatrixCoefficient (spinRepresentation k) b₀ f₀
    ((b.coord i).comp (coordinates k).toLinearMap) ((coordinates k).symm (b j))
  have hc : ∀ i j g, c i j g = b.repr (((coordinateAction k).action g).1 (b j)) i := by
    intro i j g
    exact rationalRepresentationLinearMatrixCoefficient_apply
      (spinRepresentation k) b₀ f₀ hf₀ _ _ g
  let ci := fun i j => Variety.PolynomialFunction.pullback
    (Theory.AlgebraicGroup.invMorphism (groupVariety k)) (c i j)
  have hci : ∀ i j g, ci i j g =
      b.repr ((((coordinateAction k).action g)⁻¹).1 (b j)) i := by
    intro i j g
    change c i j g⁻¹ = _
    rw [hc, map_inv]
  let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient b
    (coordinateAction k).action c ci hc hci
  exact ⟨b, f, fun g =>
    glPointEquivOf_generalLinearRepresentationPoint b ((coordinateAction k).action g)⟩

/-- The first hyperbolic basis vector, in eight scalar coordinates. -/
def coordinateVector : Fin 8 → k := coordinates k (highestVector k)

omit [IsAlgClosed k] [CharP k 2] in
/-- The chosen vector is nonzero. -/
theorem coordinateVector_ne_zero : coordinateVector k ≠ 0 := by
  intro h
  exact highestVector_ne_zero k ((coordinates k).injective (h.trans (map_zero _).symm))

/-- The source coroot product acts with raw exponent minus one at node zero. -/
theorem coordinateVector_parameter (t : Fin 4 → kˣ) :
    ((coordinateAction k).action (CorootTorus.parameter k t)).1 (coordinateVector k) =
      ((t 0 : k)⁻¹) • coordinateVector k := by
  rw [coordinateAction_apply, coordinateVector, LinearEquiv.symm_apply_apply,
    highestVector_parameter, map_smul]

/-- Every root positive in the original standard D4 base fixes the vector. -/
theorem coordinateVector_root (r : TypeDRootIndex 4)
    (hr : (typeDRootPairing_base 2).IsPos r) (a : k) :
    ((coordinateAction k).action (rootPoint k r a)).1 (coordinateVector k) =
      coordinateVector k := by
  rw [coordinateAction_apply, coordinateVector, LinearEquiv.symm_apply_apply,
    highestVector_root k r hr]

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions.NaturalConstruction
