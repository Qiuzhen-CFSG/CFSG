module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Spaces
public import Theory.AlgebraicGroup.RightTranslation.OrbitRational

/-!
# Realizing the full covariant space from a highest-weight cover

Every nonzero regular function with right Borel covariance is a highest
vector in its finite-dimensional rational right-translation orbit. A module
with the universal highest-vector mapping property therefore realizes every
such function as a matrix coefficient: lift that orbit's highest vector,
then compose the lift with evaluation at the identity. This gives a
surjective linear map from the covering module's dual onto the entire
published `covariantSpace`, and consequently a dimension upper bound.

`HighestWeightCover` records the standard Weyl-module mapping property. This
module does not construct a cover or assert its Weyl dimension formula. The
extremal dimension assembly must supply these algebraic representation facts
for each Borel. No finite evaluation or restriction theorem enters the proof.

Sources: the rational highest-weight setup of GLS3, Section 1.14, and the
extremal degree calculation in `refs/KGroup/GLS3/Chapter2St2.tex`, 13.2(d).
The latter refers to Steinberg, *Representations of algebraic groups*, Nagoya
Math. J. 22 (1963), Corollary 8.3; that statement concerns an irreducible
module and alone does not establish the full covariant-space bound.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
open Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- A finite rational module with the universal highest-vector mapping property.
No dimension estimate or finite-group assertion is included. -/
structure HighestWeightCover (S : Geometry K) (B : ClosedSubgroup K)
    (chi : TorusWeight S.torus) where
  Space : Type u
  [addCommGroup : AddCommGroup Space]
  [module : Module k Space]
  [finiteDimensional : FiniteDimensional k Space]
  action : RationalRepresentation K Space
  rational : IsRationalRepresentation action
  vector : Space
  highest : HasHighWeight action B S.torus vector chi
  lift : ∀ {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation K V), IsRationalRepresentation rho →
    ∀ v, HasHighWeight rho B S.torus v chi →
      ∃ F : Space →ₗ[k] V, Intertwines action rho F ∧ F vector = v

attribute [instance] HighestWeightCover.addCommGroup HighestWeightCover.module
  HighestWeightCover.finiteDimensional

variable (S : Geometry K) {P : Set S.roots.Root} {B : ClosedSubgroup K}
  {chi : TorusWeight S.torus}

omit [IsAlgClosed k] in
/-- The function itself is a highest vector in its rational right-translation orbit. -/
theorem rootCovariant_orbit_highest (hB : IsBorelOfPositiveSystem S.roots P B)
    (f : K.PolynomialFunction) (hf : RootCovariant S P chi f) (hf0 : f ≠ 0) :
    HasHighWeight (rightTranslateOrbitRationalRepresentation K f) B S.torus
      ⟨f, Submodule.subset_span ⟨1, rightMul_pullback_one K f⟩⟩ chi := by
  let v : rightTranslateOrbitSpan K f :=
    ⟨f, Submodule.subset_span ⟨1, rightMul_pullback_one K f⟩⟩
  have hv : v ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  refine ⟨⟨hv, ?_⟩, hv, ?_⟩
  · intro b hb
    obtain ⟨t, w, ht, hw, rfl⟩ := (BorelOfPositiveSystem.pointwise_decomposition hB b).mp hb
    let t' := S.torus.pointEquiv.symm ⟨t, ht⟩
    have ht' : S.torus.includePoint t' = t :=
      congrArg Subtype.val (S.torus.pointEquiv.apply_symm_apply ⟨t, ht⟩)
    refine ⟨chi.pointCharacter t', ?_⟩
    apply Subtype.ext
    apply Variety.PolynomialFunction.ext
    intro x
    rw [rightTranslateOrbitRationalRepresentation_apply]
    change f (x * (t * w)) = (chi.pointCharacter t' • f) x
    rw [polynomialFunction_smul_apply, ← mul_assoc, ← ht']
    exact hf x t' w hw
  · intro t
    apply Subtype.ext
    apply Variety.PolynomialFunction.ext
    intro x
    rw [rightTranslateOrbitRationalRepresentation_apply]
    change f (x * S.torus.includePoint t) = (chi.pointCharacter t • f) x
    rw [polynomialFunction_smul_apply]
    simpa only [mul_one] using hf x t 1 (Subgroup.one_mem _)

namespace HighestWeightCover
variable {S} (C : HighestWeightCover S B chi)
  (hB : IsBorelOfPositiveSystem S.roots P B)

private def coefficientFunction (l : Module.Dual k C.Space) : K.PolynomialFunction :=
  (exists_rootCovariant_matrixCoefficient S C.action C.rational hB
    C.vector chi C.highest l).choose

private theorem coefficientFunction_covariant (l : Module.Dual k C.Space) :
    RootCovariant S P chi (coefficientFunction C hB l) :=
  (exists_rootCovariant_matrixCoefficient S C.action C.rational hB
    C.vector chi C.highest l).choose_spec.1

private theorem coefficientFunction_apply (l : Module.Dual k C.Space)
    (g : Variety.Point K) :
    coefficientFunction C hB l g = l ((C.action.action g).1 C.vector) :=
  (exists_rootCovariant_matrixCoefficient S C.action C.rational hB
    C.vector chi C.highest l).choose_spec.2 g

/-- The actual regular matrix-coefficient map at the universal highest vector. -/
def coefficient : Module.Dual k C.Space →ₗ[k] covariantSpace S P chi where
  toFun l := ⟨coefficientFunction C hB l, coefficientFunction_covariant C hB l⟩
  map_add' l m := by
    apply Subtype.ext
    apply Variety.PolynomialFunction.ext
    intro g
    change coefficientFunction C hB (l + m) g =
      coefficientFunction C hB l g + coefficientFunction C hB m g
    simp only [coefficientFunction_apply, LinearMap.add_apply]
  map_smul' c l := by
    apply Subtype.ext
    apply Variety.PolynomialFunction.ext
    intro g
    change coefficientFunction C hB (c • l) g = (c • coefficientFunction C hB l) g
    simp only [polynomialFunction_smul_apply, coefficientFunction_apply,
      LinearMap.smul_apply, smul_eq_mul]

@[simp] theorem coefficient_apply (l : Module.Dual k C.Space) (g : Variety.Point K) :
    (C.coefficient hB l).val g = l ((C.action.action g).1 C.vector) :=
  coefficientFunction_apply C hB l g

/-- Every covariant regular function is a coefficient of the covering module.
The universal mapping property is applied to its actual finite translation orbit. -/
theorem coefficient_surjective : Function.Surjective (C.coefficient hB) := by
  intro f
  by_cases hf : f.val = 0
  · have hf' : f = 0 := Subtype.ext hf
    exact ⟨0, by rw [map_zero, hf']⟩
  let v : rightTranslateOrbitSpan K f.val :=
    ⟨f.val, Submodule.subset_span ⟨1, rightMul_pullback_one K f.val⟩⟩
  obtain ⟨F, hF, hFv⟩ := C.lift
    (rightTranslateOrbitRationalRepresentation K f.val)
    (rightTranslateOrbitRationalRepresentation_isRational K f.val) v
    (rootCovariant_orbit_highest S hB f.val f.property hf)
  let l : Module.Dual k C.Space :=
    (polynomialFunctionSubspaceEvaluation K (rightTranslateOrbitSpan K f.val) 1).comp F
  refine ⟨l, ?_⟩
  apply Subtype.ext
  apply Variety.PolynomialFunction.ext
  intro g
  rw [coefficient_apply]
  change (F ((C.action.action g).1 C.vector)).val 1 = f.val g
  rw [hF, hFv, rightTranslateOrbitRationalRepresentation_apply, one_mul]

include C hB in
/-- Finite dimensionality holds for the full covariant space, not only for a
chosen subspace of matrix coefficients. -/
theorem covariantSpace_finite : FiniteDimensional k (covariantSpace S P chi) :=
  Module.Finite.of_surjective (C.coefficient hB) (C.coefficient_surjective hB)

include hB in
/-- The full covariant space has dimension at most that of a highest-weight cover. -/
theorem finrank_covariantSpace_le :
    Module.finrank k (covariantSpace S P chi) ≤ Module.finrank k C.Space := by
  have h := LinearMap.finrank_le_finrank_of_surjective (C.coefficient_surjective hB)
  simpa only [Subspace.dual_finrank_eq] using h

end HighestWeightCover
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
