module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.RootOperators
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.SimpleRootOrbits.RankOneDegree
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.CorootRealization.Comparison
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.Coroots
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.RankOne

/-!
# Transporting rank-one degree bounds to the supplied D4 roots

A compatible SL₂ chart has the stored raw coroot; its standard diagonal is
therefore the left coroot. Regular additive-group automorphisms are scalar
rescalings, so replacing the chart parameters by the independently supplied
root parameters preserves the degree bound. The positive and opposite Borel
arguments retain their respective character and inverse character.

Sources: GLS3 §1.3.5(a), §§1.9, 1.12, 1.14; Steinberg (6.1), 13.2(d).
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
open Theory.AlgebraicGroup AlgebraicTensor.RestrictedStep
open ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A fixed vector has only a constant coefficient on a rational root curve. -/
theorem curveCoefficient_eq_zero_of_fixed
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (x : Morphism (KPlus k) K) (v : V)
    (hx : ∀ t : k, (rho.action (x.onPoints (kPlusPoint t))).val v = v)
    (j : ℕ) (hj : j ≠ 0) : curveCoefficient rho hr x j v = 0 := by
  have hp (l : Module.Dual k V) : curvePolynomial rho hr x l v = Polynomial.C (l v) := by
    apply Polynomial.funext
    intro t
    rw [curvePolynomial_eval, hx, Polynomial.eval_C]
  simp [curveCoefficient, hp, Polynomial.coeff_C, hj]

/-- Pointwise scalar reparametrization gives the corresponding polynomial
substitution, with no normalization assumption on either curve. -/
theorem curvePolynomial_eq_comp_of_rescale
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (x y : Morphism (KPlus k) K) (c : k)
    (hxy : ∀ t : k, y.onPoints (kPlusPoint t) = x.onPoints (kPlusPoint (c * t)))
    (l : Module.Dual k V) (v : V) :
    curvePolynomial rho hr y l v =
      (curvePolynomial rho hr x l v).comp (Polynomial.C c * Polynomial.X) := by
  apply Polynomial.funext
  intro t
  rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, curvePolynomial_eval, curvePolynomial_eval, hxy]

/-- Vanishing of a scalar coefficient is preserved by scalar reparametrization. -/
theorem curveCoefficient_eq_zero_of_rescale
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (x y : Morphism (KPlus k) K) (c : k)
    (hxy : ∀ t : k, y.onPoints (kPlusPoint t) = x.onPoints (kPlusPoint (c * t)))
    (v : V) (j : ℕ)
    (hx : ∀ l : Module.Dual k V, (curvePolynomial rho hr x l v).coeff j = 0) :
    curveCoefficient rho hr y j v = 0 := by
  have hy (l : Module.Dual k V) : (curvePolynomial rho hr y l v).coeff j = 0 := by
    rw [curvePolynomial_eq_comp_of_rescale rho hr x y c hxy,
      Polynomial.comp_C_mul_X_coeff, hx, zero_mul]
  simp [curveCoefficient, hy]

variable [CharP k 2]

/-- Include the chart's genuine rank-one map into the original ambient group. -/
@[expose] def simpleRootChartMap {S : Geometry K} {i : Fin 4}
    (A : SimpleRootSL2Chart S i) : Morphism (slVariety k 2) K :=
  (oppositePairGeneratedSubgroup (S.roots.rootSubgroup (S.simpleRoot i).val)
    (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val))).inclusion.comp A.map

theorem simpleRootChartMap_upper {S : Geometry K} {i : Fin 4}
    (A : SimpleRootSL2Chart S i) (t : k) :
    (simpleRootChartMap A).onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) =
      (S.roots.rootSubgroup (S.simpleRoot i).val).includePoint (A.plus.value t) := by
  have h := congrArg (fun f : Morphism (KPlus k)
    (oppositePairGeneratedSubgroup _ _).carrierVariety => f.onPoints (kPlusPoint t))
      A.compatible.1
  change (oppositePairPlusMorphism _ _).onPoints (A.plus.value t) =
    A.map.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) at h
  change (oppositePairGeneratedSubgroup _ _).inclusion.onPoints
    (A.map.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t))) = _
  rw [← h]
  exact oppositePairPlusMorphism_inclusion_apply _ _ _

theorem simpleRootChartMap_lower {S : Geometry K} {i : Fin 4}
    (A : SimpleRootSL2Chart S i) (t : k) :
    (simpleRootChartMap A).onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t)) =
      (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).includePoint
        (A.minus.value t) := by
  have h := congrArg (fun f : Morphism (KPlus k)
    (oppositePairGeneratedSubgroup _ _).carrierVariety => f.onPoints (kPlusPoint t))
      A.compatible.2
  change (oppositePairMinusMorphism _ _).onPoints (A.minus.value t) =
    A.map.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t)) at h
  change (oppositePairGeneratedSubgroup _ _).inclusion.onPoints
    (A.map.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t))) = _
  rw [← h]
  exact oppositePairMinusMorphism_inclusion_apply _ _ _

private theorem standardDiagonal_eq_binaryCoroot_inv (t : Variety.Point (KMult k)) :
    standardSL2DiagonalMorphism.onPoints t = binarySL2Coroot.onPoints t⁻¹ := by
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change (slPointEquiv 2 (standardSL2DiagonalMorphism.onPoints t)).val =
    slPointMatrix 2 (binarySL2Coroot.onPoints t⁻¹)
  rw [LeftWeights.RankOne.diagonal_matrix, binarySL2Coroot_matrix, LeftWeights.dPointEquiv_inverse]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

/-- The standard diagonal is the actual left coroot, including parameter inversion. -/
theorem simpleRootChartMap_diagonal {S : Geometry K} {i : Fin 4}
    (A : SimpleRootSL2Chart S i) (t : Variety.Point (KMult k)) :
    (simpleRootChartMap A).onPoints (standardSL2DiagonalMorphism.onPoints t) =
      S.torus.includePoint ((S.leftSimpleCoroot i).onPoints t) := by
  rw [standardDiagonal_eq_binaryCoroot_inv]
  change (oppositePairGeneratedSubgroup _ _).inclusion.onPoints
    (A.map.onPoints (binarySL2Coroot.onPoints t⁻¹)) = _
  rw [← A.cocharacter_inclusion_apply, SimpleRootSL2Chart.cocharacter_eq S i A]
  rfl

omit [IsAlgClosed k] in
private theorem simpleRoot_positive (S : Geometry K) (i : Fin 4) :
    (S.simpleRoot i).val ∈ S.roots.positive :=
  ((S.realized.2.2.2.2.2.2.2.2.2.2.2.1 _).mp (S.simpleRoot i).property).1

omit [FiniteDimensional k V] in
private theorem highWeight_root_fixed (S : Geometry K)
    {P : Set S.roots.Root} {B : ClosedSubgroup K}
    (hB : IsBorelOfPositiveSystem S.roots P B)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (v : V) {chi : TorusWeight S.torus} (hv : HasHighWeight rho B S.torus v chi)
    (r : S.roots.Root) (hrP : r ∈ P)
    (x : OneParameterParametrization (S.roots.rootSubgroup r).carrierVariety) (t : k) :
    (rho.action ((S.roots.rootSubgroup r).includePoint (x.value t))).val v = v := by
  apply invariantLine_fixed_of_unipotent_subgroup rho hr B hB.unipotent v hv.1
    hB.radical.1 hB.radical.2.1
  change (S.roots.rootSubgroup r).includePoint (x.value t) ∈ hB.unipotent.toSubgroup
  rw [hB.root_generated]
  exact rootSubgroup_le_RootSubgroupGenerated S.roots hrP
    ((S.roots.rootSubgroup r).pointEquiv _).property

/-- A positive highest vector has no nonconstant coefficients on any positive root. -/
theorem rootCoefficient_eq_zero_of_positive_highest (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (v : V) {chi : TorusWeight S.torus}
    (hv : HasHighWeight rho S.bigCell.data.B S.torus v chi)
    (r : S.roots.Root) (hrP : r ∈ S.roots.positive) (j : ℕ) (hj : j ≠ 0) :
    rootCoefficient S rho hr r j v = 0 :=
  curveCoefficient_eq_zero_of_fixed rho hr (rootCurve S r) v
    (highWeight_root_fixed S S.bigCell.data.positive_witness rho hr v hv r hrP
      (S.rootParameter r)) j hj

/-- The analogous fixation statement retains the opposite Borel. -/
theorem rootCoefficient_eq_zero_of_negative_highest (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (v : V) {chi : TorusWeight S.torus}
    (hv : HasHighWeight rho S.bigCell.data.Bopp S.torus v chi)
    (r : S.roots.Root) (hrP : S.roots.neg r ∈ S.roots.positive) (j : ℕ) (hj : j ≠ 0) :
    rootCoefficient S rho hr r j v = 0 :=
  curveCoefficient_eq_zero_of_fixed rho hr (rootCurve S r) v
    (highWeight_root_fixed S S.bigCell.data.opposite_witness rho hr v hv r hrP
      (S.rootParameter r)) j hj

/-- A compatible chart bounds the actual negative simple-root coefficients by
the corresponding nonnegative highest-weight coordinate. -/
theorem negative_simple_rootCoefficient_eq_zero (S : Geometry K) (i : Fin 4)
    (A : SimpleRootSL2Chart S i)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (v : V) (a : Weight) (m : ℕ) (ha : a i = (m : ℤ))
    (hv : HasHighWeight rho S.bigCell.data.B S.torus v (S.leftWeightEmbedding a))
    (j : ℕ) (hj : m < j) :
    rootCoefficient S rho hr (S.roots.neg (S.simpleRoot i).val) j v = 0 := by
  obtain ⟨c, ⟨_, hc⟩, _⟩ := oneParameterParametrization_eq_rescale
    A.minus (S.rootParameter (S.roots.neg (S.simpleRoot i).val))
  refine curveCoefficient_eq_zero_of_rescale rho hr
    ((simpleRootChartMap A).comp standardSL2LowerMorphism) _ c ?_ v j ?_
  · intro t
    change (S.roots.rootSubgroup _).includePoint ((S.rootParameter _).value t) =
      (simpleRootChartMap A).onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint (c * t)))
    rw [simpleRootChartMap_lower, hc]
  · intro l
    apply sl2_lower_curvePolynomial_coeff_eq_zero (simpleRootChartMap A) rho hr v m ?_ ?_ l j hj
    · intro t
      rw [simpleRootChartMap_upper]
      exact highWeight_root_fixed S S.bigCell.data.positive_witness rho hr v hv _
        (simpleRoot_positive S i) A.plus t
    · intro t
      rw [simpleRootChartMap_diagonal, hv.2.2, S.leftWeightEmbedding_coroot, ha, zpow_natCast]

/-- For an opposite highest vector, the inverse character bounds the positive
simple-root orbit with the same nonnegative coordinate. -/
theorem positive_simple_rootCoefficient_eq_zero_of_opposite (S : Geometry K) (i : Fin 4)
    (A : SimpleRootSL2Chart S i)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (v : V) (a : Weight) (m : ℕ) (ha : a i = (m : ℤ))
    (hv : HasHighWeight rho S.bigCell.data.Bopp S.torus v (S.leftWeightEmbedding a)⁻¹)
    (j : ℕ) (hj : m < j) :
    rootCoefficient S rho hr (S.simpleRoot i).val j v = 0 := by
  obtain ⟨c, ⟨_, hc⟩, _⟩ := oneParameterParametrization_eq_rescale
    A.plus (S.rootParameter (S.simpleRoot i).val)
  refine curveCoefficient_eq_zero_of_rescale rho hr
    ((simpleRootChartMap A).comp standardSL2UpperMorphism) _ c ?_ v j ?_
  · intro t
    change (S.roots.rootSubgroup _).includePoint ((S.rootParameter _).value t) =
      (simpleRootChartMap A).onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint (c * t)))
    rw [simpleRootChartMap_upper, hc]
  · intro l
    apply sl2_upper_curvePolynomial_coeff_eq_zero (simpleRootChartMap A) rho hr v m ?_ ?_ l j hj
    · intro t
      rw [simpleRootChartMap_lower]
      apply highWeight_root_fixed S S.bigCell.data.opposite_witness rho hr v hv _ ?_ A.minus t
      change S.roots.neg (S.roots.neg (S.simpleRoot i).val) ∈ S.roots.positive
      rw [S.realized.neg_neg]
      exact simpleRoot_positive S i
    · intro t
      rw [simpleRootChartMap_diagonal, hv.2.2]
      have he : ((S.leftWeightEmbedding a)⁻¹).pointCharacter
          ((S.leftSimpleCoroot i).onPoints t) =
        ((S.leftWeightEmbedding a).pointCharacter ((S.leftSimpleCoroot i).onPoints t))⁻¹ := by
        change (torusPointEval _ _ ((S.leftWeightEmbedding a)⁻¹) : k) = _
        rw [map_inv, Units.val_inv_eq_inv_val]
        rfl
      rw [he, S.leftWeightEmbedding_coroot, ha, zpow_natCast]

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
