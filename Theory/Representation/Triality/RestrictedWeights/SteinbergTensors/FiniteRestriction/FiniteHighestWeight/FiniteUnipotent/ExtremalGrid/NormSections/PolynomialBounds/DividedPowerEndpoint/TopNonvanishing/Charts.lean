module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.TopNonvanishing.RankOne
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.RankOne

/-!
# Rank-one endpoints for the supplied D4 root parameters

The diagonal of a compatible chart is the left simple coroot. Comparing its
root parameters with the supplied independent parameters introduces nonzero
scalar powers. Thus the rank-one coefficient endpoints transfer without a
mutual normalization assumption on the positive and negative root curves.

Source: GLS3 §1.12 and Steinberg (1963), §4.3. The source coroot is inverse
to the direct diagonal; the left-weight adapter performs that inversion.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
open AlgebraicTensor.RestrictedStep CyclicDimension
open ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Include a compatible simple-root chart in the actual ambient group. -/
@[expose] def simpleChartMap {S : Geometry K} {i : Fin 4} (C : SimpleRootSL2Chart S i) :
    Morphism (slVariety k 2) K :=
  (oppositePairGeneratedSubgroup _ _).inclusion.comp C.map

/-- The ambient chart preserves its positive parametrization. -/
theorem simpleChartMap_upper {S : Geometry K} {i : Fin 4} (C : SimpleRootSL2Chart S i) :
    (simpleChartMap C).comp standardSL2UpperMorphism =
      (S.roots.rootSubgroup (S.simpleRoot i).val).inclusion.comp C.plus.hom := by
  apply Morphism.ext
  funext t
  have h := congrArg (fun f : Morphism (KPlus k)
    (oppositePairGeneratedSubgroup _ _).carrierVariety => f.onPoints t) C.compatible.1
  change (oppositePairPlusMorphism _ _).onPoints (C.plus.hom.onPoints t) =
    C.map.onPoints (standardSL2UpperMorphism.onPoints t) at h
  change (oppositePairGeneratedSubgroup _ _).inclusion.onPoints
    (C.map.onPoints (standardSL2UpperMorphism.onPoints t)) = _
  rw [← h]
  exact oppositePairPlusMorphism_inclusion_apply _ _ _

/-- The ambient chart preserves its negative parametrization. -/
theorem simpleChartMap_lower {S : Geometry K} {i : Fin 4} (C : SimpleRootSL2Chart S i) :
    (simpleChartMap C).comp standardSL2LowerMorphism =
      (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).inclusion.comp C.minus.hom := by
  apply Morphism.ext
  funext t
  have h := congrArg (fun f : Morphism (KPlus k)
    (oppositePairGeneratedSubgroup _ _).carrierVariety => f.onPoints t) C.compatible.2
  change (oppositePairMinusMorphism _ _).onPoints (C.minus.hom.onPoints t) =
    C.map.onPoints (standardSL2LowerMorphism.onPoints t) at h
  change (oppositePairGeneratedSubgroup _ _).inclusion.onPoints
    (C.map.onPoints (standardSL2LowerMorphism.onPoints t)) = _
  rw [← h]
  exact oppositePairMinusMorphism_inclusion_apply _ _ _

/-- The matrix Weyl point maps to the existing chart word at parameter one. -/
theorem simpleChartMap_weyl {S : Geometry K} {i : Fin 4} (C : SimpleRootSL2Chart S i) :
    (simpleChartMap C).onPoints rankOneWeylPoint = C.parameters.word 1 := by
  have hw : (rankOneWeylPoint (k := k)) =
      standardSL2UpperMorphism.onPoints (kPlusPoint 1) *
        standardSL2LowerMorphism.onPoints (kPlusPoint 1) *
          standardSL2UpperMorphism.onPoints (kPlusPoint 1) := by
    apply (slPointEquiv 2).injective
    apply Subtype.ext
    change (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) k) =
      Matrix.transvection 0 1 1 * Matrix.transvection 1 0 1 * Matrix.transvection 0 1 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
        Matrix.single_apply, Matrix.one_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  rw [hw, map_mul, map_mul]
  have hu := congrArg (fun f : Morphism (KPlus k) K => f.onPoints (kPlusPoint 1))
    (simpleChartMap_upper C)
  have hl := congrArg (fun f : Morphism (KPlus k) K => f.onPoints (kPlusPoint 1))
    (simpleChartMap_lower C)
  change (simpleChartMap C).onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint 1)) = _ at hu
  change (simpleChartMap C).onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint 1)) = _ at hl
  rw [hu, hl]
  simp only [ClassBound.FixedOpposition.AmbientNormalizer.SimpleRootParameters.word,
    SimpleRootSL2Chart.parameters, inv_one, Units.val_one, CharTwo.neg_eq]
  rfl

private theorem diagonal_eq_binaryCoroot_inv (t : Variety.Point (KMult k)) :
    standardSL2DiagonalMorphism.onPoints t = binarySL2Coroot.onPoints t⁻¹ := by
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  rw [LeftWeights.RankOne.diagonal_matrix]
  change _ = slPointMatrix 2 (binarySL2Coroot.onPoints t⁻¹)
  rw [binarySL2Coroot_matrix, LeftWeights.dPointEquiv_inverse]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

/-- The standard SL₂ diagonal is exactly the left simple coroot, not the raw one. -/
theorem simpleChartMap_diagonal {S : Geometry K} {i : Fin 4} (C : SimpleRootSL2Chart S i)
    (t : Variety.Point (KMult k)) :
    (simpleChartMap C).onPoints (standardSL2DiagonalMorphism.onPoints t) =
      S.torus.includePoint ((S.leftSimpleCoroot i).onPoints t) := by
  rw [diagonal_eq_binaryCoroot_inv]
  change (oppositePairGeneratedSubgroup _ _).inclusion.onPoints
    (C.map.onPoints (binarySL2Coroot.onPoints t⁻¹)) = _
  rw [← C.cocharacter_inclusion_apply, SimpleRootSL2Chart.cocharacter_eq S i C]
  rfl

/-- A simple lowering endpoint in the literal supplied parameter, with its
nonzero rescaling factor retained. The zero vector is allowed. -/
theorem simpleRoot_lower_endpoint (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (i : Fin 4) (C : SimpleRootSL2Chart S i)
    (a : D4RestrictedWeight.Weight) (v : V) (m : ℕ)
    (ha : a i = (m : ℤ))
    (hv : v ∈ weightSpace rho S.torus (S.leftWeightEmbedding a))
    (hu : ∀ t : k, (rho.action ((rootCurve S (S.simpleRoot i).val).onPoints
      (kPlusPoint t))).val v = v) :
    ∃ c : k, c ≠ 0 ∧ rootDividedPower S rho hr (S.roots.neg (S.simpleRoot i).val) m v =
      c ^ m • (rho.action ((simpleChartMap C).onPoints rankOneWeylPoint)).val v := by
  obtain ⟨d, hd, _⟩ := oneParameterParametrization_eq_rescale
    (S.rootParameter (S.simpleRoot i).val) C.plus
  have hupper (t : k) : (rho.action ((simpleChartMap C).onPoints
      (standardSL2UpperMorphism.onPoints (kPlusPoint t)))).val v = v := by
    change (rho.action (((simpleChartMap C).comp standardSL2UpperMorphism).onPoints
      (kPlusPoint t))).val v = v
    rw [simpleChartMap_upper]
    change (rho.action ((S.roots.rootSubgroup (S.simpleRoot i).val).includePoint
      (C.plus.value t))).val v = v
    rw [hd.2 t]
    exact hu (d * t)
  have hdiagonal (t : Variety.Point (KMult k)) :
      (rho.action ((simpleChartMap C).onPoints (standardSL2DiagonalMorphism.onPoints t))).val v =
        (dPointEquiv 1 t 0 : k) ^ m • v := by
    rw [simpleChartMap_diagonal, hv, S.leftWeightEmbedding_coroot a i t, ha, zpow_natCast]
  have he := rankOne_lower_endpoint rho hr (simpleChartMap C) v m hupper hdiagonal
  rw [simpleChartMap_lower] at he
  obtain ⟨c, hc, heq⟩ := coefficient_change_parameter rho hr
    (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)) C.minus
    (S.rootParameter (S.roots.neg (S.simpleRoot i).val))
  refine ⟨c, hc, ?_⟩
  change curveCoefficient rho hr
    ((S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).inclusion.comp
      (S.rootParameter (S.roots.neg (S.simpleRoot i).val)).hom) m v = _
  rw [heq m, LinearMap.smul_apply, he]

/-- Nonvanishing of the actual simple lowering endpoint. -/
theorem simpleRoot_lower_endpoint_ne_zero (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (i : Fin 4) (C : SimpleRootSL2Chart S i)
    (a : D4RestrictedWeight.Weight) (v : V) (m : ℕ)
    (ha : a i = (m : ℤ)) (hv0 : v ≠ 0)
    (hv : v ∈ weightSpace rho S.torus (S.leftWeightEmbedding a))
    (hu : ∀ t : k, (rho.action ((rootCurve S (S.simpleRoot i).val).onPoints
      (kPlusPoint t))).val v = v) :
    rootDividedPower S rho hr (S.roots.neg (S.simpleRoot i).val) m v ≠ 0 := by
  obtain ⟨c, hc, he⟩ := simpleRoot_lower_endpoint S rho hr i C a v m ha hv hu
  rw [he]
  apply smul_ne_zero (pow_ne_zero _ hc)
  exact fun h => hv0 (((LinearMap.GeneralLinearGroup.generalLinearEquiv k V)
    (rho.action ((simpleChartMap C).onPoints rankOneWeylPoint))).injective
      (h.trans (map_zero _).symm))

/-- A simple raising endpoint in the literal supplied parameter, with its
nonzero rescaling factor retained. The zero vector is allowed. -/
theorem simpleRoot_upper_endpoint (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (i : Fin 4) (C : SimpleRootSL2Chart S i)
    (a : D4RestrictedWeight.Weight) (v : V) (m : ℕ)
    (ha : a i = -(m : ℤ))
    (hv : v ∈ weightSpace rho S.torus (S.leftWeightEmbedding a))
    (hl : ∀ t : k, (rho.action ((rootCurve S (S.roots.neg (S.simpleRoot i).val)).onPoints
      (kPlusPoint t))).val v = v) :
    ∃ c : k, c ≠ 0 ∧ rootDividedPower S rho hr (S.simpleRoot i).val m v =
      c ^ m • (rho.action ((simpleChartMap C).onPoints rankOneWeylPoint)).val v := by
  obtain ⟨d, hd, _⟩ := oneParameterParametrization_eq_rescale
    (S.rootParameter (S.roots.neg (S.simpleRoot i).val)) C.minus
  have hlower (t : k) : (rho.action ((simpleChartMap C).onPoints
      (standardSL2LowerMorphism.onPoints (kPlusPoint t)))).val v = v := by
    change (rho.action (((simpleChartMap C).comp standardSL2LowerMorphism).onPoints
      (kPlusPoint t))).val v = v
    rw [simpleChartMap_lower]
    change (rho.action ((S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).includePoint
      (C.minus.value t))).val v = v
    rw [hd.2 t]
    exact hl (d * t)
  have hdiagonal (t : Variety.Point (KMult k)) :
      (rho.action ((simpleChartMap C).onPoints (standardSL2DiagonalMorphism.onPoints t))).val v =
        (dPointEquiv 1 t 0 : k)⁻¹ ^ m • v := by
    rw [simpleChartMap_diagonal, hv, S.leftWeightEmbedding_coroot a i t, ha,
      zpow_neg, zpow_natCast, inv_pow]
  have he := rankOne_upper_endpoint rho hr (simpleChartMap C) v m hlower hdiagonal
  rw [simpleChartMap_upper] at he
  obtain ⟨c, hc, heq⟩ := coefficient_change_parameter rho hr
    (S.roots.rootSubgroup (S.simpleRoot i).val) C.plus
    (S.rootParameter (S.simpleRoot i).val)
  refine ⟨c, hc, ?_⟩
  change curveCoefficient rho hr
    ((S.roots.rootSubgroup (S.simpleRoot i).val).inclusion.comp
      (S.rootParameter (S.simpleRoot i).val).hom) m v = _
  rw [heq m, LinearMap.smul_apply, he]

/-- Nonvanishing of the actual simple raising endpoint. -/
theorem simpleRoot_upper_endpoint_ne_zero (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (i : Fin 4) (C : SimpleRootSL2Chart S i)
    (a : D4RestrictedWeight.Weight) (v : V) (m : ℕ)
    (ha : a i = -(m : ℤ)) (hv0 : v ≠ 0)
    (hv : v ∈ weightSpace rho S.torus (S.leftWeightEmbedding a))
    (hl : ∀ t : k, (rho.action ((rootCurve S (S.roots.neg (S.simpleRoot i).val)).onPoints
      (kPlusPoint t))).val v = v) :
    rootDividedPower S rho hr (S.simpleRoot i).val m v ≠ 0 := by
  obtain ⟨c, hc, he⟩ := simpleRoot_upper_endpoint S rho hr i C a v m ha hv hl
  rw [he]
  apply smul_ne_zero (pow_ne_zero _ hc)
  exact fun h => hv0 (((LinearMap.GeneralLinearGroup.generalLinearEquiv k V)
    (rho.action ((simpleChartMap C).onPoints rankOneWeylPoint))).injective
      (h.trans (map_zero _).symm))

end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
