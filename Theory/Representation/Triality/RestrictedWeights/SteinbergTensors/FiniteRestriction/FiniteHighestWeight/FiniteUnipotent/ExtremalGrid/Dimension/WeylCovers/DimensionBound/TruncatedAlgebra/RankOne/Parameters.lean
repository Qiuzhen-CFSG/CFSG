module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.CoefficientLaws
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.CorootRealization.Comparison
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.Coroots
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.RankOne

/-!
# Coordinates for opposite-root coefficient calculations

The algebra of a marked opposite pair uses the root parameters actually stored
in the D4 geometry. A compatible SL₂ chart need not use those parameters.
Regular additive-group automorphisms are nonzero scalar rescalings; extracting
coefficients therefore gives a power of that scalar in every degree and leaves
the generated algebra unchanged. The chart diagonal is the left coroot, the
inverse-parameter version of the source coroot.

These are coordinate comparisons, without a normalization or straightening
assumption. They prepare the rank-one calculation for arbitrary rational
representations, including zero vectors and arbitrary truncation lengths.

Sources: GLS3 1.3.5(a), 1.12.1; Steinberg, Representations of algebraic groups
(1963), §§2–3. Direct left-action weights use the convention of Steinberg (6.1).
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
open ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Reparametrizing a curve multiplies its degree-j coefficient by c^j. -/
theorem rankOne_curveCoefficient_rescale (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x y : Morphism (KPlus k) K) (c : k)
    (h : ∀ t, x.onPoints (kPlusPoint t) = y.onPoints (kPlusPoint (c * t)))
    (j : ℕ) : curveCoefficient rho hr x j = c ^ j • curveCoefficient rho hr y j := by
  have he := curveCoefficient_intertwine rho hr x y 1 c (fun t => ?_) j
  · simpa only [one_mul, mul_one] using he
  simp only [one_mul, mul_one, h]

/-- The coefficient algebra of two specified additive curves. -/
@[expose] def rankOneCurveAlgebra (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x y : Morphism (KPlus k) K) (q : ℕ) :
    Subalgebra k (Module.End k V) :=
  Algebra.adjoin k (Set.range (fun j : Fin q => curveCoefficient rho hr x j) ∪
    Set.range (fun j : Fin q => curveCoefficient rho hr y j))

theorem rankOneCurveAlgebra_first (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x y : Morphism (KPlus k) K) (q j : ℕ)
    (hj : j < q) : curveCoefficient rho hr x j ∈ rankOneCurveAlgebra rho hr x y q :=
  Algebra.subset_adjoin (Or.inl ⟨⟨j, hj⟩, rfl⟩)

theorem rankOneCurveAlgebra_second (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x y : Morphism (KPlus k) K) (q j : ℕ)
    (hj : j < q) : curveCoefficient rho hr y j ∈ rankOneCurveAlgebra rho hr x y q :=
  Algebra.subset_adjoin (Or.inr ⟨⟨j, hj⟩, rfl⟩)

private theorem rankOneCurveAlgebra_rescale_le (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x y x' y' : Morphism (KPlus k) K)
    (c d : k)
    (hx : ∀ t, x.onPoints (kPlusPoint t) = x'.onPoints (kPlusPoint (c * t)))
    (hy : ∀ t, y.onPoints (kPlusPoint t) = y'.onPoints (kPlusPoint (d * t)))
    (q : ℕ) : rankOneCurveAlgebra rho hr x y q ≤ rankOneCurveAlgebra rho hr x' y' q := by
  apply Algebra.adjoin_le_iff.mpr
  intro a ha
  rcases ha with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · change curveCoefficient rho hr x j ∈ rankOneCurveAlgebra rho hr x' y' q
    rw [rankOne_curveCoefficient_rescale rho hr x x' c hx]
    exact (rankOneCurveAlgebra rho hr x' y' q).smul_mem
      (rankOneCurveAlgebra_first rho hr x' y' q j j.isLt) _
  · change curveCoefficient rho hr y j ∈ rankOneCurveAlgebra rho hr x' y' q
    rw [rankOne_curveCoefficient_rescale rho hr y y' d hy]
    exact (rankOneCurveAlgebra rho hr x' y' q).smul_mem
      (rankOneCurveAlgebra_second rho hr x' y' q j j.isLt) _

/-- Independent nonzero changes of root parameters preserve the whole algebra. -/
theorem rankOneCurveAlgebra_rescale (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x y x' y' : Morphism (KPlus k) K)
    (c d : k) (hc : c ≠ 0) (hd : d ≠ 0)
    (hx : ∀ t, x.onPoints (kPlusPoint t) = x'.onPoints (kPlusPoint (c * t)))
    (hy : ∀ t, y.onPoints (kPlusPoint t) = y'.onPoints (kPlusPoint (d * t)))
    (q : ℕ) : rankOneCurveAlgebra rho hr x y q = rankOneCurveAlgebra rho hr x' y' q := by
  apply le_antisymm (rankOneCurveAlgebra_rescale_le rho hr x y x' y' c d hx hy q)
  apply rankOneCurveAlgebra_rescale_le rho hr x' y' x y c⁻¹ d⁻¹ _ _ q
  · intro t
    rw [hx]
    simp [hc]
  · intro t
    rw [hy]
    simp [hd]

variable [CharP k 2]

/-- The subalgebra generated by the actual marked simple root and its negative. -/
@[expose] def rankOneAlgebra (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (i : Fin 4) (q : ℕ) :
    Subalgebra k (Module.End k V) :=
  rankOneCurveAlgebra rho hr (rootCurve S (S.simpleRoot i).val)
    (rootCurve S (S.roots.neg (S.simpleRoot i).val)) q

/-- This pair algebra is a subalgebra of the full D4 coefficient algebra. -/
theorem rankOneAlgebra_le (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (i : Fin 4) (q : ℕ) :
    rankOneAlgebra S rho hr i q ≤ coefficientAlgebra S rho hr q := by
  apply Algebra.adjoin_le_iff.mpr
  intro a ha
  rcases ha with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact rootCoefficient_mem S rho hr q _ j j.isLt
  · exact rootCoefficient_mem S rho hr q _ j j.isLt

/-- Include the actual chart in the original ambient group. -/
@[expose] def rankOneChartMap {S : Geometry K} {i : Fin 4}
    (C : SimpleRootSL2Chart S i) : Morphism (slVariety k 2) K :=
  (oppositePairGeneratedSubgroup (S.roots.rootSubgroup (S.simpleRoot i).val)
    (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val))).inclusion.comp C.map

theorem rankOneChartMap_upper {S : Geometry K} {i : Fin 4}
    (C : SimpleRootSL2Chart S i) (t : k) :
    (rankOneChartMap C).onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) =
      (S.roots.rootSubgroup (S.simpleRoot i).val).includePoint (C.plus.value t) := by
  have h := congrArg (fun f : Morphism (KPlus k)
    (oppositePairGeneratedSubgroup _ _).carrierVariety => f.onPoints (kPlusPoint t))
      C.compatible.1
  change (oppositePairPlusMorphism _ _).onPoints (C.plus.value t) =
    C.map.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) at h
  change (oppositePairGeneratedSubgroup _ _).inclusion.onPoints
    (C.map.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t))) = _
  rw [← h]
  exact oppositePairPlusMorphism_inclusion_apply _ _ _

theorem rankOneChartMap_lower {S : Geometry K} {i : Fin 4}
    (C : SimpleRootSL2Chart S i) (t : k) :
    (rankOneChartMap C).onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t)) =
      (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).includePoint
        (C.minus.value t) := by
  have h := congrArg (fun f : Morphism (KPlus k)
    (oppositePairGeneratedSubgroup _ _).carrierVariety => f.onPoints (kPlusPoint t))
      C.compatible.2
  change (oppositePairMinusMorphism _ _).onPoints (C.minus.value t) =
    C.map.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t)) at h
  change (oppositePairGeneratedSubgroup _ _).inclusion.onPoints
    (C.map.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t))) = _
  rw [← h]
  exact oppositePairMinusMorphism_inclusion_apply _ _ _

/-- The direct diagonal is the left coroot, not the raw source coroot. -/
theorem rankOneChartMap_diagonal {S : Geometry K} {i : Fin 4}
    (C : SimpleRootSL2Chart S i) (t : Variety.Point (KMult k)) :
    (rankOneChartMap C).onPoints (standardSL2DiagonalMorphism.onPoints t) =
      S.torus.includePoint ((S.leftSimpleCoroot i).onPoints t) := by
  have hd : standardSL2DiagonalMorphism.onPoints t = binarySL2Coroot.onPoints t⁻¹ := by
    apply (slPointEquiv 2).injective
    apply Subtype.ext
    change (slPointEquiv 2 (standardSL2DiagonalMorphism.onPoints t)).val =
      slPointMatrix 2 (binarySL2Coroot.onPoints t⁻¹)
    rw [LeftWeights.RankOne.diagonal_matrix, binarySL2Coroot_matrix,
      LeftWeights.dPointEquiv_inverse]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.diagonal]
  rw [hd]
  change (oppositePairGeneratedSubgroup _ _).inclusion.onPoints
    (C.map.onPoints (binarySL2Coroot.onPoints t⁻¹)) = _
  rw [← C.cocharacter_inclusion_apply, SimpleRootSL2Chart.cocharacter_eq S i C]
  rfl

/-- Simultaneous comparisons of actual points and every higher coefficient.
The two scalars are independent and neither is silently set to one. -/
theorem rankOneChart_rescale (S : Geometry K) (i : Fin 4)
    (C : SimpleRootSL2Chart S i) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) :
    ∃ c d : k, c ≠ 0 ∧ d ≠ 0 ∧
      (∀ t, (rootCurve S (S.simpleRoot i).val).onPoints (kPlusPoint t) =
        (rankOneChartMap C).onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint (c * t)))) ∧
      (∀ t, (rootCurve S (S.roots.neg (S.simpleRoot i).val)).onPoints (kPlusPoint t) =
        (rankOneChartMap C).onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint (d * t)))) ∧
      (∀ j, rootCoefficient S rho hr (S.simpleRoot i).val j =
        c ^ j • curveCoefficient rho hr ((rankOneChartMap C).comp standardSL2UpperMorphism) j) ∧
      (∀ j, rootCoefficient S rho hr (S.roots.neg (S.simpleRoot i).val) j =
        d ^ j • curveCoefficient rho hr ((rankOneChartMap C).comp standardSL2LowerMorphism) j) := by
  obtain ⟨c, ⟨hc, he⟩, _⟩ := oneParameterParametrization_eq_rescale
    C.plus (S.rootParameter (S.simpleRoot i).val)
  obtain ⟨d, ⟨hd, hf⟩, _⟩ := oneParameterParametrization_eq_rescale
    C.minus (S.rootParameter (S.roots.neg (S.simpleRoot i).val))
  have hx (t : k) : (rootCurve S (S.simpleRoot i).val).onPoints (kPlusPoint t) =
      (rankOneChartMap C).onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint (c * t))) := by
    rw [rankOneChartMap_upper]
    exact congrArg (S.roots.rootSubgroup (S.simpleRoot i).val).includePoint (he t)
  have hy (t : k) : (rootCurve S (S.roots.neg (S.simpleRoot i).val)).onPoints (kPlusPoint t) =
      (rankOneChartMap C).onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint (d * t))) := by
    rw [rankOneChartMap_lower]
    exact congrArg (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).includePoint (hf t)
  exact ⟨c, d, hc, hd, hx, hy,
    rankOne_curveCoefficient_rescale rho hr _ _ c hx,
    rankOne_curveCoefficient_rescale rho hr _ _ d hy⟩

/-- Actual and chart coordinates generate precisely the same truncated algebra. -/
theorem rankOneAlgebra_eq_chart (S : Geometry K) (i : Fin 4)
    (C : SimpleRootSL2Chart S i) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (q : ℕ) :
    rankOneAlgebra S rho hr i q = rankOneCurveAlgebra rho hr
      ((rankOneChartMap C).comp standardSL2UpperMorphism)
      ((rankOneChartMap C).comp standardSL2LowerMorphism) q := by
  obtain ⟨c, d, hc, hd, hx, hy, _, _⟩ := rankOneChart_rescale S i C rho hr
  exact rankOneCurveAlgebra_rescale rho hr _ _ _ _ c d hc hd hx hy q

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
