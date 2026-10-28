module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RankOne.Conjugation
/-!
# Transport by both actual opposite simple-root curves

The SL₂ Weyl word conjugates each root into the opposite root with parameter
minus the original parameter. Its regular conjugation morphism transfers the
upper transport theorem to the lower root. Independent nonzero parameter
rescalings then identify the chart algebra with the actual supplied root
coefficient algebra and transport both families of actual points.

The truncation length is arbitrary, hence in particular may be `2^n` with
`n=1`. The only geometric witness is the specified simple-root SL₂ chart.

Source: SL₂ Weyl conjugation and Gauss decomposition supporting Steinberg,
*Representations of algebraic groups* (1963), §§2–3; GLS3 1.12.1.
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private def transportWeylPoint : Variety.Point (slVariety k 2) :=
  standardSL2UpperMorphism.onPoints (kPlusPoint 1) *
    standardSL2LowerMorphism.onPoints (kPlusPoint (-1)) *
      standardSL2UpperMorphism.onPoints (kPlusPoint 1)

private theorem transportWeyl_upper (s : k) :
    transportWeylPoint * standardSL2UpperMorphism.onPoints (kPlusPoint s) =
      standardSL2LowerMorphism.onPoints (kPlusPoint (-s)) * transportWeylPoint := by
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change (Matrix.transvection 0 1 1 * Matrix.transvection 1 0 (-1) *
    Matrix.transvection 0 1 1) * Matrix.transvection 0 1 s =
      Matrix.transvection 1 0 (-s) * (Matrix.transvection 0 1 1 *
        Matrix.transvection 1 0 (-1) * Matrix.transvection 0 1 1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.one_apply, Matrix.single_apply]

private theorem transportWeyl_lower (s : k) :
    transportWeylPoint * standardSL2LowerMorphism.onPoints (kPlusPoint s) =
      standardSL2UpperMorphism.onPoints (kPlusPoint (-s)) * transportWeylPoint := by
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change (Matrix.transvection 0 1 1 * Matrix.transvection 1 0 (-1) *
    Matrix.transvection 0 1 1) * Matrix.transvection 1 0 s =
      Matrix.transvection 0 1 (-s) * (Matrix.transvection 0 1 1 *
        Matrix.transvection 1 0 (-1) * Matrix.transvection 0 1 1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.one_apply, Matrix.single_apply]

private def transportSwap : Morphism (slVariety k 2) (slVariety k 2) where
  toVariety := Theory.AlgebraicGroup.conjugationByMorphism _ transportWeylPoint
  map_one := by simp [Theory.AlgebraicGroup.conjugationByMorphism_apply]
  map_mul := by
    intro x y
    simp only [Theory.AlgebraicGroup.conjugationByMorphism_apply]
    group

private theorem transportSwap_upper (s : k) :
    transportSwap.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint s)) =
      standardSL2LowerMorphism.onPoints (kPlusPoint (-s)) := by
  change (Theory.AlgebraicGroup.conjugationByMorphism _ transportWeylPoint).toFun _ = _
  rw [Theory.AlgebraicGroup.conjugationByMorphism_apply, transportWeyl_upper, mul_inv_cancel_right]

private theorem transportSwap_lower (s : k) :
    transportSwap.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint s)) =
      standardSL2UpperMorphism.onPoints (kPlusPoint (-s)) := by
  change (Theory.AlgebraicGroup.conjugationByMorphism _ transportWeylPoint).toFun _ = _
  rw [Theory.AlgebraicGroup.conjugationByMorphism_apply, transportWeyl_lower, mul_inv_cancel_right]

/-- Lower-root transport follows by the actual regular Weyl conjugation of SL₂.
The parameter sign is retained, so this also holds outside characteristic two. -/
theorem rankOneCurveAlgebra_lower_transport (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (q : ℕ) (s : k) (a : Module.End k V)
    (ha : a ∈ rankOneCurveAlgebra rho hr
      (f.comp standardSL2UpperMorphism) (f.comp standardSL2LowerMorphism) q) :
    ∃ b ∈ rankOneCurveAlgebra rho hr
      (f.comp standardSL2UpperMorphism) (f.comp standardSL2LowerMorphism) q,
      (rho.action (f.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint s)))).val * a =
        b * (rho.action (f.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint s)))).val := by
  let f' := f.comp transportSwap
  have hx (t : k) : (f'.comp standardSL2UpperMorphism).onPoints (kPlusPoint t) =
      (f.comp standardSL2LowerMorphism).onPoints (kPlusPoint ((-1)*t)) := by
    change f.onPoints (transportSwap.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t))) = _
    rw [transportSwap_upper]
    simp only [neg_one_mul]
    rfl
  have hy (t : k) : (f'.comp standardSL2LowerMorphism).onPoints (kPlusPoint t) =
      (f.comp standardSL2UpperMorphism).onPoints (kPlusPoint ((-1)*t)) := by
    change f.onPoints (transportSwap.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t))) = _
    rw [transportSwap_lower]
    simp only [neg_one_mul]
    rfl
  have hA : rankOneCurveAlgebra rho hr (f'.comp standardSL2UpperMorphism)
      (f'.comp standardSL2LowerMorphism) q =
      rankOneCurveAlgebra rho hr (f.comp standardSL2UpperMorphism)
        (f.comp standardSL2LowerMorphism) q := by
    rw [rankOneCurveAlgebra_rescale rho hr _ _ _ _ (-1) (-1)
      (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero) hx hy]
    unfold rankOneCurveAlgebra
    rw [Set.union_comm]
  obtain ⟨b, hb, he⟩ := rankOneCurveAlgebra_upper_transport f' rho hr q (-s) a (hA.symm ▸ ha)
  refine ⟨b, hA ▸ hb, ?_⟩
  have hp : f'.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint (-s))) =
      f.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint s)) := by
    change f.onPoints (transportSwap.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint (-s)))) = _
    rw [transportSwap_upper, neg_neg]
  simpa only [hp] using he

variable [CharP k 2]
open ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization

/-- Every point of the actual chosen simple root transports its opposite-pair
coefficient algebra, for arbitrary truncation length. -/
theorem rankOneAlgebra_simple_transport (S : Geometry K) (i : Fin 4)
    (C : SimpleRootSL2Chart S i) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (q : ℕ) (s : k) (a : Module.End k V)
    (ha : a ∈ rankOneAlgebra S rho hr i q) :
    ∃ b ∈ rankOneAlgebra S rho hr i q,
      (rho.action ((rootCurve S (S.simpleRoot i).val).onPoints (kPlusPoint s))).val * a =
        b * (rho.action ((rootCurve S (S.simpleRoot i).val).onPoints (kPlusPoint s))).val := by
  obtain ⟨c, d, hc, hd, hx, hy, hE, hF⟩ := rankOneChart_rescale S i C rho hr
  rw [rankOneAlgebra_eq_chart S i C rho hr q] at ha ⊢
  rw [hx]
  exact rankOneCurveAlgebra_upper_transport (rankOneChartMap C) rho hr q (c*s) a ha

/-- Every point of the actual opposite simple root transports the same algebra.
In particular both transport statements apply at q=2^n, including n=1. -/
theorem rankOneAlgebra_opposite_transport (S : Geometry K) (i : Fin 4)
    (C : SimpleRootSL2Chart S i) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (q : ℕ) (s : k) (a : Module.End k V)
    (ha : a ∈ rankOneAlgebra S rho hr i q) :
    ∃ b ∈ rankOneAlgebra S rho hr i q,
      (rho.action ((rootCurve S (S.roots.neg (S.simpleRoot i).val)).onPoints (kPlusPoint s))).val * a =
        b * (rho.action ((rootCurve S (S.roots.neg (S.simpleRoot i).val)).onPoints (kPlusPoint s))).val := by
  obtain ⟨c, d, hc, hd, hx, hy, hE, hF⟩ := rankOneChart_rescale S i C rho hr
  rw [rankOneAlgebra_eq_chart S i C rho hr q] at ha ⊢
  rw [hy]
  exact rankOneCurveAlgebra_lower_transport (rankOneChartMap C) rho hr q (d*s) a ha

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
