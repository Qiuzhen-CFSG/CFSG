module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RankOne.Parameters
/-!
# Actual rank-one Gauss identities and coefficient weights

Matrix multiplication proves the two Gauss decompositions on `1 + s*t ≠ 0`.
Direct diagonal conjugation, followed by the coefficient intertwining theorem,
raises or lowers an integral weight by twice the coefficient order. The weight
predicate deliberately includes zero, so no nonvanishing is lost in iteration.

These identities are valid for every rational representation pulled back along
an SL₂ morphism. Extracting mixed coefficients of the resulting Laurent
identities is a further step; no divided-power straightening is assumed here.

Source: the rank-one relations of Steinberg, Representations of algebraic
groups (1963), §3.2, with direct diagonal `diag(z,z⁻¹)`.
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

@[expose] def rankOneTorusPoint (z : kˣ) : Variety.Point (KMult k) :=
  (dPointEquiv 1).symm (fun _ => z)

omit [IsAlgClosed k] in
@[simp] theorem rankOneTorusPoint_coordinate (z : kˣ) :
    dPointEquiv 1 (rankOneTorusPoint z) 0 = z := by
  simp [rankOneTorusPoint]

@[expose] def rankOneDiagonal (f : Morphism (slVariety k 2) K) (z : kˣ) : Variety.Point K :=
  f.onPoints (standardSL2DiagonalMorphism.onPoints (rankOneTorusPoint z))

theorem rankOne_gauss (s t : k) (h : 1 + s * t ≠ 0) :
    standardSL2UpperMorphism.onPoints (kPlusPoint s) *
      standardSL2LowerMorphism.onPoints (kPlusPoint t) =
      standardSL2LowerMorphism.onPoints (kPlusPoint (t / (1 + s * t))) *
        standardSL2DiagonalMorphism.onPoints (rankOneTorusPoint (Units.mk0 (1 + s * t) h)) *
        standardSL2UpperMorphism.onPoints (kPlusPoint (s / (1 + s * t))) := by
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change Matrix.transvection 0 1 s * Matrix.transvection 1 0 t =
    Matrix.transvection 1 0 (t / (1 + s * t)) *
      (slPointEquiv 2 (standardSL2DiagonalMorphism.onPoints
        (rankOneTorusPoint (Units.mk0 (1 + s * t) h)))).val *
      Matrix.transvection 0 1 (s / (1 + s * t))
  rw [LeftWeights.RankOne.diagonal_matrix, rankOneTorusPoint_coordinate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.one_apply, Matrix.single_apply] <;> field_simp [h] <;> ring_nf
  all_goals field_simp [h, show 1 + t * s ≠ 0 by simpa only [mul_comm t s] using h] <;> ring

theorem rankOne_gauss_reverse (s t : k) (h : 1 + s * t ≠ 0) :
    standardSL2LowerMorphism.onPoints (kPlusPoint t) *
      standardSL2UpperMorphism.onPoints (kPlusPoint s) =
      standardSL2UpperMorphism.onPoints (kPlusPoint (s / (1 + s * t))) *
        standardSL2DiagonalMorphism.onPoints (rankOneTorusPoint (Units.mk0 (1 + s * t) h)⁻¹) *
        standardSL2LowerMorphism.onPoints (kPlusPoint (t / (1 + s * t))) := by
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change Matrix.transvection 1 0 t * Matrix.transvection 0 1 s =
    Matrix.transvection 0 1 (s / (1 + s * t)) *
      (slPointEquiv 2 (standardSL2DiagonalMorphism.onPoints
        (rankOneTorusPoint (Units.mk0 (1 + s * t) h)⁻¹))).val *
      Matrix.transvection 1 0 (t / (1 + s * t))
  rw [LeftWeights.RankOne.diagonal_matrix, rankOneTorusPoint_coordinate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.one_apply, Matrix.single_apply] <;> field_simp [h] <;> ring_nf
  all_goals field_simp [h, show 1 + t * s ≠ 0 by simpa only [mul_comm t s] using h]

theorem rankOne_diagonal_upper (z : kˣ) (s : k) :
    standardSL2DiagonalMorphism.onPoints (rankOneTorusPoint z) *
      standardSL2UpperMorphism.onPoints (kPlusPoint s) =
      standardSL2UpperMorphism.onPoints (kPlusPoint ((z : k) ^ 2 * s)) *
        standardSL2DiagonalMorphism.onPoints (rankOneTorusPoint z) := by
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change (slPointEquiv 2 (standardSL2DiagonalMorphism.onPoints (rankOneTorusPoint z))).val *
      Matrix.transvection 0 1 s = Matrix.transvection 0 1 ((z : k) ^ 2 * s) *
        (slPointEquiv 2 (standardSL2DiagonalMorphism.onPoints (rankOneTorusPoint z))).val
  rw [LeftWeights.RankOne.diagonal_matrix, rankOneTorusPoint_coordinate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.one_apply, Matrix.single_apply]
  all_goals field_simp

theorem rankOne_diagonal_lower (z : kˣ) (s : k) :
    standardSL2DiagonalMorphism.onPoints (rankOneTorusPoint z) *
      standardSL2LowerMorphism.onPoints (kPlusPoint s) =
      standardSL2LowerMorphism.onPoints (kPlusPoint ((z : k)⁻¹ ^ 2 * s)) *
        standardSL2DiagonalMorphism.onPoints (rankOneTorusPoint z) := by
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change (slPointEquiv 2 (standardSL2DiagonalMorphism.onPoints (rankOneTorusPoint z))).val *
      Matrix.transvection 1 0 s = Matrix.transvection 1 0 ((z : k)⁻¹ ^ 2 * s) *
        (slPointEquiv 2 (standardSL2DiagonalMorphism.onPoints (rankOneTorusPoint z))).val
  rw [LeftWeights.RankOne.diagonal_matrix, rankOneTorusPoint_coordinate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.one_apply, Matrix.single_apply]
  all_goals field_simp

/-- Upper coefficients have direct diagonal degree twice their order. -/
theorem rankOne_upper_coefficient_torus (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (z : kˣ) (j : ℕ) :
    (rho.action (rankOneDiagonal f z)).val *
        curveCoefficient rho hr (f.comp standardSL2UpperMorphism) j =
      ((z : k) ^ 2) ^ j •
        (curveCoefficient rho hr (f.comp standardSL2UpperMorphism) j *
          (rho.action (rankOneDiagonal f z)).val) := by
  apply curveCoefficient_intertwine
  intro s
  have h := congrArg (fun g => (rho.action (f.onPoints g)).val)
    (rankOne_diagonal_upper z s)
  simpa only [rankOneDiagonal, Morphism.comp, Morphism.onPoints, Variety.Morphism.comp, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, Units.val_mul] using h

/-- Lower coefficients have the opposite direct diagonal degree. -/
theorem rankOne_lower_coefficient_torus (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (z : kˣ) (j : ℕ) :
    (rho.action (rankOneDiagonal f z)).val *
        curveCoefficient rho hr (f.comp standardSL2LowerMorphism) j =
      ((z : k)⁻¹ ^ 2) ^ j •
        (curveCoefficient rho hr (f.comp standardSL2LowerMorphism) j *
          (rho.action (rankOneDiagonal f z)).val) := by
  apply curveCoefficient_intertwine
  intro s
  have h := congrArg (fun g => (rho.action (f.onPoints g)).val)
    (rankOne_diagonal_lower z s)
  simpa only [rankOneDiagonal, Morphism.comp, Morphism.onPoints, Variety.Morphism.comp, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, Units.val_mul] using h

/-- A direct diagonal eigenvector. Zero belongs to every such weight space. -/
@[expose] def rankOneHasWeight (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (m : ℤ) (v : V) : Prop :=
  ∀ z : kˣ, (rho.action (rankOneDiagonal f z)).val v = (z : k) ^ m • v

/-- No nonzero-vector premise is used when transporting weights. -/
theorem rankOne_upper_weight (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (m : ℤ) (v : V) (hv : rankOneHasWeight f rho m v) (j : ℕ) :
    rankOneHasWeight f rho (m + 2 * j) (curveCoefficient rho hr (f.comp standardSL2UpperMorphism) j v) := by
  intro z
  have h := LinearMap.congr_fun (rankOne_upper_coefficient_torus f rho hr z j) v
  simp only [Module.End.mul_apply, LinearMap.smul_apply, hv z, map_smul, smul_smul] at h
  rw [h]
  congr 1
  rw [zpow_add₀ (Units.ne_zero z), zpow_mul, zpow_natCast, zpow_ofNat, mul_comm]

/-- Lower coefficients subtract twice their order, also on the zero vector. -/
theorem rankOne_lower_weight (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (m : ℤ) (v : V) (hv : rankOneHasWeight f rho m v) (j : ℕ) :
    rankOneHasWeight f rho (m - 2 * j) (curveCoefficient rho hr (f.comp standardSL2LowerMorphism) j v) := by
  intro z
  have h := LinearMap.congr_fun (rankOne_lower_coefficient_torus f rho hr z j) v
  simp only [Module.End.mul_apply, LinearMap.smul_apply, hv z, map_smul, smul_smul] at h
  rw [h]
  congr 1
  rw [sub_eq_add_neg, zpow_add₀ (Units.ne_zero z), zpow_neg, zpow_mul, zpow_natCast,
    zpow_ofNat, inv_pow, inv_pow, mul_comm]

end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
