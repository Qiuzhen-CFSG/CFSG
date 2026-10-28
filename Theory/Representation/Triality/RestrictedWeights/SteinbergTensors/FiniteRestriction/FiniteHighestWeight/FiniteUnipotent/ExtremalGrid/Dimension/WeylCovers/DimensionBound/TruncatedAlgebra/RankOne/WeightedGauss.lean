module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.CoefficientLaws
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RankOne.Gauss
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RankOne.Expansion

/-!
# Rank-one Laurent expansions for the truncated coefficient algebra

For a direct-diagonal eigenvector of integral weight m, Gauss decomposition
expresses the upper-lower action as a finite sum of
`t^a s^b (1+s*t)^(m+b-a) F_a E_b v`. Reversing the two roots replaces the
exponent by `-m+a-b`. Both statements allow zero vectors and negative weights.
The finite bounds here come from rationality, with no bound by q imposed.

`RankOne.Parameters` compares every chart coefficient with the actual supplied
root coefficient and identifies their truncated algebras. `RankOne.Gauss`
proves the point identities and coefficient weight shifts. `RankOne.Expansion`
provides the finite polynomial expansions used below.

`RankOne.Straightening` extracts the mixed coefficients of these expansions
and proves torus-binomial membership. `RankOne.Conjugation` uses the same Gauss
calculus to prove root-point transport of the truncated algebra.

Sources: Steinberg, Representations of algebraic groups (1963), §§2–3;
GLS3 1.12.1 and Steinberg (6.1). The direct diagonal is `diag(z,z⁻¹)`;
the stored source coroot uses its inverse parameter.
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [IsAlgClosed k] in
private theorem rankOne_gauss_scalar (s t u : k) (hu : u ≠ 0) (m : ℤ) (a b : ℕ) :
    (s / u) ^ b * ((t / u) ^ a * u ^ (m + 2 * (b : ℤ))) =
      t ^ a * s ^ b * u ^ (m + (b : ℤ) - (a : ℤ)) := by
  rw [zpow_add₀ hu, zpow_sub₀ hu, zpow_add₀ hu,
    zpow_mul, zpow_natCast, zpow_natCast, zpow_natCast, zpow_ofNat]
  rw [← pow_mul, Nat.mul_comm 2 b, pow_mul]
  simp only [div_pow]
  field_simp

/-- Gauss decomposition on any integral eigenvector, including zero, in a
finite Laurent sum suitable for extracting mixed coefficients. -/
theorem rankOne_weighted_gauss (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (m : ℤ) (v : V) (hv : rankOneHasWeight f rho m v) :
    ∃ M N : ℕ,
      (∀ j, M ≤ j → curveCoefficient rho hr (f.comp standardSL2UpperMorphism) j = 0) ∧
      (∀ j, N ≤ j → curveCoefficient rho hr (f.comp standardSL2LowerMorphism) j = 0) ∧
      ∀ s t : k, 1 + s * t ≠ 0 →
        (rho.action (f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint s)))).val
          ((rho.action (f.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t)))).val v) =
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range M,
          (t ^ a * s ^ b * (1 + s * t) ^ (m + (b : ℤ) - (a : ℤ))) •
            curveCoefficient rho hr (f.comp standardSL2LowerMorphism) a
              (curveCoefficient rho hr (f.comp standardSL2UpperMorphism) b v) := by
  obtain ⟨M, hM, hE⟩ := rankOne_curveCoefficient_expansion rho hr (f.comp standardSL2UpperMorphism)
  obtain ⟨N, hN, hF⟩ := rankOne_curveCoefficient_expansion rho hr (f.comp standardSL2LowerMorphism)
  refine ⟨M, N, hM, hN, ?_⟩
  intro s t hu
  have hg := congrArg (fun g => (rho.action (f.onPoints g)).val v) (rankOne_gauss s t hu)
  simp only [map_mul, Units.val_mul, Module.End.mul_apply] at hg
  rw [hg]
  change (rho.action ((f.comp standardSL2LowerMorphism).onPoints (kPlusPoint (t / (1 + s * t))))).val
    ((rho.action (rankOneDiagonal f (Units.mk0 (1 + s * t) hu))).val
      ((rho.action ((f.comp standardSL2UpperMorphism).onPoints (kPlusPoint (s / (1 + s * t))))).val v)) = _
  rw [hE, hF]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [rankOne_upper_weight f rho hr m v hv b (Units.mk0 (1 + s * t) hu)]
  simp only [Units.val_mk0, map_smul, smul_smul]
  rw [rankOne_gauss_scalar s t (1 + s * t) hu m a b]


/-- The reversed Gauss expansion has weight exponent -m, because its
middle diagonal is the inverse of the direct diagonal. -/
theorem rankOne_weighted_gauss_reverse (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (m : ℤ) (v : V) (hv : rankOneHasWeight f rho m v) :
    ∃ M N : ℕ,
      (∀ j, M ≤ j → curveCoefficient rho hr (f.comp standardSL2UpperMorphism) j = 0) ∧
      (∀ j, N ≤ j → curveCoefficient rho hr (f.comp standardSL2LowerMorphism) j = 0) ∧
      ∀ s t : k, 1 + s * t ≠ 0 →
        (rho.action (f.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t)))).val
          ((rho.action (f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint s)))).val v) =
        ∑ b ∈ Finset.range M, ∑ a ∈ Finset.range N,
          (s ^ b * t ^ a * (1 + s * t) ^ (-m + (a : ℤ) - (b : ℤ))) •
            curveCoefficient rho hr (f.comp standardSL2UpperMorphism) b
              (curveCoefficient rho hr (f.comp standardSL2LowerMorphism) a v) := by
  obtain ⟨M, hM, hE⟩ := rankOne_curveCoefficient_expansion rho hr (f.comp standardSL2UpperMorphism)
  obtain ⟨N, hN, hF⟩ := rankOne_curveCoefficient_expansion rho hr (f.comp standardSL2LowerMorphism)
  refine ⟨M, N, hM, hN, ?_⟩
  intro s t hu
  have hg := congrArg (fun g => (rho.action (f.onPoints g)).val v) (rankOne_gauss_reverse s t hu)
  simp only [map_mul, Units.val_mul, Module.End.mul_apply] at hg
  rw [hg]
  change (rho.action ((f.comp standardSL2UpperMorphism).onPoints (kPlusPoint (s / (1 + s * t))))).val
    ((rho.action (rankOneDiagonal f (Units.mk0 (1 + s * t) hu)⁻¹)).val
      ((rho.action ((f.comp standardSL2LowerMorphism).onPoints (kPlusPoint (t / (1 + s * t))))).val v)) = _
  rw [hE, hF]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  rw [rankOne_lower_weight f rho hr m v hv a (Units.mk0 (1 + s * t) hu)⁻¹]
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0, map_smul, smul_smul, inv_zpow, ← zpow_neg]
  rw [show -(m - 2 * (a : ℤ)) = -m + 2 * (a : ℤ) by ring]
  rw [rankOne_gauss_scalar t s (1 + s * t) hu (-m) b a]

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
