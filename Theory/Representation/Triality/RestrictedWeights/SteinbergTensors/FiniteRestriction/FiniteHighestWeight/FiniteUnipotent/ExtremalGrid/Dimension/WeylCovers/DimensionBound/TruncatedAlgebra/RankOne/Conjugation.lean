module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RankOne.Straightening
/-!
# Conjugation of truncated opposite-root coefficients

Gauss decomposition gives `E(s)F(t)E(-s)` with upper parameter
`-s²t/(1+st)`. On each integral eigenvector, extracting its t-coefficient
leaves only indices `a+c≤j`. The resulting operators are
`F_a H(-a-c,j-a-c) E_c`; all their orders are at most j. Straightening and
Vandermonde already put these torus binomials in the opposite-root algebra.
Algebra-adjoin induction therefore proves transport by every upper point.

All polynomial bounds come from rationality and may exceed the truncation.
No irreducibility, PBW, or ambient normalization is assumed.

Source: SL₂ Gauss decomposition and integral divided powers underlying
Steinberg, *Representations of algebraic groups* (1963), §§2–3.
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
open AlgebraicTensor.RestrictedStep
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private theorem conjugation_gauss (s t : k) (h : 1+s*t ≠ 0) :
    standardSL2UpperMorphism.onPoints (kPlusPoint s) *
      standardSL2LowerMorphism.onPoints (kPlusPoint t) *
        standardSL2UpperMorphism.onPoints (kPlusPoint (-s)) =
      standardSL2LowerMorphism.onPoints (kPlusPoint (t/(1+s*t))) *
        standardSL2DiagonalMorphism.onPoints (rankOneTorusPoint (Units.mk0 (1+s*t) h)) *
          standardSL2UpperMorphism.onPoints (kPlusPoint (-s^2*t/(1+s*t))) := by
  rw [rankOne_gauss s t h, mul_assoc, ← map_mul, kPlusPoint_mul]
  congr 3
  field_simp
  ring

omit [IsAlgClosed k] in
private theorem conjugation_scalar (r t u : k) (hu : u ≠ 0) (m : ℤ) (a c : ℕ) :
    (t/u)^a * ((r*t/u)^c * u^(m+2*(c:ℤ))) =
      r^c * t^(a+c) * u^(m+(c:ℤ)-(a:ℤ)) := by
  rw [zpow_add₀ hu, zpow_sub₀ hu, zpow_add₀ hu,
    zpow_mul, zpow_natCast, zpow_natCast, zpow_natCast, zpow_ofNat]
  rw [← pow_mul, Nat.mul_comm 2 c, pow_mul]
  simp only [div_pow, mul_pow, pow_add]
  field_simp

/-- The coefficient of a conjugated opposite root is a finite sum using only
root and torus-binomial orders at most its own order. -/
theorem rankOne_upper_conjugation_coefficients (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) :
    ∃ M N : ℕ, ∀ s : k, ∀ j : ℕ,
      (rho.action (f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint s)))).val *
        curveCoefficient rho hr (f.comp standardSL2LowerMorphism) j *
          (rho.action (f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint (-s))))).val =
        ∑ a ∈ Finset.range N, ∑ c ∈ Finset.range M,
          if a+c ≤ j then ((-s^2)^c * s^(j-(a+c))) •
            (curveCoefficient rho hr (f.comp standardSL2LowerMorphism) a *
              rankOneTorusBinomial f rho hr (-(a:ℤ)-(c:ℤ)) (j-(a+c)) *
                curveCoefficient rho hr (f.comp standardSL2UpperMorphism) c) else 0 := by
  classical
  obtain ⟨M, hM, hE⟩ := rankOne_curveCoefficient_expansion rho hr (f.comp standardSL2UpperMorphism)
  obtain ⟨N, hN, hF⟩ := rankOne_curveCoefficient_expansion rho hr (f.comp standardSL2LowerMorphism)
  refine ⟨M, N, ?_⟩
  intro s j
  apply rankOne_weight_ext f rho hr
  intro m v hv
  apply (Module.finBasis k V).repr.injective
  ext z
  let l := (Module.finBasis k V).coord z
  let L := (rho.action (f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint s)))).val
  let R := (rho.action (f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint (-s))))).val
  change l (L (curveCoefficient rho hr (f.comp standardSL2LowerMorphism) j (R v))) = l _
  have hpoly : ∀ t : k, 1+s*t ≠ 0 →
      (curvePolynomial rho hr (f.comp standardSL2LowerMorphism) (l.comp L) (R v)).eval t =
      ∑ a ∈ Finset.range N, ∑ c ∈ Finset.range M,
        ((-s^2)^c * l (curveCoefficient rho hr (f.comp standardSL2LowerMorphism) a
          (curveCoefficient rho hr (f.comp standardSL2UpperMorphism) c v))) *
          t^(a+c) * (1+s*t)^(m+(c:ℤ)-(a:ℤ)) := by
    intro t ht
    have hg := congrArg (fun g => (rho.action (f.onPoints g)).val v) (conjugation_gauss s t ht)
    simp only [map_mul, Units.val_mul, Module.End.mul_apply] at hg
    rw [curvePolynomial_eval, LinearMap.comp_apply]
    change l ((rho.action (f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint s)))).val
      ((rho.action (f.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t)))).val
        ((rho.action (f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint (-s))))).val v))) = _
    rw [hg]
    change l ((rho.action ((f.comp standardSL2LowerMorphism).onPoints (kPlusPoint (t/(1+s*t))))).val
      ((rho.action (rankOneDiagonal f (Units.mk0 (1+s*t) ht))).val
        ((rho.action ((f.comp standardSL2UpperMorphism).onPoints (kPlusPoint (-s^2*t/(1+s*t))))).val v))) = _
    rw [hE, hF]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro c hc
    rw [rankOne_upper_weight f rho hr m v hv c (Units.mk0 (1+s*t) ht)]
    simp only [Units.val_mk0, map_smul, smul_eq_mul]
    have hs := conjugation_scalar (-s^2) t (1+s*t) ht m a c
    linear_combination hs * l (curveCoefficient rho hr (f.comp standardSL2LowerMorphism) a
      (curveCoefficient rho hr (f.comp standardSL2UpperMorphism) c v))
  have he := rankOne_laurent_coeff ((Finset.range N) ×ˢ (Finset.range M))
    (fun ac => (-s^2)^ac.2 * l (curveCoefficient rho hr (f.comp standardSL2LowerMorphism) ac.1
      (curveCoefficient rho hr (f.comp standardSL2UpperMorphism) ac.2 v)))
    (fun ac => ac.1+ac.2) (fun ac => m+(ac.2:ℤ)-(ac.1:ℤ)) s
    (curvePolynomial rho hr (f.comp standardSL2LowerMorphism) (l.comp L) (R v))
    (fun t ht => by rw [hpoly t ht, Finset.sum_product]) j
  rw [Finset.sum_product] at he
  change (l.comp L) (curveCoefficient rho hr (f.comp standardSL2LowerMorphism) j (R v)) = _
  rw [dual_curveCoefficient, he]
  simp only [LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  split_ifs with hac
  · simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_eq_mul]
    rw [rankOneTorusBinomial_apply_weight f rho hr _ (m+2*(c:ℤ)) _ _
      (rankOne_upper_weight f rho hr m v hv c)]
    simp only [map_smul, smul_eq_mul]
    rw [show m+2*(c:ℤ)+(-(a:ℤ)-(c:ℤ)) = m+(c:ℤ)-(a:ℤ) by ring]
    ring
  · simp

/-- Every upper point transports the truncated opposite-root algebra. -/
theorem rankOneCurveAlgebra_upper_transport (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (q : ℕ) (s : k) (a : Module.End k V)
    (ha : a ∈ rankOneCurveAlgebra rho hr
      (f.comp standardSL2UpperMorphism) (f.comp standardSL2LowerMorphism) q) :
    ∃ b ∈ rankOneCurveAlgebra rho hr
      (f.comp standardSL2UpperMorphism) (f.comp standardSL2LowerMorphism) q,
      (rho.action (f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint s)))).val * a =
        b * (rho.action (f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint s)))).val := by
  let A := rankOneCurveAlgebra rho hr
    (f.comp standardSL2UpperMorphism) (f.comp standardSL2LowerMorphism) q
  let L := (rho.action (f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint s)))).val
  let R := (rho.action (f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint (-s))))).val
  have hRL : R * L = 1 := by
    change (rho.action ((f.comp standardSL2UpperMorphism).onPoints (kPlusPoint (-s)))).val *
      (rho.action ((f.comp standardSL2UpperMorphism).onPoints (kPlusPoint s))).val = 1
    rw [← Units.val_mul, ← map_mul, ← map_mul, kPlusPoint_mul, neg_add_cancel]
    have hz : kPlusPoint (0 : k) = 1 := by
      apply (additiveGroupPointEquiv k).injective
      rfl
    simp [hz]
  apply adjoin_intertwine_mem _ _ _ a ha
  rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · refine ⟨curveCoefficient rho hr (f.comp standardSL2UpperMorphism) j,
      rankOneCurveAlgebra_first rho hr _ _ q j j.isLt, ?_⟩
    have he := curveCoefficient_intertwine rho hr
      (f.comp standardSL2UpperMorphism) (f.comp standardSL2UpperMorphism) L 1 (fun t => ?_) j
    · simpa only [one_pow, one_smul] using he
    change (rho.action ((f.comp standardSL2UpperMorphism).onPoints (kPlusPoint s))).val *
      (rho.action ((f.comp standardSL2UpperMorphism).onPoints (kPlusPoint t))).val = _
    simp only [one_mul]
    rw [← Units.val_mul, ← map_mul, ← map_mul, kPlusPoint_mul, add_comm s t,
      ← kPlusPoint_mul, map_mul, map_mul, Units.val_mul]
    rfl
  · refine ⟨L * curveCoefficient rho hr (f.comp standardSL2LowerMorphism) j * R, ?_, ?_⟩
    · obtain ⟨M, N, he⟩ := rankOne_upper_conjugation_coefficients f rho hr
      change L * curveCoefficient rho hr (f.comp standardSL2LowerMorphism) j * R ∈ A
      rw [show L * curveCoefficient rho hr (f.comp standardSL2LowerMorphism) j * R = _ from he s j]
      apply A.sum_mem
      intro a ha'
      apply A.sum_mem
      intro c hc
      split_ifs with hac
      · apply A.smul_mem
        apply A.mul_mem
        · exact A.mul_mem (rankOneCurveAlgebra_second rho hr _ _ q a (by omega))
            (rankOneTorusBinomial_shift_mem f rho hr q _ (by omega) _)
        · exact rankOneCurveAlgebra_first rho hr _ _ q c (by omega)
      · exact A.zero_mem
    · dsimp only
      rw [mul_assoc, hRL, mul_one]

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
