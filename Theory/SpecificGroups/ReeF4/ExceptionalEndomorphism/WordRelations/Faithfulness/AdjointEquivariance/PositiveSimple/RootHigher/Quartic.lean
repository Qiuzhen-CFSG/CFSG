module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.Coefficients
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.RootColumns

/-!
# The quartic positive-simple root coefficient

A second divided-power column is supported at a root displaced by twice the
simple root. Two endpoints of such displacements are neither opposite nor
have a root as their sum. This follows from the F4 squared-length bounds:
each endpoint has scalar product at least `|α|² - 1/4` with `α`, which is too
large for their sum to be a root.

The actual routed root-column formula therefore shows that an endpoint root
operator annihilates the entire second divided power. Applying this to the
second column image proves the quartic coefficient, without any equivariance
hypothesis. The matrix formulas come from `IntegralGeckConstruction` and
`IntegralChevalleyBrackets`, and the length bounds from `F4RootPairing`.
-/

public section

open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
noncomputable section
private lemma norm_bounds (r : typeF4Roots) :
    1 ≤ dot r.val r.val ∧ dot r.val r.val ≤ 2 := by
  by_cases hr : IsLongRoot r
  · rw [isLongRoot_norm r hr]
    norm_num
  · rw [isShortRoot_norm r hr]
    norm_num

private lemma top_dot (i r k : typeF4Roots)
    (h : typeF4RootPairing.root k = typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i) :
    dot i.val i.val - 1 / 4 ≤ dot k.val i.val := by
  have hr : r.val = k.val - (2 : ℝ) • i.val := by
    have h' : k.val = r.val + (2 : ℝ) • i.val := by
      simpa only [typeF4RootPairing_root, ofNat_smul_eq_nsmul] using h
    rw [h']
    module
  have he : dot r.val r.val = dot k.val k.val - 4 * dot k.val i.val + 4 * dot i.val i.val := by
    rw [hr]
    change (k.val - (2 : ℝ) • i.val) ⬝ᵥ (k.val - (2 : ℝ) • i.val) = _
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, dotProduct_comm i.val k.val]
    change dot _ _ - 2 * dot _ _ - 2 * (dot _ _ - 2 * dot _ _) = _
    ring
  linarith [(norm_bounds k).1, (norm_bounds r).2]

private lemma tops_not_add (i r s k l : typeF4Roots)
    (hk : typeF4RootPairing.root k = typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i)
    (hl : typeF4RootPairing.root l = typeF4RootPairing.root s + (2 : ℕ) • typeF4RootPairing.root i) :
    typeF4RootPairing.root k + typeF4RootPairing.root l ∉ Set.range typeF4RootPairing.root := by
  rintro ⟨q, hq⟩
  have hqi : dot q.val i.val = dot k.val i.val + dot l.val i.val := by
    change q.val = k.val + l.val at hq
    rw [hq]
    exact add_dotProduct _ _ _
  have hp : 0 ≤ dot (q.val - (3 / 2 : ℝ) • i.val) (q.val - (3 / 2 : ℝ) • i.val) :=
    Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  change 0 ≤ (q.val - (3 / 2 : ℝ) • i.val) ⬝ᵥ (q.val - (3 / 2 : ℝ) • i.val) at hp
  simp only [sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, dotProduct_comm i.val q.val] at hp
  change 0 ≤ dot q.val q.val - 3 / 2 * dot q.val i.val -
    3 / 2 * (dot q.val i.val - 3 / 2 * dot i.val i.val) at hp
  linarith [top_dot i r k hk, top_dot i s l hl, (norm_bounds i).1, (norm_bounds q).2]

private lemma tops_not_opposite (i r s k l : typeF4Roots)
    (hk : typeF4RootPairing.root k = typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i)
    (hl : typeF4RootPairing.root l = typeF4RootPairing.root s + (2 : ℕ) • typeF4RootPairing.root i) :
    letI := typeF4RootPairing.indexNeg; l ≠ -k := by
  let := typeF4RootPairing.indexNeg
  change l ≠ -k
  intro h
  have he : dot l.val i.val = -dot k.val i.val := by
    have hr : l.val = -k.val := by
      have := congrArg typeF4RootPairing.root h
      change typeF4RootPairing.root l = -typeF4RootPairing.root k
      simpa only [RootPairing.indexNeg_neg, typeF4RootPairing.root_reflectionPerm,
        typeF4RootPairing.reflection_apply_self] using this
    rw [hr]
    exact neg_dotProduct _ _
  linarith [top_dot i r k hk, top_dot i s l hl, (norm_bounds i).1]
/-- A second divided-power column with a root endpoint is a single root vector. -/
lemma dividedPower_two_rootColumn (m : ℕ) (i : typeF4RootPairing_base.support) (r k : typeF4Roots)
    (hk : typeF4RootPairing.root k = typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i) :
    (fun x => dividedPower m i 2 x (Sum.inr r)) =
      (((typeF4RootPairing.chainBotCoeff i r + 2).choose 2 : ℕ) : CoefficientField m) •
        Pi.single (Sum.inr k : Coordinate) 1 := by
  classical
  have he (j : typeF4Roots) :
      typeF4RootPairing.root j = typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i ↔ j = k := by
    rw [← hk, EmbeddingLike.apply_eq_iff_eq]
  ext (j | j)
  · simp [dividedPower, eDividedPower]
  · simp only [dividedPower, eDividedPower, Matrix.map_apply, Matrix.of_apply]
    simp only [Nat.zero_add, Nat.add_zero, he j]
    by_cases hj : j = k
    · subst j; simp
    · simp [hj]

/-- The second divided-power column vanishes if its endpoint is absent. -/
lemma dividedPower_two_rootColumn_zero (m : ℕ) (i : typeF4RootPairing_base.support) (r : typeF4Roots)
    (hr : typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i ∉ Set.range typeF4RootPairing.root) :
    (fun x => dividedPower m i 2 x (Sum.inr r)) = 0 := by
  classical
  have he (j : typeF4Roots) :
      typeF4RootPairing.root j ≠ typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i :=
    fun h => hr ⟨j, h⟩
  ext (j | j)
  · simp [dividedPower, eDividedPower]
  · simp only [dividedPower, eDividedPower, Matrix.map_apply, Matrix.of_apply]
    simp only [if_neg (he j), map_zero, Pi.zero_apply]

/-- A second divided power vanishes on Cartan coordinates. -/
lemma dividedPower_two_cartanColumn (m : ℕ) (i j : typeF4RootPairing_base.support) :
    (fun x => dividedPower m i 2 x (Sum.inl j)) = 0 := by
  ext (k | k) <;> simp [dividedPower, eDividedPower]

/-- An endpoint root operator annihilates the entire second divided power. -/
lemma top_rootOperator_mul_dividedPower_two (m : ℕ) (i : typeF4RootPairing_base.support) (r k : typeF4Roots)
    (hk : typeF4RootPairing.root k = typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i) :
    coordinateOperator m (Sum.inr k) * dividedPower m i 2 = 0 := by
  classical
  have hcol (j : Coordinate) :
      (coordinateOperator m (Sum.inr k) * dividedPower m i 2) *ᵥ Pi.single j 1 = 0 := by
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rcases j with j | s
    · change coordinateOperator m (Sum.inr k) *ᵥ (fun x => dividedPower m i 2 x (Sum.inl j)) = 0
      rw [dividedPower_two_cartanColumn, Matrix.mulVec_zero]
    · change coordinateOperator m (Sum.inr k) *ᵥ (fun x => dividedPower m i 2 x (Sum.inr s)) = 0
      by_cases hs : typeF4RootPairing.root s + (2 : ℕ) • typeF4RootPairing.root i ∈ Set.range typeF4RootPairing.root
      · obtain ⟨l, hl⟩ := hs
        rw [dividedPower_two_rootColumn m i s l hl, Matrix.mulVec_smul]
        have hkl := ShortOperators.rootOperator_rootColumn_zero (K := CoefficientField m) k l
          (tops_not_opposite i r s k l hk hl) (tops_not_add i r s k l hk hl)
        change coordinateOperator m (Sum.inr k) *ᵥ Pi.single (Sum.inr l) 1 = 0 at hkl
        rw [hkl, smul_zero]
      · rw [dividedPower_two_rootColumn_zero m i s hs, Matrix.mulVec_zero]
  ext x y
  have h := congrFun (hcol y) x
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply, Matrix.zero_apply] using h

/-- The quartic coefficient vanishes for every root, independently of degree one. -/
lemma positive_root_coefficient_four (m : ℕ) (i : typeF4RootPairing_base.support) (r : typeF4Roots) :
    CoefficientIdentity m i (Sum.inr r) 4 := by
  classical
  have hv : columnImage m i 2 (Sum.inr r) * dividedPower m i 2 = 0 := by
    by_cases hr : typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i ∈ Set.range typeF4RootPairing.root
    · obtain ⟨k, hk⟩ := hr
      rw [columnImage, dividedPower_two_rootColumn m i r k hk, map_smul, adjointMap_single,
        Matrix.smul_mul, top_rootOperator_mul_dividedPower_two m i r k hk, smul_zero]
    · rw [columnImage, dividedPower_two_rootColumn_zero m i r hr, map_zero, zero_mul]
  simpa only [CoefficientIdentity, curveProductCoefficient, columnImage_three_eq_zero,
    dividedPower_three_eq_zero, dividedPower_eq_zero m i 4 (by omega),
    zero_mul, mul_zero, zero_add, add_zero] using hv
end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
