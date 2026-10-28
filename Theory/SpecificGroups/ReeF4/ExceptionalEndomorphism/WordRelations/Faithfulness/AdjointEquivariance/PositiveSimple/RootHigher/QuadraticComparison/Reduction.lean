module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.IntegralReduction

/-!
# Twice the integral quadratic coefficient

The double operator commutator with a simple raising operator is twice its
second adjoint divided power. For a root string with successive roots
`r`, `s = r + i`, and `k = r + 2i`, two signed integral commutator formulas
therefore give the required quadratic comparison. The root-string identity
`(p + 1)(p + 2) = 2 * choose (p + 2) 2` supplies exactly the coefficient of
the independently defined integral second column. Cancellation takes place
over the integers.

Both absent-endpoint cases are included: either the first root sum is absent,
or the first exists and the second is absent. Root-string saturation rules
out a second root without a first root. The non-opposite hypotheses also
exclude an opposite root in the intermediate step.

The final theorem here is a conditional reduction. Its signed operator
commutator premises still require proofs for the actual routed operators;
the vector-action formulas of `IntegralChevalleyBrackets` do not discharge
them. Sources: Geck's integral root-string construction, as formalized in
`IntegralGeckConstruction`, and Mathlib's `RootSystem.Chain`.
-/

public section

open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
noncomputable section

/-- The second adjoint divided power is half the double operator commutator. -/
lemma integralQuadraticOperator_two_smul (i : typeF4RootPairing_base.support)
    (r : typeF4Roots) :
    (2 : ℤ) • integralQuadraticOperator i r =
      eMatrix i * (eMatrix i * F4Chevalley.integralOperators.rootOperator r -
        F4Chevalley.integralOperators.rootOperator r * eMatrix i) -
      (eMatrix i * F4Chevalley.integralOperators.rootOperator r -
        F4Chevalley.integralOperators.rootOperator r * eMatrix i) * eMatrix i := by
  have hEE : eMatrix (P := typeF4RootPairing) i * eMatrix i =
      (2 : ℤ) • eDividedPower i 2 := by
    have h := eDividedPower_mul (P := typeF4RootPairing) i 1 1
    rw [← Nat.cast_smul_eq_nsmul ℤ] at h
    exact h
  unfold integralQuadraticOperator
  calc
    _ = (eMatrix i * eMatrix i) * F4Chevalley.integralOperators.rootOperator r -
        (eMatrix i * F4Chevalley.integralOperators.rootOperator r * eMatrix i +
          eMatrix i * F4Chevalley.integralOperators.rootOperator r * eMatrix i) +
        F4Chevalley.integralOperators.rootOperator r * (eMatrix i * eMatrix i) := by
      rw [hEE]
      simp only [smul_add, smul_sub, two_smul, add_mul, mul_add]
    _ = _ := by noncomm_ring

/-- If the second displacement is a root, its operator is the sole column summand. -/
lemma integralQuadraticColumn_of_root (i : typeF4RootPairing_base.support)
    (r k : typeF4Roots)
    (hk : typeF4RootPairing.root k =
      typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i) :
    integralQuadraticColumn i r =
      (((typeF4RootPairing.chainBotCoeff i r + 2).choose 2 : ℕ) : ℤ) •
        F4Chevalley.integralOperators.rootOperator k := by
  classical
  have he (s : typeF4Roots) :
      typeF4RootPairing.root s =
        typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i ↔ s = k := by
    rw [← hk, EmbeddingLike.apply_eq_iff_eq]
  simp only [integralQuadraticColumn, eDividedPower, Matrix.of_apply, he,
    ite_smul, zero_smul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

/-- The integral second column vanishes when its root endpoint is absent. -/
lemma integralQuadraticColumn_of_no_root (i : typeF4RootPairing_base.support)
    (r : typeF4Roots)
    (hr : typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i ∉
      Set.range typeF4RootPairing.root) :
    integralQuadraticColumn i r = 0 := by
  classical
  unfold integralQuadraticColumn
  apply Finset.sum_eq_zero
  intro s _
  have hs : typeF4RootPairing.root s ≠
      typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i := fun h => hr ⟨s, h⟩
  simp only [eDividedPower, Matrix.of_apply, if_neg hs, zero_smul]

private lemma cancel_two {A B : Matrix Coordinate Coordinate ℤ}
    (h : (2 : ℤ) • A = (2 : ℤ) • B) : A = B := by
  ext x y
  have hxy := congrFun (congrFun h x) y
  simp only [Matrix.smul_apply, smul_eq_mul] at hxy
  omega

private lemma independent (i : typeF4RootPairing_base.support) (r : typeF4Roots)
    (hpos : r ≠ (i : typeF4Roots))
    (hneg : letI := typeF4RootPairing.indexNeg; r ≠ -(i : typeF4Roots)) :
    LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root r] := by
  let := typeF4RootPairing.indexNeg
  refine RootPairing.IsReduced.linearIndependent typeF4RootPairing hpos.symm ?_
  intro h
  apply hneg
  apply typeF4RootPairing.root.injective
  rw [show typeF4RootPairing.root (-i : typeF4Roots) =
    -typeF4RootPairing.root i by
      simp only [RootPairing.indexNeg_neg, typeF4RootPairing.root_reflectionPerm,
        typeF4RootPairing.reflection_apply_self]]
  exact ((neg_eq_iff_eq_neg).2 h).symm

private lemma next_ne_neg (i : typeF4RootPairing_base.support) (r s : typeF4Roots)
    (hs : typeF4RootPairing.root s = typeF4RootPairing.root i + typeF4RootPairing.root r) :
    letI := typeF4RootPairing.indexNeg; s ≠ -(i : typeF4Roots) := by
  let := typeF4RootPairing.indexNeg
  rintro rfl
  have : (2 : ℕ).AtLeastTwo := ⟨by omega⟩
  apply typeF4RootPairing.nsmul_notMem_range_root (n := 2) (i := i)
  refine ⟨-r, ?_⟩
  rw [show typeF4RootPairing.root (-r) = -typeF4RootPairing.root r by
    simp only [RootPairing.indexNeg_neg, typeF4RootPairing.root_reflectionPerm,
      typeF4RootPairing.reflection_apply_self]]
  have hs' : -typeF4RootPairing.root i =
      typeF4RootPairing.root i + typeF4RootPairing.root r := by
    simpa only [RootPairing.indexNeg_neg, typeF4RootPairing.root_reflectionPerm,
      typeF4RootPairing.reflection_apply_self] using hs
  calc
    -typeF4RootPairing.root r =
        -(typeF4RootPairing.root i + typeF4RootPairing.root r) +
          typeF4RootPairing.root i := by abel
    _ = -(-typeF4RootPairing.root i) + typeF4RootPairing.root i := by rw [← hs']
    _ = _ := by module

/-- Signed integral simple-root commutators imply the quadratic comparison.
The two commutator families are explicit upstream proof obligations. -/
lemma integralQuadraticComparison_other_of_commutators
    (i : typeF4RootPairing_base.support)
    (hsum : ∀ r s : typeF4Roots,
      typeF4RootPairing.root s = typeF4RootPairing.root i + typeF4RootPairing.root r →
      ∃ ε : ℤ, ε ^ 2 = 1 ∧
        eMatrix i * F4Chevalley.integralOperators.rootOperator r -
          F4Chevalley.integralOperators.rootOperator r * eMatrix i =
            ε • ((typeF4RootPairing.chainBotCoeff i r + 1 : ℤ) •
              F4Chevalley.integralOperators.rootOperator s))
    (hzero : ∀ r : typeF4Roots,
      (letI := typeF4RootPairing.indexNeg; r ≠ -(i : typeF4Roots)) →
      typeF4RootPairing.root i + typeF4RootPairing.root r ∉ Set.range typeF4RootPairing.root →
        eMatrix i * F4Chevalley.integralOperators.rootOperator r -
          F4Chevalley.integralOperators.rootOperator r * eMatrix i = 0)
    (r : typeF4Roots) (hpos : r ≠ (i : typeF4Roots))
    (hneg : letI := typeF4RootPairing.indexNeg; r ≠ -(i : typeF4Roots)) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧
      integralQuadraticOperator i r = ε • integralQuadraticColumn i r := by
  classical
  let := typeF4RootPairing.indexNeg
  have hlin := independent i r hpos hneg
  have hJ := integralQuadraticOperator_two_smul i r
  by_cases hfirst : typeF4RootPairing.root i + typeF4RootPairing.root r ∈
      Set.range typeF4RootPairing.root
  · obtain ⟨s, hs⟩ := hfirst
    obtain ⟨ε, hε, hEs⟩ := hsum r s hs
    rw [hEs, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
      ← smul_sub, ← smul_sub] at hJ
    by_cases hsecond : typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i ∈
        Set.range typeF4RootPairing.root
    · obtain ⟨k, hk⟩ := hsecond
      have hsk : typeF4RootPairing.root k =
          typeF4RootPairing.root i + typeF4RootPairing.root s := by rw [hk, hs]; module
      obtain ⟨δ, hδ, hEk⟩ := hsum s k hsk
      rw [hEk] at hJ
      have hbot : typeF4RootPairing.chainBotCoeff i s =
          typeF4RootPairing.chainBotCoeff i r + 1 :=
        typeF4RootPairing.chainBotCoeff_of_add hlin (by simpa [add_comm] using hs)
      have hcoeff : (typeF4RootPairing.chainBotCoeff i r + 1 : ℤ) *
          (typeF4RootPairing.chainBotCoeff i s + 1 : ℤ) =
          2 * (((typeF4RootPairing.chainBotCoeff i r + 2).choose 2 : ℕ) : ℤ) := by
        rw [hbot]
        have hc := Nat.add_one_mul_choose_eq (typeF4RootPairing.chainBotCoeff i r + 1) 1
        have ha : typeF4RootPairing.chainBotCoeff i r + 1 + 1 =
            typeF4RootPairing.chainBotCoeff i r + 2 := by omega
        rw [ha] at hc
        simp only [Nat.choose_one_right] at hc
        exact_mod_cast (by simpa [Nat.mul_comm] using hc)
      refine ⟨ε * δ, by rw [mul_pow, hε, hδ, one_mul], ?_⟩
      apply cancel_two
      rw [hJ, integralQuadraticColumn_of_root i r k hk]
      simp only [smul_smul]
      congr 1
      calc
        _ = 2 * (ε * δ * (((typeF4RootPairing.chainBotCoeff i r + 2).choose 2 : ℕ) : ℤ)) := by
          linear_combination ε * δ * hcoeff
        _ = _ := by ring
    · have hsk : typeF4RootPairing.root i + typeF4RootPairing.root s ∉
          Set.range typeF4RootPairing.root := by
        rintro ⟨k, hk⟩
        apply hsecond
        exact ⟨k, by rw [hk, hs]; module⟩
      rw [hzero s (next_ne_neg i r s hs) hsk, smul_zero, smul_zero] at hJ
      refine ⟨1, by norm_num, ?_⟩
      rw [integralQuadraticColumn_of_no_root i r hsecond, smul_zero]
      exact cancel_two (by simpa only [smul_zero] using hJ)
  · have hsecond : typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i ∉
        Set.range typeF4RootPairing.root := by
      intro h
      apply hfirst
      rw [show typeF4RootPairing.root i + typeF4RootPairing.root r =
        typeF4RootPairing.root r + (1 : ℕ) • typeF4RootPairing.root i by simp [add_comm]]
      rw [typeF4RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin] at h ⊢
      omega
    rw [hzero r hneg hfirst, mul_zero, zero_mul, sub_zero] at hJ
    refine ⟨1, by norm_num, ?_⟩
    rw [integralQuadraticColumn_of_no_root i r hsecond, smul_zero]
    exact cancel_two (by simpa only [smul_zero] using hJ)
end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
