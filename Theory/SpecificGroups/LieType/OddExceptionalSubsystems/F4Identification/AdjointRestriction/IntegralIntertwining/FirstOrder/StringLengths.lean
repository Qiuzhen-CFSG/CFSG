module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.IntegralIntertwining.FirstOrder.Reduction
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.IntegralIntertwining.FirstOrder.StringLengths.Certificate

/-!
# Bottom root-string lengths under the E6–F4 folding

For each numbered F4 node and each E6 root projecting to an F4 root, the
bottom string length in F4 equals the sum over the E6 node fibre. This uses
the literal coordinate projection and the actual root pairings.

In a reduced crystallographic root system a bottom string has length at
most three. Its length is therefore determined by the first three downward
root-membership tests; if the first step is absent, the length is zero,
including for dependent roots. We identify the concrete real root sets with
rational coordinate predicates and apply two kernel-checked certificates.
No root-image or simple-fibre theorem is needed for this scalar identity.

The two consumer theorems discharge the string-length premise of the integral
first-order reduction. They retain root-image and simple-fibre hypotheses,
whose unconditional construction belongs to the separate geometry task.
Sources: GLS3 §§2.2–2.6; the F4 inclusions in Aschbacher–Smith A.2.17,
printed p.39 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem Matrix
local instance : Fintype typeF4Roots := Fintype.ofFinite _
namespace TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction.StringLengths

open scoped Classical in
private lemma chain_formula {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsCrystallographic] [P.IsReduced] (i j : ι) :
    P.chainBotCoeff i j =
      if P.root j - P.root i ∈ Set.range P.root then
        if P.root j - 2 • P.root i ∈ Set.range P.root then
          if P.root j - 3 • P.root i ∈ Set.range P.root then 3 else 2
        else 1
      else 0 := by
  classical
  by_cases h : P.root j - P.root i ∈ Set.range P.root
  · rw [if_pos h]
    have hl : LinearIndependent ℝ ![P.root i, P.root j] :=
      P.linearIndependent_of_sub_mem_range_root' (by
        rw [← P.neg_mem_range_root_iff, neg_sub]
        exact h)
    have h1 : 1 ≤ P.chainBotCoeff i j :=
      (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hl).mp (by simpa using h)
    have h2 := P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff (n := 2) hl
    have h3 := P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff (n := 3) hl
    have hb := P.chainBotCoeff_add_chainTopCoeff_le_three (i := i) (j := j)
    rw [h2, h3]
    split_ifs <;> omega
  · rw [if_neg h]
    exact P.chainBotCoeff_eq_zero_iff.mpr (Or.inr h)

private def real {n : ℕ} (x : Fin n → ℚ) : Vec n := fun k => x k

private lemma real_injective {n : ℕ} : Function.Injective (@real n) := by
  intro x y h
  funext k
  exact Rat.cast_injective (congrFun h k)

private lemma real_unit {n : ℕ} (i : Fin n) : real (unit i) = basisVector i := by
  ext k
  by_cases h : k = i <;> simp [real, unit, basisVector, h]

private lemma real_neg {n : ℕ} (x : Fin n → ℚ) : real (-x) = -real x := by
  ext k
  simp [real]

private lemma real_pair {n : ℕ} (i j : Fin n) (s t : Bool) :
    real (pair i j s t) = (sign s : ℝ) • basisVector i + (sign t : ℝ) • basisVector j := by
  ext k
  simp only [real, pair, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Rat.cast_add, Rat.cast_mul]
  have hu (l : Fin n) : (unit l k : ℝ) = basisVector l k := congrFun (real_unit l) k
  rw [hu, hu]

private lemma real_half {n : ℕ} (ε : Fin n → Bool) : real (half ε) = halfSignVector ε := by
  ext k
  cases h : ε k <;> norm_num [real, half, sign, halfSignVector, h]

private lemma isPair_iff {n : ℕ} (x : Fin n → ℚ) :
    isPair x ↔ ∃ i j : Fin n, i ≠ j ∧ ∃ s t : Bool, x = pair i j s t := by
  constructor
  · rintro ⟨hx, hc⟩
    obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp hc
    have hsupport (k : Fin n) : x k ≠ 0 ↔ k = i ∨ k = j := by
      have := Finset.ext_iff.mp hs k
      simpa using this
    have hi : x i = -1 ∨ x i = 1 := by
      rcases hx i with h | h | h
      · exact Or.inl h
      · exact False.elim ((hsupport i).mpr (Or.inl rfl) h)
      · exact Or.inr h
    have hj : x j = -1 ∨ x j = 1 := by
      rcases hx j with h | h | h
      · exact Or.inl h
      · exact False.elim ((hsupport j).mpr (Or.inr rfl) h)
      · exact Or.inr h
    have build (s t : Bool) (hi : x i = sign s) (hj : x j = sign t) :
        x = pair i j s t := by
      funext k
      by_cases hki : k = i
      · subst k
        simp [pair, unit, hij, hi]
      · by_cases hkj : k = j
        · subst k
          simp [pair, unit, hij.symm, hj]
        · have hk : x k = 0 := by simpa [hki, hkj] using (hsupport k).not
          simp [pair, unit, hki, hkj, hk]
    refine ⟨i, j, hij, ?_⟩
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact ⟨false, false, build false false hi hj⟩
    · exact ⟨false, true, build false true hi hj⟩
    · exact ⟨true, false, build true false hi hj⟩
    · exact ⟨true, true, build true true hi hj⟩
  · rintro ⟨i, j, hij, s, t, rfl⟩
    constructor
    · intro k
      by_cases hki : k = i
      · subst k
        cases s <;> simp [pair, unit, hij, sign]
      · by_cases hkj : k = j
        · subst k
          cases t <;> simp [pair, unit, hij.symm, sign]
        · simp [pair, unit, hki, hkj]
    · have hs : Finset.univ.filter (fun k => pair i j s t k ≠ 0) = {i,j} := by
        ext k
        by_cases hki : k = i
        · subst k
          cases s <;> simp [pair, unit, hij, sign]
        · by_cases hkj : k = j
          · subst k
            cases t <;> simp [pair, unit, hij.symm, sign]
          · simp [pair, unit, hki, hkj]
      rw [hs, Finset.card_pair hij]

private lemma real_mem_pair {n : ℕ} (x : Fin n → ℚ) :
    real x ∈ pairRoots n ↔ isPair x := by
  rw [isPair_iff]
  constructor
  · rintro ⟨i, j, hij, s, t, hs, ht, he⟩
    have hs' : s = -1 ∨ s = 1 := by simpa using hs
    have ht' : t = -1 ∨ t = 1 := by simpa using ht
    refine ⟨i, j, hij, ?_⟩
    rcases hs' with rfl | rfl <;> rcases ht' with rfl | rfl
    · exact ⟨false, false, real_injective (by simpa [real_pair, sign] using he)⟩
    · exact ⟨false, true, real_injective (by simpa [real_pair, sign] using he)⟩
    · exact ⟨true, false, real_injective (by simpa [real_pair, sign] using he)⟩
    · exact ⟨true, true, real_injective (by simpa [real_pair, sign] using he)⟩
  · rintro ⟨i, j, hij, s, t, rfl⟩
    refine ⟨i, j, hij, (sign s : ℝ), (sign t : ℝ), ?_, ?_, real_pair i j s t⟩
    · cases s <;> simp [sign]
    · cases t <;> simp [sign]

private lemma isHalf_iff {n : ℕ} (x : Fin n → ℚ) :
    isHalf x ↔ ∃ ε : Fin n → Bool, x = half ε := by
  constructor
  · intro h
    refine ⟨fun k => decide (x k = 1/2), ?_⟩
    funext k
    rcases h k with hk | hk <;> norm_num [half, sign, hk]
  · rintro ⟨ε, rfl⟩ k
    cases h : ε k <;> norm_num [half, sign, h]

private lemma real_mem_half {n : ℕ} (x : Fin n → ℚ) :
    real x ∈ Set.range halfSignVector ↔ isHalf x := by
  rw [isHalf_iff]
  constructor
  · rintro ⟨ε, he⟩
    exact ⟨ε, real_injective (he.symm.trans (real_half ε).symm)⟩
  · rintro ⟨ε, rfl⟩
    exact ⟨ε, (real_half ε).symm⟩



private lemma half_negative {n : ℕ} (ε : Fin n → Bool) :
    Finset.univ.filter (fun k => half ε k < 0) = Finset.univ.filter (fun k => !(ε k)) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases h : ε k <;> norm_num [half, sign, h]

private lemma real_mem_evenHalf (x : Fin 8 → ℚ) :
    (∃ ε : Fin 8 → Bool, evenNegative ε ∧ real x = halfSignVector ε) ↔
      isHalf x ∧ (Finset.univ.filter (fun k => x k < 0)).card % 2 = 0 := by
  constructor
  · rintro ⟨ε, hε, he⟩
    have hx : x = half ε := real_injective (he.trans (real_half ε).symm)
    subst x
    refine ⟨(isHalf_iff _).mpr ⟨ε, rfl⟩, ?_⟩
    rw [half_negative]
    exact Nat.even_iff.mp hε
  · rintro ⟨hx, he⟩
    obtain ⟨ε, rfl⟩ := (isHalf_iff _).mp hx
    rw [half_negative] at he
    exact ⟨ε, Nat.even_iff.mpr he, real_half ε⟩

private lemma real_mem_F4 (x : Fin 4 → ℚ) : real x ∈ typeF4Roots ↔ F4 x := by
  change ((real x ∈ pairRoots 4) ∨ (real x ∈ signedUnitRoots 4)) ∨
    real x ∈ Set.range halfSignVector ↔ _
  rw [real_mem_pair, real_mem_half]
  simp only [signedUnitRoots, Set.mem_ofPred_eq, ← real_unit, ← real_neg,
    real_injective.eq_iff]
  exact or_assoc

private lemma real_mem_E6 (x : Fin 8 → ℚ) : real x ∈ typeE6Roots ↔ E6 x := by
  have h01 : dot (real x) (basisVector 0 + basisVector 1) = ((x 0 + x 1 : ℚ) : ℝ) := by
    simp [dot, mul_add, Finset.sum_add_distrib, basisVector, Pi.single_apply, real]
  have h12 : dot (real x) (basisVector 1 - basisVector 2) = ((x 1 - x 2 : ℚ) : ℝ) := by
    simp [dot, mul_sub, Finset.sum_sub_distrib, basisVector, Pi.single_apply, real]
  change (((real x ∈ pairRoots 8) ∨
    (∃ ε : Fin 8 → Bool, evenNegative ε ∧ real x = halfSignVector ε)) ∧
    dot (real x) (basisVector 0 + basisVector 1) = 0) ∧
    dot (real x) (basisVector 1 - basisVector 2) = 0 ↔ _
  rw [real_mem_pair, real_mem_evenHalf, h01, h12, Rat.cast_eq_zero, Rat.cast_eq_zero]
  exact and_assoc

private lemma real_simple6 (i : Fin 6) : real (simple6 i) = typeE6SimpleRoot i := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [real, simple6, typeE6SimpleRoot, typeE8SimpleRoot]

private lemma real_simple4 (i : Fin 4) : real (simple4 i) = typeF4SimpleRoot i := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [real, simple4, typeF4SimpleRoot]

private lemma real_project (x : Fin 8 → ℚ) : real (project x) = rootProjection (real x) := by
  ext k
  fin_cases k <;> simp [real, project, rootProjection]

private lemma exists_real_E6 (r : typeE6Roots) : ∃ x : Fin 8 → ℚ, real x = r.val := by
  rcases r.property.1.1 with hp | ⟨ε, _, he⟩
  · rcases hp with ⟨i, j, _, s, t, hs, ht, he⟩
    have hs' : s = -1 ∨ s = 1 := by simpa using hs
    have ht' : t = -1 ∨ t = 1 := by simpa using ht
    rcases hs' with rfl | rfl <;> rcases ht' with rfl | rfl
    · refine ⟨pair i j false false, ?_⟩
      rw [real_pair]
      simpa [sign] using he.symm
    · refine ⟨pair i j false true, ?_⟩
      rw [real_pair]
      simpa [sign] using he.symm
    · refine ⟨pair i j true false, ?_⟩
      rw [real_pair]
      simpa [sign] using he.symm
    · refine ⟨pair i j true true, ?_⟩
      rw [real_pair]
      simpa [sign] using he.symm
  · exact ⟨half ε, (real_half ε).trans he.symm⟩



private lemma real_sub_nsmul {n : ℕ} (x y : Fin n → ℚ) (k : ℕ) :
    real (x - k • y) = real x - k • real y := by
  ext j
  simp [real]

private lemma range_E6 (v : typeE6RootSpan) :
    v ∈ Set.range typeE6RootPairing.root ↔ v.val ∈ typeE6Roots := by
  constructor
  · rintro ⟨r, rfl⟩
    exact r.property
  · intro h
    exact ⟨⟨v.val, h⟩, Subtype.ext rfl⟩

private lemma range_F4 (v : Vec 4) :
    v ∈ Set.range typeF4RootPairing.root ↔ v ∈ typeF4Roots := by
  constructor
  · rintro ⟨r, rfl⟩
    exact r.property
  · intro h
    exact ⟨⟨v, h⟩, rfl⟩

private lemma bottom_E6 (j : Fin 6) (r : typeE6Roots)
    (x : Fin 8 → ℚ) (hx : real x = r.val) :
    typeE6RootPairing.chainBotCoeff (simpleIndex j) r = bottom E6 (simple6 j) x := by
  have hm (k : ℕ) :
      typeE6RootPairing.root r - k • typeE6RootPairing.root (simpleIndex j) ∈
        Set.range typeE6RootPairing.root ↔ E6 (x - k • simple6 j) := by
    rw [range_E6]
    change r.val - k • typeE6SimpleRoot j ∈ typeE6Roots ↔ _
    rw [← hx, ← real_simple6, ← real_sub_nsmul, real_mem_E6]
  have hm1 := hm 1
  simp only [one_smul] at hm1
  rw [chain_formula]
  simp only [hm1, hm 2, hm 3, bottom]

private lemma bottom_F4 (i : Fin 4) (a : typeF4Roots)
    (x : Fin 4 → ℚ) (hx : real x = a.val) :
    typeF4RootPairing.chainBotCoeff (sourceIndex i) a = bottom F4 (simple4 i) x := by
  have hm (k : ℕ) :
      typeF4RootPairing.root a - k • typeF4RootPairing.root (sourceIndex i) ∈
        Set.range typeF4RootPairing.root ↔ F4 (x - k • simple4 i) := by
    rw [range_F4]
    change a.val - k • typeF4SimpleRoot i ∈ typeF4Roots ↔ _
    rw [← hx, ← real_simple4, ← real_sub_nsmul, real_mem_F4]
  have hm1 := hm 1
  simp only [one_smul] at hm1
  rw [chain_formula]
  simp only [hm1, hm 2, hm 3, bottom]


private theorem rational_check (x : Fin 8 → ℚ) (i : Fin 4) (hx : E6 x) :
    check x i := by
  rcases hx with ⟨hp | ⟨hh, he⟩, h0, h1⟩
  · obtain ⟨a, b, hab, s, t, rfl⟩ := (isPair_iff _).mp hp
    exact pair_check a b s t i hab h0 h1
  · obtain ⟨ε, rfl⟩ := (isHalf_iff _).mp hh
    rw [half_negative] at he
    exact half_check ε i he h0 h1

end TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction.StringLengths

namespace TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction
open StringLengths

/-- Bottom string lengths add over a node fibre under the literal E6–F4
projection. The only extra input is the equality with the specified F4 root. -/
theorem chainBotCoeff_projection (i : Fin 4) (r : typeE6Roots) (a : typeF4Roots)
    (h : rootProjection r.val = a.val) :
    (∑ j : Fin 6, if node j = i then
      typeE6RootPairing.chainBotCoeff (simpleIndex j) r else 0) =
        typeF4RootPairing.chainBotCoeff (sourceIndex i) a := by
  obtain ⟨x, hx⟩ := exists_real_E6 r
  have hxE6 : E6 x := real_mem_E6 x |>.mp (hx.symm ▸ r.property)
  have ha : real (project x) = a.val := by
    rw [real_project, hx, h]
  rw [bottom_F4 i a (project x) ha]
  simp_rw [bottom_E6 _ r x hx]
  exact rational_check x i hxE6

section Consumer
variable
    (hroot : ∀ r : typeE6Roots, rootProjection r.val ∈ typeF4Roots)
    (hsimple : ∀ (i : Fin 4) (r : typeE6Roots),
      rootProjection r.val = typeF4SimpleRoot i →
        ∃ j : Fin 6, node j = i ∧ r = typeE6SimpleRootIndex j)

include hroot hsimple

/-- The string-length premise of the integral first-order comparison is
now discharged. Root-image and simple-fibre geometry remain explicit. -/
theorem firstOrder_intertwines_of_root_fibres (s : Bool) (i : Fin 4) :
    foldedOperator s i * latticeMatrix = latticeMatrix * sourceOperator s i :=
  firstOrder_intertwines_of_root_geometry hroot hsimple chainBotCoeff_projection s i

/-- Apply the coefficient identity to the literal integral column map,
retaining the independent root-image and simple-fibre inputs. -/
theorem firstOrder_mulVec_of_root_fibres (s : Bool) (i : Fin 4) (x : SourceIndex → ℤ) :
    foldedOperator s i *ᵥ linearMap ℤ x =
      linearMap ℤ (sourceOperator s i *ᵥ x) :=
  firstOrder_mulVec_of_root_geometry hroot hsimple chainBotCoeff_projection s i x

end Consumer
end TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction
