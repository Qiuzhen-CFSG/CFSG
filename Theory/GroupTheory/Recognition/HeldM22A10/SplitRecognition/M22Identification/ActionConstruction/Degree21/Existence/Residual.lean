module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.IntegralExpansion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints


/-!
# Extracting the degree-21 constituent from the negative Gram entry

The scalar product of the fourth and fifth actual exceptional inductions is
minus one. Their simultaneous expansion in genuine irreducibles therefore has
a constituent with opposite multiplicities. If no constituent of the first
three inductions has this property, its first three coordinates vanish. Unit
multiplicities, actual degree divisibility, and the Sylow restriction congruence
then force degree 21 and all five special values. The two finite divisor checks
use complementary factors up to the square root, avoiding a scan of the group
order. No class function is introduced by its numerical values.

`FirstThreeCompatible` isolates the remaining calculation for the first three
inductions. Its proof is required before using this construction to establish
source existence under the original local hypotheses.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 6–7, pp.12–16,
DOI 10.1016/0021-8693(68)90002-1.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
open LocalModelDichotomy CharacterOrder CharacterOrder.OrderExhaustion

private def smallDivisors (g : ℕ) : List ℕ :=
  ((List.range (g.sqrt + 1)).filter (fun d => 0 < d ∧ d ∣ g)).flatMap
    (fun d => [d, g / d])

private theorem mem_smallDivisors {g n : ℕ} (hg : 0 < g) (hn : n ∣ g) :
    n ∈ smallDivisors g := by
  have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hn hg
  obtain ⟨m, hm⟩ := hn
  have hm0 : 0 < m := by nlinarith
  rcases Nat.le_sqrt_of_eq_mul hm with h | h
  · apply List.mem_flatMap.mpr
    refine ⟨n, ?_, by simp⟩
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨by omega, hn0, ⟨m, hm⟩⟩
  · apply List.mem_flatMap.mpr
    refine ⟨m, ?_, ?_⟩
    · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨by omega, hm0, ⟨n, hm.trans (Nat.mul_comm _ _)⟩⟩
    · simp [hm, Nat.mul_div_cancel _ hm0]

set_option maxRecDepth 10000 in
private theorem positive_residue : ∀ n ∈ smallDivisors 443520,
    (128 : ℤ) ∣ (n : ℤ) + 235 → n = 21 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem negative_residue : ∀ n ∈ smallDivisors 443520,
    ¬ (128 : ℤ) ∣ (n : ℤ) - 235 := by decide +kernel

/-- The first three exceptional inductions have no constituent whose fourth
and fifth multiplicities have opposite signs. This is the remaining signed
character calculation, separate from the residual Gram argument. -/
@[expose] public def FirstThreeCompatible {G : Type*} [Group G] [Finite G]
    {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) : Prop :=
  ∀ (χ : ClassFunction G) (hχ : IsIrreducibleCharacter χ),
    (∃ i : Fin 3, multiplicities I hχ i.castSucc.castSucc ≠ 0) →
      0 ≤ multiplicities I hχ 3 * multiplicities I hχ 4

/-- The negative Gram entry produces an actual irreducible of degree 21.
The arithmetic identifies its signs; it does not posit a character row. -/
public theorem exists_special_values_of_compatible {G : Type*} [Group G] [Finite G]
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hcard : Nat.card G = 443520)
    (hu : HasUnitMultiplicities I.induced) (hcompat : FirstThreeCompatible I) :
    ∃ (χ : ClassFunction G) (hχ : IsIrreducibleCharacter χ),
      hχ.degree = 21 ∧
      ∀ r, χ (CaseII.into D k (specialRepresentative r)) =
        (![5, -1, -1, 1, 1] r : ℂ) := by
  classical
  obtain ⟨E⟩ := exists_integralExpansion I
  have hg : ∑ j, E.coefficient 3 j * E.coefficient 4 j = -1 := E.gram 3 4
  obtain ⟨j, hj⟩ : ∃ j, E.coefficient 3 j * E.coefficient 4 j < 0 := by
    by_contra h
    have hh : ∀ j, 0 ≤ E.coefficient 3 j * E.coefficient 4 j := by simpa using h
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hh j)
    omega
  let χ := E.character j
  let hχ := E.irreducible j
  let c := multiplicities I hχ
  have hc (i : Fin 5) : c i = E.coefficient i j := by
    have h := (multiplicities_scalarProduct I hχ i).symm.trans (E.multiplicity i j)
    exact_mod_cast h
  have hneg : c 3 * c 4 < 0 := by simpa only [hc] using hj
  have hzero (i : Fin 3) : c i.castSucc.castSucc = 0 := by
    by_contra h
    have := hcompat χ hχ ⟨i, h⟩
    change 0 ≤ c 3 * c 4 at this
    omega
  have h0 : c 0 = 0 := hzero 0
  have h1 : c 1 = 0 := hzero 1
  have h2 : c 2 = 0 := hzero 2
  have h3 := multiplicities_unit I hu hχ 3
  have h4 := multiplicities_unit I hu hχ 4
  change c 3 = 0 ∨ c 3 = 1 ∨ c 3 = -1 at h3
  change c 4 = 0 ∨ c 4 = 1 ∨ c 4 = -1 at h4
  have hsign : (c 3 = 1 ∧ c 4 = -1) ∨ (c 3 = -1 ∧ c 4 = 1) := by
    rcases h3 with h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4 <;>
      simp_all
  have hd : hχ.degree ∈ smallDivisors 443520 := by
    apply mem_smallDivisors (by norm_num)
    simpa only [hcard] using hχ.degree_dvd_card
  have hcong := degree_congruence_mod128 D k L I hχ c (multiplicities_values I hχ)
  rw [h0, h1, h2] at hcong
  obtain ⟨hs3, hs4⟩ : c 3 = 1 ∧ c 4 = -1 := by
    rcases hsign with h | ⟨hs3, hs4⟩
    · exact h
    · rw [hs3, hs4] at hcong
      have hh : (128 : ℤ) ∣ (hχ.degree : ℤ) - 235 := by convert hcong using 1; ring
      exact False.elim (negative_residue _ hd hh)
  have hdegree : hχ.degree = 21 := by
    apply positive_residue _ hd
    rw [hs3, hs4] at hcong
    convert hcong using 1
    ring
  refine ⟨χ, hχ, hdegree, ?_⟩
  intro r
  change E.character j _ = _
  rw [multiplicities_values I hχ]
  change (columnValue c r : ℂ) = _
  fin_cases r <;> norm_num [columnValue, h0, h1, h2, hs3, hs4]
end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
