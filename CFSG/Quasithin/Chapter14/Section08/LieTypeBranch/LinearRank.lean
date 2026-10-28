module

public import Theory.SpecificGroups.ProjectiveLinear.RootNormalizerTorus
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.RankOneExclusion
public import CFSG.Quasithin.ClassificationModels

/-!
# The complete linear-family branch of Theorem D

A genuine PSL_d(2^n) model with n > 1 and d ≥ 4 has an elementary odd-prime
rank-three subgroup in an actual root two-local normalizer. Quasithinness
therefore gives d ≤ 3. The nonempty faithful local family excludes d = 2
by the proved rank-one Borel theorem, leaving precisely PSL₃(2^n).

Every transport uses the supplied finite field and actual multiplicative
equivalence. The source K-class can remain arbitrary for this subcase.
Source: Aschbacher–Smith A.2.18 (printed p.40) and Theorem D/14.8.2(1)
(printed pp.1078–1079). The other classical and exceptional families remain
separate obligations of the full Lie-type branch.
-/

public section

namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The direct root-normalizer obstruction bounds every genuine binary PSL
model of a quasithin group, retaining the strict field-exponent hypothesis. -/
theorem psl_degree_le_three_of_quasithin (hG : IsQuasithin G)
    {d n : ℕ} (hn : 1 < n) (hmodel : ClassicalGroup.IsPSL G d (2 ^ n)) : d ≤ 3 := by
  by_contra hlarge
  have hd : 4 ≤ d := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := by
    apply ringChar.of_eq
    apply FiniteField.even_card_iff_char_two.mpr
    rw [← Nat.card_eq_fintype_card, hcard]
    exact Nat.mod_eq_zero_of_dvd
      (even_iff_two_dvd.mp (even_two.pow_of_ne_zero (by omega)))
  have hq : 2 < Nat.card F := by
    rw [hcard]
    exact (by norm_num : (2 : ℕ) = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
  exact Theory.SpecificGroups.ProjectiveLinearRoot.not_quasithin k hq
    (Theory.GroupTheory.isQuasithin_of_equiv e hG)

/-- The actual nonempty faithful family removes the remaining rank-one linear case. -/
theorem psl_degree_eq_three_of_faithfulLocalComponents_nonempty
    {K : GroupClass.{u}} (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {d n : ℕ} (hd : 2 ≤ d) (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL G d (2 ^ n)) : d = 3 := by
  have hle := psl_degree_le_three_of_quasithin h.quasithin hn hmodel
  by_contra hne3
  have hd2 : d = 2 := by omega
  subst d
  exact hne.ne_empty (localFamilies_eq_empty_of_psl2 h T (by omega) hmodel).2

/-- The linear branch supplies the exact rank-two model at the original field exponent. -/
theorem rankTwoModel_of_psl
    {K : GroupClass.{u}} (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {d n : ℕ} (hd : 2 ≤ d) (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL G d (2 ^ n)) :
    ClassificationModels.IsRankTwoModel G n := by
  have hd3 := psl_degree_eq_three_of_faithfulLocalComponents_nonempty h T hne hd hn hmodel
  subst d
  exact .linear (by omega) hmodel

/-- Complete Theorem D output for every simple-range linear model over q > 2. -/
theorem theoremDModel_of_psl
    {K : GroupClass.{u}} (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {d n : ℕ} (hd : 2 ≤ d) (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL G d (2 ^ n)) :
    ClassificationModels.IsTheoremDModel G :=
  .rank_two n hn (rankTwoModel_of_psl h T hne hd hn hmodel)

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
