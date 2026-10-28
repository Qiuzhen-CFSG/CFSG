module

public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer.RankOne
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.RankOneExclusion
public import CFSG.Quasithin.ClassificationModels

/-!
# The complete symplectic-family branch of Theorem D over fields larger than two

For a genuine PSp₂ᵣ(2ⁿ) model with `n > 1`, three inverse diagonal pairs in
an actual projective root two-local normalizer exclude `r ≥ 3` by quasithinness.
The concrete PSp₂–PSL₂ equivalence and the rank-one Borel theorem exclude
`r = 1` when the faithful local family is nonempty. Thus `r = 2`, giving
precisely the allowed symplectic rank-two model at the unchanged exponent.

Here `r` is half the natural dimension, and every transport uses the field
and multiplicative equivalence supplied by `ClassicalGroup.IsPSp`. No
parabolic induction, normalizer-rank premise or classification premise is
added. The source K-class can remain arbitrary.

Source: Aschbacher–Smith, A.2.18 (printed p.40) and Theorem D/14.8.2(1)
(printed pp.1078–1079). The field-of-order-two cases belong to the separate
binary-field branch; the other Lie families retain their own assembly owners.
-/

public section

namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch

universe u
variable {G : Type u} [Group G] [Finite G]

/-- A quasithin symplectic model over a binary field larger than two has rank at most two. -/
theorem psp_rank_le_two_of_quasithin (hG : IsQuasithin G)
    {r n : ℕ} (hn : 1 < n) (hmodel : ClassicalGroup.IsPSp G r (2 ^ n)) : r ≤ 2 := by
  by_contra hlarge
  have hr : 3 ≤ r := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
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
  exact Theory.SpecificGroups.SymplecticRoot.not_quasithin k hq
    (Theory.GroupTheory.isQuasithin_of_equiv e hG)

omit [Finite G] in
/-- The genuine rank-one projective symplectic model is a PSL₂ model over the same field. -/
theorem psl2_of_psp_rankOne {q : ℕ} (hmodel : ClassicalGroup.IsPSp G 1 q) :
    ClassicalGroup.IsPSL G 2 q := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  exact ⟨F, hF, hfin, hcard,
    ⟨e.trans Theory.SpecificGroups.SymplecticRoot.rankOneProjectiveEquiv⟩⟩

/-- The actual nonempty faithful family excludes symplectic rank one. -/
theorem psp_rank_eq_two_of_faithfulLocalComponents_nonempty
    {K : GroupClass.{u}} (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {r n : ℕ} (hr : 1 ≤ r) (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSp G r (2 ^ n)) : r = 2 := by
  have hle := psp_rank_le_two_of_quasithin h.quasithin hn hmodel
  by_contra hne2
  have hr1 : r = 1 := by omega
  subst r
  exact hne.ne_empty
    (localFamilies_eq_empty_of_psl2 h T (by omega) (psl2_of_psp_rankOne hmodel)).2

/-- The symplectic family supplies the exact rank-two model at the original exponent. -/
theorem rankTwoModel_of_psp
    {K : GroupClass.{u}} (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {r n : ℕ} (hr : 1 ≤ r) (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSp G r (2 ^ n)) :
    ClassificationModels.IsRankTwoModel G n := by
  have hr2 := psp_rank_eq_two_of_faithfulLocalComponents_nonempty h T hne hr hn hmodel
  subst r
  exact .symplectic (by omega) hmodel

/-- Complete Theorem D output for every positive-rank symplectic model over q > 2. -/
theorem theoremDModel_of_psp
    {K : GroupClass.{u}} (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {r n : ℕ} (hr : 1 ≤ r) (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSp G r (2 ^ n)) :
    ClassificationModels.IsTheoremDModel G :=
  .rank_two n hn (rankTwoModel_of_psp h T hne hr hn hmodel)

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
