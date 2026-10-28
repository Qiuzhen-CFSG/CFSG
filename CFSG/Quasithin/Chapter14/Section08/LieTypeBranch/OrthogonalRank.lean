module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.OddComparison
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoFixedField
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.RankOneExclusion
public import CFSG.Quasithin.ClassificationModels

/-!
# The orthogonal-family restrictions used by Theorem D

For q = 2^n > 2, actual root two-subgroups and rank-three odd tori in their
literal normalizers exclude every plus rank at least three and every minus
rank at least four, including Ω₈⁻(q). The arbitrary-field minus-four
comparison gives PSL₂(q²), which the nonempty faithful local family excludes.
The remaining minus-six model gives PSU₄(q), hence the exact rank-two output
and the full Theorem D model alternative. Its inherited simplicity premise
is discharged from the original simple QTKE group through the actual model
isomorphism; the unitary parameter remains the fixed-field order q.

The odd orthogonal model is identified with the symplectic model at the same
rank and field, including rank one. This comparison requires neither
simplicity nor a symplectic rank theorem. All comparisons are compositions
of actual multiplicative equivalences respecting the projective quotients.
The earlier canonical-field minus-four interfaces are preserved below.

Sources: Aschbacher–Smith A.2.18, printed p.40, and Theorem D/14.8.2,
printed pp.1078–1079; classical model conventions in GLS3 §2.7.
-/

public section

namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
universe u
variable {G : Type u} [Group G]

/-- An actual binary odd orthogonal model supplies the actual symplectic model,
without a simplicity, quasithinness, or symplectic rank premise. -/
theorem psp_of_pOmegaOdd {r n : ℕ} (hr : 1 ≤ r) (hn : 0 < n)
    (hmodel : ClassicalGroup.IsPOmegaOdd G r (2 ^ n)) :
    ClassicalGroup.IsPSp G r (2 ^ n) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := by
    apply ringChar.of_eq
    apply FiniteField.even_card_iff_char_two.mpr
    rw [← Nat.card_eq_fintype_card, hcard]
    exact Nat.mod_eq_zero_of_dvd
      (even_iff_two_dvd.mp (even_two.pow_of_ne_zero (Nat.ne_of_gt hn)))
  exact ⟨F, hF, hfin, hcard,
    ⟨e.trans (ClassicalOrthogonal.TheoremDRootNormalizer.oddProjectiveEquivPSp
      (by omega))⟩⟩

/-- The canonical minus-four model has the required quadratic-extension PSL₂
identification, with the field order proved rather than inferred from a label. -/
theorem psl_of_pOmegaMinus_two_fixedField {n : ℕ} (hn : 0 < n)
    (hmodel : Nonempty (G ≃* ClassicalGroup.POmegaMinus 2
      (Representation.OrthogonalFourMinus.FiniteModel.fixedField n))) :
    ClassicalGroup.IsPSL G 2 (2 ^ (2 * n)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨e⟩ := hmodel
  refine ⟨Representation.OrthogonalFourMinus.FiniteModel.Field n,
    inferInstance, inferInstance, ?_,
    ⟨e.trans (ClassicalOrthogonal.TheoremDRootNormalizer.minusTwoFixedFieldEquivPSL n)⟩⟩
  exact GaloisField.card 2 (2 * n) (by omega)

/-- The original nonempty faithful local family excludes this actual rank-one
minus model through the proved PSL₂ local theorem. -/
theorem not_pOmegaMinus_two_fixedField_of_faithfulLocalComponents_nonempty
    [Finite G] {K : GroupClass.{u}} (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {n : ℕ} (hn : 0 < n) :
    ¬ Nonempty (G ≃* ClassicalGroup.POmegaMinus 2
      (Representation.OrthogonalFourMinus.FiniteModel.fixedField n)) := by
  intro hmodel
  exact hne.ne_empty (localFamilies_eq_empty_of_psl2 h T (by omega)
    (psl_of_pOmegaMinus_two_fixedField hn hmodel)).2

private theorem orthogonal_charTwo_of_card {F : Type} [Field F] [Finite F]
    {n : ℕ} (hcard : Nat.card F = 2 ^ n) : CharP F 2 := by
  let : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by
    simpa only [← Nat.card_eq_fintype_card] using hcard)

private theorem orthogonal_two_lt_card {F : Type} {n : ℕ}
    (hn : 1 < n) (hcard : Nat.card F = 2 ^ n) : 2 < Nat.card F := by
  rw [hcard]
  exact (by norm_num : (2 : ℕ) = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn

/-- Every plus orthogonal rank in the simple range is excluded over `q > 2`,
including the split rank-three model. -/
theorem not_pOmegaPlus_of_quasithin [Finite G] (hG : IsQuasithin G)
    {r n : ℕ} (hr : 3 ≤ r) (hn : 1 < n) :
    ¬ ClassicalGroup.IsPOmegaPlus G r (2 ^ n) := by
  rintro ⟨F, hF, hfin, hcard, ⟨e⟩⟩
  let : CharP F 2 := orthogonal_charTwo_of_card hcard
  exact ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.not_quasithin_plus
    hr (orthogonal_two_lt_card hn hcard) (Theory.GroupTheory.isQuasithin_of_equiv e hG)

/-- The plus branch of the source simple QTKE input is impossible. -/
theorem not_pOmegaPlus_of_isSimpleQTKE [Finite G]
    {K : GroupClass.{u}} (h : IsSimpleQTKE K G)
    {r n : ℕ} (hr : 3 ≤ r) (hn : 1 < n) :
    ¬ ClassicalGroup.IsPOmegaPlus G r (2 ^ n) :=
  not_pOmegaPlus_of_quasithin h.quasithin hr hn

/-- Every minus rank at least four is excluded, including the source's
`Ω₈⁻(q)` case of relative Lie rank three. -/
theorem not_pOmegaMinus_of_quasithin [Finite G] (hG : IsQuasithin G)
    {r n : ℕ} (hr : 4 ≤ r) (hn : 1 < n) :
    ¬ ClassicalGroup.IsPOmegaMinus G r (2 ^ n) := by
  rintro ⟨F, hF, hfin, hcard, ⟨e⟩⟩
  let : CharP F 2 := orthogonal_charTwo_of_card hcard
  exact ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.not_quasithin_minus
    (orthogonal_two_lt_card hn hcard) hr (Theory.GroupTheory.isQuasithin_of_equiv e hG)

/-- Quasithinness leaves only the low-rank minus aliases. -/
theorem pOmegaMinus_rank_le_three_of_quasithin [Finite G] (hG : IsQuasithin G)
    {r n : ℕ} (hn : 1 < n) (hmodel : ClassicalGroup.IsPOmegaMinus G r (2 ^ n)) :
    r ≤ 3 := by
  by_contra hlarge
  exact not_pOmegaMinus_of_quasithin hG (by omega) hn hmodel

/-- The actual minus-four model over an arbitrary field of order `2^n` is
PSL₂ over the quadratic extension. No simplicity assumption is needed. -/
theorem psl_of_pOmegaMinus_two {n : ℕ} (hn : 0 < n)
    (hmodel : ClassicalGroup.IsPOmegaMinus G 2 (2 ^ n)) :
    ClassicalGroup.IsPSL G 2 (2 ^ (2 * n)) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  refine ⟨GaloisField 2 (2 * n), inferInstance, inferInstance, ?_,
    ⟨e.trans (ClassicalOrthogonal.TheoremDRootNormalizer.minusTwoEquivPSL F hn hcard)⟩⟩
  exact GaloisField.card 2 (2 * n) (by omega)

/-- The actual minus-six model is PSU₄ with fixed-field order `2^n`.
Simplicity is transported from the original group to its orthogonal carrier. -/
theorem psu_of_pOmegaMinus_three [IsSimpleGroup G] {n : ℕ} (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPOmegaMinus G 3 (2 ^ n)) :
    ClassicalGroup.IsPSU G 4 (2 ^ n) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let : IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F) := e.symm.isSimpleGroup
  obtain ⟨E, hE, hfinite, J, hcardE, hconj, ⟨f⟩⟩ :=
    ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.exists_comparison n hn hcard
  exact ⟨E, hE, hfinite, J, hcardE, hconj, ⟨e.trans f⟩⟩

/-- The rank-one minus alias is excluded by the original faithful local
family, now for every permitted coefficient field. -/
theorem not_pOmegaMinus_two_of_faithfulLocalComponents_nonempty
    [Finite G] {K : GroupClass.{u}} (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {n : ℕ} (hn : 0 < n) : ¬ ClassicalGroup.IsPOmegaMinus G 2 (2 ^ n) := by
  intro hmodel
  exact hne.ne_empty (localFamilies_eq_empty_of_psl2 h T (by omega)
    (psl_of_pOmegaMinus_two hn hmodel)).2

/-- In the full simple minus range, the source hypotheses force rank three
(natural dimension six, relative Lie rank two). -/
theorem pOmegaMinus_rank_eq_three_of_faithfulLocalComponents_nonempty
    [Finite G] {K : GroupClass.{u}} (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {r n : ℕ} (hr : 2 ≤ r) (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPOmegaMinus G r (2 ^ n)) : r = 3 := by
  have hle := pOmegaMinus_rank_le_three_of_quasithin h.quasithin hn hmodel
  by_contra hne3
  have hr2 : r = 2 := by omega
  subst r
  exact not_pOmegaMinus_two_of_faithfulLocalComponents_nonempty h T hne (by omega) hmodel

/-- The surviving actual minus-six model gives the source's unitary-four
rank-two output at the original fixed-field exponent. -/
theorem rankTwoModel_of_pOmegaMinus_three
    [Finite G] {K : GroupClass.{u}} (h : IsSimpleQTKE K G)
    {n : ℕ} (hn : 1 < n) (hmodel : ClassicalGroup.IsPOmegaMinus G 3 (2 ^ n)) :
    ClassificationModels.IsRankTwoModel G n := by
  let : IsSimpleGroup G := h.simple
  exact .unitary_four (by omega) (psu_of_pOmegaMinus_three hn hmodel)

/-- The complete minus-family branch discharges both the higher-rank and
rank-one exclusions before constructing the actual unitary model. -/
theorem rankTwoModel_of_pOmegaMinus
    [Finite G] {K : GroupClass.{u}} (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {r n : ℕ} (hr : 2 ≤ r) (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPOmegaMinus G r (2 ^ n)) :
    ClassificationModels.IsRankTwoModel G n := by
  have hr3 := pOmegaMinus_rank_eq_three_of_faithfulLocalComponents_nonempty h T hne hr hn hmodel
  subst r
  exact rankTwoModel_of_pOmegaMinus_three h hn hmodel

/-- Complete Theorem D output for the actual minus orthogonal family. -/
theorem theoremDModel_of_pOmegaMinus
    [Finite G] {K : GroupClass.{u}} (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {r n : ℕ} (hr : 2 ≤ r) (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPOmegaMinus G r (2 ^ n)) :
    ClassificationModels.IsTheoremDModel G :=
  .rank_two n hn (rankTwoModel_of_pOmegaMinus h T hne hr hn hmodel)

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
