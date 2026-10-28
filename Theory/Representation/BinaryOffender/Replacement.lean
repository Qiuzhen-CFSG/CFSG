module

public import Theory.Representation.BinaryOffender.ReplacementCounting
public import Theory.Representation.BinaryOffender.Ratio

/-!
# Thompson replacement for binary offenders

For each vector `v`, the actual centralizer `C_A([v,A])` has equal weight
to a best offender `A`. The displacement-coset bound and the cyclic-span
lemma also prove that this centralizer is nontrivial. Equal-weight
minimality therefore forces it to be all of `A`, proving quadraticity.
Weight maximization followed by equal-weight minimization extracts a
quadratic offender without losing strict offending. This proves the
FF-module equivalence with quadratic ratio at most one, and its strict
analogue. Ambient faithfulness is not needed for these arguments.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, B.1.4(3), (5), printed pp. 68–69.
-/

public section
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The replacement centralizer has the original best offender's weight. -/
theorem IsBestOffender.replacement_equalWeightLE {A : Subgroup G}
    (hA : IsBestOffender ρ A) (v : V) :
    EqualWeightLE ρ (replacementSubgroup ρ A v) A := by
  refine ⟨replacementSubgroup_le ρ A v, le_antisymm
    (hA.2 _ (replacementSubgroup_le ρ A v)) ?_⟩
  have hle : displacementSpan ρ A v ⊔ fixedSpace ρ A ≤
      fixedSpace ρ (replacementSubgroup ρ A v) :=
    sup_le (displacementSpan_le_fixedSpace_replacement ρ A v)
      (fixedSpace_antitone ρ (replacementSubgroup_le ρ A v))
  exact (replacement_rank_bound ρ hA.1 v).trans
    (Nat.add_le_add_left (Submodule.finrank_mono hle) _)

/-- The actual replacement centralizer of a best offender is nontrivial. -/
theorem IsBestOffender.replacement_ne_bot {A : Subgroup G}
    (hA : IsBestOffender ρ A) (v : V) : replacementSubgroup ρ A v ≠ ⊥ := by
  by_cases hv : v ∈ fixedSpace ρ A
  · rw [replacementSubgroup_eq_of_mem_fixedSpace ρ hv]
    exact hA.1.1
  · intro hbot
    have hproper : displacementSpan ρ A v ⊔ fixedSpace ρ A ≠ ⊤ := by
      intro htop
      apply hv
      apply (mem_displacementSpan_sup_fixedSpace_iff ρ hA.1 v).mp
      rw [htop]
      trivial
    have hlt := Submodule.finrank_lt hproper
    have hbound := replacement_rank_bound ρ hA.1 v
    rw [hbot, rank_bot, zero_add] at hbound
    have hweight := (fixedCodim_le_rank_iff ρ A).mp (hA.isOffender ρ).2
    omega

/-- The replacement centralizer is itself a best offender. -/
theorem IsBestOffender.replacement_isBestOffender {A : Subgroup G}
    (hA : IsBestOffender ρ A) (v : V) :
    IsBestOffender ρ (replacementSubgroup ρ A v) :=
  hA.of_equalWeightLE ρ
    (hA.1.of_le (replacementSubgroup_le ρ A v) (hA.replacement_ne_bot ρ v))
    (hA.replacement_equalWeightLE ρ v)

/-- Thompson replacement, B.1.4(3): equal-weight minimal best offenders are quadratic.
The argument proves this even without the source's ambient faithfulness assumption. -/
theorem IsMinimalBestOffender.isQuadratic {A : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) : IsQuadratic ρ A := by
  intro a ha b hb v
  have heq := hA.2 _ (hA.1.replacement_isBestOffender ρ v)
    (hA.1.replacement_equalWeightLE ρ v)
  have ha' : a ∈ replacementSubgroup ρ A v := heq.symm ▸ ha
  exact (mem_replacementSubgroup_iff ρ).mp ha' |>.2 b hb

/-- The inclusion-minimal case in B.1.4(3). -/
theorem isQuadratic_of_inclusion_minimal_bestOffender {A : Subgroup G}
    (hA : IsBestOffender ρ A)
    (hmin : ∀ B ≤ A, IsBestOffender ρ B → B = A) : IsQuadratic ρ A := by
  apply IsMinimalBestOffender.isQuadratic ρ
  exact ⟨hA, fun B hB hBA => hmin B hBA.1 hB⟩

/-- Every offender contains a quadratic minimal best offender with no smaller weight. -/
theorem IsOffender.exists_quadratic_minimalBestOffender
    {A : Subgroup G} (hA : IsOffender ρ A) :
    ∃ B ≤ A, IsMinimalBestOffender ρ B ∧ IsQuadratic ρ B ∧ weight ρ A ≤ weight ρ B := by
  obtain ⟨C, hCA, hC, hweight⟩ := exists_bestOffender_ge_weight ρ hA
  obtain ⟨B, hB, hBC⟩ := hC.exists_minimal ρ
  exact ⟨B, hBC.1.trans hCA, hB, hB.isQuadratic ρ, hBC.2.symm ▸ hweight⟩

/-- Quadratic replacement preserves strict offending, as needed when excluding `q < 1`. -/
theorem IsStrongOffender.exists_quadratic_minimalBestOffender
    {A : Subgroup G} (hA : IsStrongOffender ρ A) :
    ∃ B ≤ A, IsMinimalBestOffender ρ B ∧ IsQuadratic ρ B ∧ IsStrongOffender ρ B := by
  obtain ⟨B, hBA, hB, hquad, hweight⟩ :=
    (show IsOffender ρ A from ⟨hA.1, hA.2.le⟩).exists_quadratic_minimalBestOffender ρ
  refine ⟨B, hBA, hB, hquad, hB.1.1, (fixedCodim_lt_rank_iff ρ B).mpr ?_⟩
  exact ((fixedCodim_lt_rank_iff ρ A).mp hA.2).trans_le hweight

/-- B.1.4(5): failure of factorization is equivalent to quadratic ratio at most one. -/
theorem isFFModule_iff_quadraticRatio_le_one : IsFFModule ρ ↔ quadraticRatio ρ ≤ 1 := by
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨B, _, hB, hquad, _⟩ := hA.exists_quadratic_minimalBestOffender ρ
    exact (quadraticRatio_le_one_iff ρ).mpr ⟨B, hB.1.isOffender ρ, hquad⟩
  · exact isFFModule_of_quadraticRatio_le_one ρ

/-- Strong failure of factorization is equivalent to quadratic ratio strictly below one. -/
theorem isStrongFFModule_iff_quadraticRatio_lt_one :
    IsStrongFFModule ρ ↔ quadraticRatio ρ < 1 := by
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨B, _, hB, hquad, hstrong⟩ := hA.exists_quadratic_minimalBestOffender ρ
    have hle : quadraticRatio ρ ≤ actionRatio ρ B :=
      iInf_le_of_le B (iInf_le_of_le ⟨hB.1.1, hquad⟩ le_rfl)
    exact hle.trans_lt ((actionRatio_lt_one_iff ρ hstrong.1).mpr hstrong.2)
  · intro h
    by_contra hstrong
    have hlower : 1 ≤ quadraticRatio ρ := by
      refine le_iInf fun A => le_iInf fun hA => ?_
      apply le_of_not_gt
      intro hlt
      exact hstrong ⟨A, hA.1, (actionRatio_lt_one_iff ρ hA.1).mp hlt⟩
    exact (not_lt_of_ge hlower) h

end Representation.BinaryOffender
