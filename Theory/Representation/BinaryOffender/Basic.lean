module
public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Basic binary offender lemmas

We prove the elementary parts of Aschbacher–Smith B.1.4 (1), (2), (4),
(5)(i) iff (ii), and (6). Maximizing the weight among the nontrivial subgroups
of a given offender gives a best offender and preserves strong offending.
Minimizing order within an equal-weight class gives a minimal best offender.
Rank-nullity identifies the dimension inequalities with weight comparisons;
the action-ratio lemmas recover the source's ratio formulation.

Source: *The Classification of Quasithin Groups*, 1 March 2004 manuscript,
printed pp. 67–69. Thompson replacement and the equivalence with the global
quadratic ratio are not proved in this module.
-/

@[expose] public section
namespace Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A nontrivial subgroup of an elementary abelian 2-subgroup is elementary abelian. -/
theorem IsElementaryTwo.of_le {A B : Subgroup G} (hA : IsElementaryTwo A)
    (hBA : B ≤ A) (hB : B ≠ ⊥) : IsElementaryTwo B := by
  let _ : IsElementaryAbelian 2 A := hA.2
  refine ⟨hB, ?_⟩
  exact {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
      (congrArg (fun a : A => (a : G)) ((IsMulCommutative.is_comm (M := A)).comm
        (⟨x, hBA x.property⟩ : A) ⟨y, hBA y.property⟩))⟩⟩
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (x : G) (hBA x.property) }

/-- The trivial subgroup has binary rank zero. -/
@[simp] theorem rank_bot : rank (⊥ : Subgroup G) = 0 := by simp [rank]

/-- The trivial subgroup fixes the whole representation. -/
@[simp] theorem fixedSpace_bot : fixedSpace ρ ⊥ = ⊤ := by
  ext v
  simp [fixedSpace, Representation.mem_invariants]

/-- The trivial subgroup has weight equal to the dimension of the module. -/
@[simp] theorem weight_bot : weight ρ ⊥ = Module.finrank (ZMod 2) V := by
  rw [weight, rank_bot, fixedSpace_bot ρ]
  simp

/-- Rank-nullity for the fixed space. -/
theorem fixedCodim_add_finrank [FiniteDimensional (ZMod 2) V] (A : Subgroup G) :
    fixedCodim ρ A + Module.finrank (ZMod 2) (fixedSpace ρ A) =
      Module.finrank (ZMod 2) V :=
  (fixedSpace ρ A).finrank_quotient_add_finrank

/-- The offender inequality is equivalent to a lower bound on weight. -/
theorem fixedCodim_le_rank_iff [FiniteDimensional (ZMod 2) V] (A : Subgroup G) :
    fixedCodim ρ A ≤ rank A ↔ Module.finrank (ZMod 2) V ≤ weight ρ A := by
  have := fixedCodim_add_finrank ρ A
  unfold weight
  omega

/-- The strict offender inequality is equivalent to a strict weight bound. -/
theorem fixedCodim_lt_rank_iff [FiniteDimensional (ZMod 2) V] (A : Subgroup G) :
    fixedCodim ρ A < rank A ↔ Module.finrank (ZMod 2) V < weight ρ A := by
  have := fixedCodim_add_finrank ρ A
  unfold weight
  omega

/-- B.1.4(1): a best offender is an offender. -/
theorem IsBestOffender.isOffender [FiniteDimensional (ZMod 2) V]
    {A : Subgroup G} (hA : IsBestOffender ρ A) : IsOffender ρ A := by
  refine ⟨hA.1, (fixedCodim_le_rank_iff ρ A).2 ?_⟩
  simpa using hA.2 ⊥ bot_le

/-- B.1.4(2): nontrivial equal-weight subgroups of best offenders are best offenders. -/
theorem IsBestOffender.of_equalWeightLE {A B : Subgroup G}
    (hA : IsBestOffender ρ A) (hB : IsElementaryTwo B) (hBA : EqualWeightLE ρ B A) :
    IsBestOffender ρ B := by
  refine ⟨hB, fun C hC => ?_⟩
  rw [hBA.2]
  exact hA.2 C (hC.trans hBA.1)

/-- An offender contains a best offender of at least its weight. -/
theorem exists_bestOffender_ge_weight [Finite G] [FiniteDimensional (ZMod 2) V]
    {A : Subgroup G} (hA : IsOffender ρ A) :
    ∃ B ≤ A, IsBestOffender ρ B ∧ weight ρ A ≤ weight ρ B := by
  classical
  let S : Set (Subgroup G) := {B | B ≤ A ∧ B ≠ ⊥}
  obtain ⟨B, hB, hmax⟩ := Set.exists_max_image S (weight ρ) (Set.toFinite _)
    ⟨A, le_rfl, hA.1.1⟩
  have hAB : weight ρ A ≤ weight ρ B := hmax A ⟨le_rfl, hA.1.1⟩
  refine ⟨B, hB.1, ⟨hA.1.of_le hB.1 hB.2, ?_⟩, hAB⟩
  intro C hCB
  by_cases hC : C = ⊥
  · subst C
    rw [weight_bot]
    exact ((fixedCodim_le_rank_iff ρ A).1 hA.2).trans hAB
  · exact hmax C ⟨hCB.trans hB.1, hC⟩

/-- B.1.4(4), weak case: every offender contains a best offender. -/
theorem IsOffender.exists_bestOffender [Finite G] [FiniteDimensional (ZMod 2) V]
    {A : Subgroup G} (hA : IsOffender ρ A) : ∃ B ≤ A, IsBestOffender ρ B := by
  obtain ⟨B, hBA, hB, _⟩ := exists_bestOffender_ge_weight ρ hA
  exact ⟨B, hBA, hB⟩

/-- B.1.4(4), strict case: a strong offender contains a strong best offender. -/
theorem IsStrongOffender.exists_bestOffender [Finite G] [FiniteDimensional (ZMod 2) V]
    {A : Subgroup G} (hA : IsStrongOffender ρ A) :
    ∃ B ≤ A, IsBestOffender ρ B ∧ IsStrongOffender ρ B := by
  obtain ⟨B, hBA, hB, hAB⟩ := exists_bestOffender_ge_weight ρ ⟨hA.1, hA.2.le⟩
  exact ⟨B, hBA, hB, hB.1, (fixedCodim_lt_rank_iff ρ B).2
    (((fixedCodim_lt_rank_iff ρ A).1 hA.2).trans_le hAB)⟩

/-- B.1.4(5)(i) iff (ii): failure of factorization is detected by best offenders. -/
theorem isFFModule_iff_exists_bestOffender [Finite G] [FiniteDimensional (ZMod 2) V] :
    IsFFModule ρ ↔ ∃ A, IsBestOffender ρ A := by
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨B, _, hB⟩ := hA.exists_bestOffender ρ
    exact ⟨B, hB⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, hA.isOffender ρ⟩

/-- B.1.4(6), dimension form: without strong offenders, best offenders have equality. -/
theorem isBestOffender_iff_of_not_strong [FiniteDimensional (ZMod 2) V]
    (h : ¬ IsStrongFFModule ρ) (A : Subgroup G) :
    IsBestOffender ρ A ↔ IsElementaryTwo A ∧ fixedCodim ρ A = rank A := by
  constructor
  · intro hA
    refine ⟨hA.1, le_antisymm (hA.isOffender ρ).2 ?_⟩
    exact Nat.le_of_not_gt (fun hlt => h ⟨A, hA.1, hlt⟩)
  · rintro ⟨hA, heq⟩
    refine ⟨hA, fun B hBA => ?_⟩
    have hdim := fixedCodim_add_finrank ρ A
    have hweight : weight ρ A = Module.finrank (ZMod 2) V := by
      unfold weight
      omega
    rw [hweight]
    by_cases hB : B = ⊥
    · subst B
      simp
    · have hnot : ¬ fixedCodim ρ B < rank B :=
        fun hlt => h ⟨B, hA.of_le hBA hB, hlt⟩
      have := fixedCodim_add_finrank ρ B
      unfold weight
      omega


/-- A nontrivial finite elementary abelian 2-group has positive binary rank. -/
theorem IsElementaryTwo.rank_pos [Finite G] {A : Subgroup G}
    (hA : IsElementaryTwo A) : 0 < rank A := by
  let _ : IsElementaryAbelian 2 A := hA.2
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  rw [rank, hn, Nat.log_pow (by decide : 1 < 2)]
  by_contra h
  have hn0 : n = 0 := by omega
  exact hA.1 (Subgroup.eq_bot_of_card_eq A (by simpa only [hn0, pow_zero] using hn))

/-- The cardinality of an elementary abelian 2-group is two to its rank. -/
theorem IsElementaryTwo.card_eq_two_pow_rank [Finite G] {A : Subgroup G}
    (hA : IsElementaryTwo A) : Nat.card A = 2 ^ rank A := by
  let _ : IsElementaryAbelian 2 A := hA.2
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  rw [rank, hn, Nat.log_pow (by decide : 1 < 2)]

/-- The weak action-ratio inequality agrees with the dimension inequality. -/
theorem actionRatio_le_one_iff [Finite G] {A : Subgroup G} (hA : IsElementaryTwo A) :
    actionRatio ρ A ≤ 1 ↔ fixedCodim ρ A ≤ rank A := by
  have h0 : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA.rank_pos)
  rw [actionRatio, ENNReal.div_le_iff h0 (by simp), one_mul]
  exact_mod_cast Iff.rfl

/-- The strict action-ratio inequality agrees with the dimension inequality. -/
theorem actionRatio_lt_one_iff [Finite G] {A : Subgroup G} (hA : IsElementaryTwo A) :
    actionRatio ρ A < 1 ↔ fixedCodim ρ A < rank A := by
  have h0 : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA.rank_pos)
  rw [actionRatio, ENNReal.div_lt_iff (Or.inl h0) (Or.inl (by simp)), one_mul]
  exact_mod_cast Iff.rfl

/-- Action ratio one means equality of the two dimensions. -/
theorem actionRatio_eq_one_iff [Finite G] {A : Subgroup G} (hA : IsElementaryTwo A) :
    actionRatio ρ A = 1 ↔ fixedCodim ρ A = rank A := by
  have h0 : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA.rank_pos)
  rw [actionRatio, ENNReal.div_eq_one_iff h0 (by simp)]
  exact_mod_cast Iff.rfl

/-- Equal-weight inclusion is reflexive. -/
theorem EqualWeightLE.refl (A : Subgroup G) : EqualWeightLE ρ A A := ⟨le_rfl, rfl⟩

/-- Equal-weight inclusion is transitive. -/
theorem EqualWeightLE.trans {A B C : Subgroup G}
    (hAB : EqualWeightLE ρ A B) (hBC : EqualWeightLE ρ B C) : EqualWeightLE ρ A C :=
  ⟨hAB.1.trans hBC.1, hAB.2.trans hBC.2⟩

/-- Equal-weight inclusion is antisymmetric. -/
theorem EqualWeightLE.antisymm {A B : Subgroup G}
    (hAB : EqualWeightLE ρ A B) (hBA : EqualWeightLE ρ B A) : A = B :=
  le_antisymm hAB.1 hBA.1

/-- Every best offender contains an equal-weight minimal best offender. -/
theorem IsBestOffender.exists_minimal [Finite G] {A : Subgroup G}
    (hA : IsBestOffender ρ A) :
    ∃ B, IsMinimalBestOffender ρ B ∧ EqualWeightLE ρ B A := by
  let S : Set (Subgroup G) := {B | IsBestOffender ρ B ∧ EqualWeightLE ρ B A}
  obtain ⟨B, hB, hmin⟩ := Set.exists_min_image S (fun B => Nat.card B) (Set.toFinite _)
    ⟨A, hA, EqualWeightLE.refl ρ A⟩
  refine ⟨B, ⟨hB.1, ?_⟩, hB.2⟩
  intro C hC hCB
  exact Subgroup.eq_of_le_of_card_ge hCB.1
    (hmin C ⟨hC, hCB.trans ρ hB.2⟩)

end Representation.BinaryOffender
