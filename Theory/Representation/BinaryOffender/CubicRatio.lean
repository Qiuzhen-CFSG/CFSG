module

public import Theory.Representation.BinaryOffender.Replacement
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Cubic binary actions and their minimum ratio

The cubic condition is the vanishing of the third iterated displacement,
equivalently `[V,A,A,A] = 0`. The minimum is attained for a finite group.
Thompson replacement identifies its threshold at one with the FF condition,
without identifying cubic actors with quadratic actors.

This is the reusable version of the cubic definitions and proofs in the
Chapter 15 `SourceRestrictions.Cases.Ratios` module. Those public definitions
are preserved; the two versions are definitionally equal. The additional
threshold and natural-number bounds support Chapter K's source argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.1,
printed p.85, and the Chapter K introduction, printed pp.451–452.
-/

@[expose] public section
namespace Representation.BinaryOffender
open scoped ENNReal
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

/-- The displacement operator, so iterated commutators are compositions. -/
def displacement (ρ : Representation (ZMod 2) D V) (a : D) : V →ₗ[ZMod 2] V :=
  ρ a - LinearMap.id

/-- B.4.1's cubic condition is [V,A,A,A]=0. -/
def IsCubic (ρ : Representation (ZMod 2) D V) (A : Subgroup D) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ v : V,
    displacement ρ a (displacement ρ b (displacement ρ c v)) = 0

/-- The cubic ratio of B.4.1, separate from the quadratic ratio of B.1.1. -/
noncomputable def cubicRatio (ρ : Representation (ZMod 2) D V) : ℝ≥0∞ :=
  ⨅ (A : Subgroup D) (_ : IsElementaryTwo A ∧ IsCubic ρ A), actionRatio ρ A

theorem isCubic_of_isQuadratic {ρ : Representation (ZMod 2) D V} {A : Subgroup D}
    (h : IsQuadratic ρ A) : IsCubic ρ A := by
  intro a ha b hb c hc v
  have hz : displacement ρ b (displacement ρ c v) = 0 :=
    sub_eq_zero.mpr (h b hb c hc v)
  rw [hz, map_zero]

theorem cubicRatio_le_quadraticRatio (ρ : Representation (ZMod 2) D V) :
    cubicRatio ρ ≤ quadraticRatio ρ := by
  apply le_iInf
  intro A
  apply le_iInf
  intro hA
  exact iInf_le_of_le A (iInf_le_of_le ⟨hA.1, isCubic_of_isQuadratic hA.2⟩ le_rfl)

theorem isCubic_iff_commutator_eq_bot (ρ : Representation (ZMod 2) D V)
    (A : Subgroup D) : IsCubic ρ A ↔
      subspaceCommutator ρ (subspaceCommutator ρ (subspaceCommutator ρ ⊤ A) A) A = ⊥ := by
  constructor
  · intro h
    rw [subspaceCommutator_eq_bot_iff]
    intro v hv a
    have hv' : v ∈ LinearMap.ker (displacement ρ a) := by
      apply (show subspaceCommutator ρ (subspaceCommutator ρ ⊤ A) A ≤
          LinearMap.ker (displacement ρ a) from ?_) hv
      apply Submodule.span_le.mpr
      rintro _ ⟨b, hb, w, hw, rfl⟩
      have hw' : w ∈ LinearMap.ker ((displacement ρ a).comp (displacement ρ b)) := by
        apply (show subspaceCommutator ρ ⊤ A ≤
            LinearMap.ker ((displacement ρ a).comp (displacement ρ b)) from ?_) hw
        apply Submodule.span_le.mpr
        rintro _ ⟨c, hc, x, _, rfl⟩
        exact h a a.property b hb c hc x
      exact hw'
    exact sub_eq_zero.mp hv'
  · intro h a ha b hb c hc v
    have hc' : ρ c v - v ∈ subspaceCommutator ρ ⊤ A :=
      Submodule.subset_span ⟨c, hc, v, Submodule.mem_top, rfl⟩
    have hb' : displacement ρ b (ρ c v - v) ∈
        subspaceCommutator ρ (subspaceCommutator ρ ⊤ A) A :=
      Submodule.subset_span ⟨b, hb, ρ c v - v, hc', rfl⟩
    exact sub_eq_zero.mpr ((subspaceCommutator_eq_bot_iff _ _ _).mp h hb' ⟨a, ha⟩)

theorem cubicRatio_le_iff [Finite D] (ρ : Representation (ZMod 2) D V)
    {r : ℝ≥0∞} (hr : r ≠ ⊤) :
    cubicRatio ρ ≤ r ↔
      ∃ A, IsElementaryTwo A ∧ IsCubic ρ A ∧ actionRatio ρ A ≤ r := by
  classical
  constructor
  · intro h
    let S := {A : Subgroup D // IsElementaryTwo A ∧ IsCubic ρ A}
    by_cases hS : Nonempty S
    · let : Nonempty S := hS
      obtain ⟨A, hA⟩ := exists_eq_ciInf_of_finite (f := fun A : S => actionRatio ρ A.val)
      rw [iInf_subtype] at hA
      exact ⟨A.val, A.property.1, A.property.2, hA.trans_le h⟩
    · have htop : cubicRatio ρ = ⊤ := by
        apply iInf_eq_top.mpr
        intro A
        apply iInf_eq_top.mpr
        intro hA
        exact (hS ⟨⟨A, hA⟩⟩).elim
      exact (hr (top_le_iff.mp (htop ▸ h))).elim
  · rintro ⟨A, hA, hc, hle⟩
    exact (iInf_le_of_le A (iInf_le_of_le ⟨hA, hc⟩ le_rfl)).trans hle

/-- Even a cubic actor of ratio at most one is an offender. This does not
identify the quadratic and cubic ratios or require cubic actors to be quadratic. -/
theorem isFFModule_of_cubicRatio_le_one [Finite D]
    (ρ : Representation (ZMod 2) D V) (h : cubicRatio ρ ≤ 1) : IsFFModule ρ := by
  obtain ⟨A, hA, _, hr⟩ := (cubicRatio_le_iff ρ (by simp)).mp h
  exact ⟨A, hA, (actionRatio_le_one_iff ρ hA).mp hr⟩

/-- Clearing the positive actor rank in a finite action ratio. -/
theorem actionRatio_le_nat_iff [Finite D] (ρ : Representation (ZMod 2) D V)
    {A : Subgroup D} (hA : IsElementaryTwo A) (n : ℕ) :
    actionRatio ρ A ≤ (n : ℝ≥0∞) ↔ fixedCodim ρ A ≤ n * rank A := by
  have h0 : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA.rank_pos)
  rw [actionRatio, ENNReal.div_le_iff h0 (by simp)]
  exact_mod_cast Iff.rfl

/-- The cubic bound supplies an actual actor with the indicated dimension bound. -/
theorem cubicRatio_le_nat_iff [Finite D] (ρ : Representation (ZMod 2) D V) (n : ℕ) :
    cubicRatio ρ ≤ (n : ℝ≥0∞) ↔
      ∃ A, IsElementaryTwo A ∧ IsCubic ρ A ∧ fixedCodim ρ A ≤ n * rank A := by
  rw [cubicRatio_le_iff ρ (by simp)]
  constructor
  · rintro ⟨A, hA, hc, hr⟩
    exact ⟨A, hA, hc, (actionRatio_le_nat_iff ρ hA n).mp hr⟩
  · rintro ⟨A, hA, hc, hr⟩
    exact ⟨A, hA, hc, (actionRatio_le_nat_iff ρ hA n).mpr hr⟩

/-- The FF threshold is the same for cubic and quadratic action ratios. -/
theorem isFFModule_iff_cubicRatio_le_one [Finite D] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) : IsFFModule ρ ↔ cubicRatio ρ ≤ 1 := by
  constructor
  · intro h
    exact (cubicRatio_le_quadraticRatio ρ).trans
      ((isFFModule_iff_quadraticRatio_le_one ρ).mp h)
  · exact isFFModule_of_cubicRatio_le_one ρ

/-- The comparison at one uses replacement; the two infima need not be equal. -/
theorem cubicRatio_le_one_iff_quadraticRatio_le_one [Finite D]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V) :
    cubicRatio ρ ≤ 1 ↔ quadraticRatio ρ ≤ 1 :=
  (isFFModule_iff_cubicRatio_le_one ρ).symm.trans
    (isFFModule_iff_quadraticRatio_le_one ρ)

end Representation.BinaryOffender
