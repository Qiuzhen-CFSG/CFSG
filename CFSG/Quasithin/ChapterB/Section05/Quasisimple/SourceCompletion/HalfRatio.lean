module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.ChiefImages
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.Ratio

/-!
# Selecting a minimal offender at half ratio

A quadratic ratio at most one half is attained. Maximizing offender weight,
then minimizing within its equal-weight class, retains the inequality
2 codim C_V(B) ≤ rank B. The same actor retains this inequality on every
invariant submodule. This is the selection needed to use the B.4.2 half-ratio
sieve on actual faithful constituents; an arbitrary best offender would not
suffice.

Source: Aschbacher--Smith B.5.1, printed p.100, the smallest q_i and (**).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [FiniteDimensional (ZMod 2) V] in
theorem twice_fixedCodim_le_rank_of_half {A : Subgroup G} (hA : IsElementaryTwo A)
    (h : actionRatio ρ A ≤ 1 / 2) : 2 * fixedCodim ρ A ≤ rank A := by
  have hp : 0 < rank A := hA.rank_pos
  have hr := ENNReal.toReal_mono (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤) h
  simp only [actionRatio, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_one, ENNReal.toReal_ofNat] at hr
  have hp' : (0 : ℝ) < rank A := by exact_mod_cast hp
  have hh := (div_le_iff₀ hp').mp hr
  exact_mod_cast (by nlinarith : (2 : ℝ) * fixedCodim ρ A ≤ rank A)

omit [FiniteDimensional (ZMod 2) V] in
theorem actionRatio_le_half_of_twice {A : Subgroup G} (hA : IsElementaryTwo A)
    (h : 2 * fixedCodim ρ A ≤ rank A) : actionRatio ρ A ≤ 1 / 2 := by
  have hp : 0 < rank A := hA.rank_pos
  have h0 : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have ht : actionRatio ρ A ≠ ⊤ := ENNReal.div_ne_top (by simp) h0
  apply (ENNReal.toReal_le_toReal ht (by norm_num)).mp
  simp only [actionRatio, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_one, ENNReal.toReal_ofNat]
  have hp' : (0 : ℝ) < rank A := by exact_mod_cast hp
  apply (div_le_iff₀ hp').mpr
  have hh : (2 : ℝ) * fixedCodim ρ A ≤ rank A := by exact_mod_cast h
  nlinarith

/-- The half-ratio dimension inequality descends to an invariant submodule
with the same elementary quadratic actor. -/
theorem quadraticRatio_subrepresentation_le_half (W : Subrepresentation ρ)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hd : 2 * fixedCodim ρ A ≤ rank A) : quadraticRatio W.toRepresentation ≤ 1 / 2 := by
  apply (quadraticRatio_le_iff W.toRepresentation (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤)).mpr
  refine ⟨A, hA, quadratic_subrepresentation ρ W hq, ?_⟩
  apply actionRatio_le_half_of_twice W.toRepresentation hA
  exact (Nat.mul_le_mul_left 2 (fixedCodim_subrepresentation_le ρ W A)).trans hd

/-- A half-ratio actor contains a minimal best offender retaining the
half-ratio dimension inequality; equal-weight replacement is used explicitly. -/
theorem exists_minimal_half_ratio (h : quadraticRatio ρ ≤ 1 / 2) :
    ∃ B, IsMinimalBestOffender ρ B ∧ 2 * fixedCodim ρ B ≤ rank B := by
  obtain ⟨A, hA, _, hr⟩ := (quadraticRatio_le_iff ρ (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤)).mp h
  have hc := twice_fixedCodim_le_rank_of_half ρ hA hr
  have hoff : IsOffender ρ A := ⟨hA, by omega⟩
  obtain ⟨B, hBA, hB, hweight⟩ := exists_bestOffender_ge_weight ρ hoff
  obtain ⟨D, hD, hDB⟩ := hB.exists_minimal ρ
  have hw : weight ρ A ≤ weight ρ D := hweight.trans_eq hDB.2.symm
  have hrank : rank D ≤ rank A := Nat.log_mono_right (Subgroup.card_le_of_le (hDB.1.trans hBA))
  have ha := fixedCodim_add_finrank ρ A
  have hd := fixedCodim_add_finrank ρ D
  unfold weight at hw
  refine ⟨D, hD, ?_⟩
  omega

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
