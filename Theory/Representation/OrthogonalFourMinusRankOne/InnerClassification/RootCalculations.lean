module

public import Theory.Representation.OrthogonalFourMinusRankOne.InnerClassification.Lines
public import Theory.Representation.OrthogonalFourMinusRankOne.InnerClassification.Conjugacy

/-!
# Classification and exact ratios inside the orthogonal root group

A nontrivial quadratic subgroup lies in one fixed-field line and has the same
fixed plane as that line. Its rank is at most s, with equality exactly for the
whole line. A subgroup not lying in a line fixes the common root fixed line;
its rank is at most 2s, with equality exactly for the whole root group.

Source: Aschbacher–Smith, K.3.1.2, printed p.454, with the ratios and actor
thresholds defined in D.2.1, printed p.178. No assumption s>1 is needed.
-/

@[expose] public noncomputable section
namespace Representation.OrthogonalFourMinus.RankOne
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.BinaryOffender Matrix.SpecialLinearGroup
open scoped ENNReal
variable (s : ℕ) [NeZero s]
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))
local notation "H" => SL2.BinarySmall.hermitian s
local notation "U" => upperUnipotent (Field s)

theorem rootLine_calculation {u : Field s} (hu : u ≠ 0) :
    IsElementaryTwo (rootLine s u) ∧ IsQuadratic H (rootLine s u) ∧
      rank (rootLine s u) = s ∧ fixedCodim H (rootLine s u) = 2 * s ∧
      actionRatio H (rootLine s u) = 2 := by
  obtain ⟨g, _, hg⟩ := rootLine_eq_normalizer_conjugate s hu
  rw [hg]
  exact ⟨(fixedRoot_elementary s).map_conj g,
    (InnerTransport.quadratic_conj_iff _ _ _).mpr (fixedRoot_quadratic s),
    (rank_map_conj _ _).trans (fixedRoot_rank s),
    (fixedCodim_map_conj _ _ _).trans (fixedRoot_fixedCodim s),
    (InnerTransport.ratio_conj _ _ _).trans (fixedRoot_actionRatio s)⟩

theorem quadratic_iff_le_rootLine (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s)))
    (hAU : A ≤ U) (hne : A ≠ ⊥) :
    IsQuadratic H A ↔ ∃ u : Field s, u ≠ 0 ∧ A ≤ rootLine s u := by
  constructor
  · intro hq
    obtain ⟨a, ha, ha1⟩ := A.bot_or_exists_ne_one.resolve_left hne
    obtain ⟨u, rfl⟩ := (mem_upperUnipotent _ _).mp (hAU ha)
    have hu : u ≠ 0 := by intro h; subst u; exact ha1 (transvection_coeff_zero _)
    refine ⟨u, hu, ?_⟩
    intro b hb
    obtain ⟨v, rfl⟩ := (mem_upperUnipotent _ _).mp (hAU hb)
    exact (upper_mem_rootLine_iff s hu v).mpr
      ((root_subgroup_quadratic_iff_fixed_ratios s A hAU hu ha).mp hq v hb)
  · rintro ⟨u, hu, hA⟩
    intro a ha b hb X
    exact (rootLine_calculation s hu).2.1 a (hA ha) b (hA hb) X

private theorem fixedSpace_eq_line_of_parameter
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s)))
    {u : Field s} (hu : u ≠ 0) (huA : upper s u ∈ A) (hA : A ≤ rootLine s u) :
    fixedSpace H A = fixedSpace H (rootLine s u) := by
  apply le_antisymm
  · intro X hX g
    obtain ⟨k, hk⟩ := (mem_rootLine_iff s u g.val).mp g.property
    change action s g.val X = X
    rw [← hk]
    obtain ⟨hb, hz⟩ := (root_fixed_iff s hu X).mp (hX ⟨_, huA⟩)
    by_cases huk : u * k.val = 0
    · rw [huk]
      change action s (transvection zero_ne_one 0) X = X
      rw [transvection_coeff_zero, map_one, Module.End.one_apply]
    · apply (root_fixed_iff s huk X).mpr
      refine ⟨hb, ?_⟩
      have hkfix : conjugation s k.val = k.val := k.property
      rw [map_mul, hkfix]
      calc
        u * k.val * conjugation s (X.val 0 1) + conjugation s u * k.val * X.val 0 1 =
          k.val * (u * conjugation s (X.val 0 1) + conjugation s u * X.val 0 1) := by ring
        _ = 0 := by rw [hz, mul_zero]
  · intro X hX g
    exact hX ⟨g.val, hA g.property⟩

/-- Every nontrivial subgroup of a fixed-field line fixes its entire K-plane. -/
theorem fixedSpace_eq_rootLine
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s)))
    {u : Field s} (hu : u ≠ 0) (hne : A ≠ ⊥) (hA : A ≤ rootLine s u) :
    fixedSpace H A = fixedSpace H (rootLine s u) := by
  obtain ⟨a, ha, ha1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨v, rfl⟩ := (mem_upperUnipotent _ _).mp (rootLine_le_upper s u (hA ha))
  have hv : v ≠ 0 := by intro h; subst v; exact ha1 (transvection_coeff_zero _)
  have he : rootLine s v = rootLine s u :=
    rootLine_eq_of_common s hv hu hv (upper_mem_rootLine s v) (hA ha)
  rw [← he] at hA ⊢
  exact fixedSpace_eq_line_of_parameter s A hv ha hA

theorem quadratic_fixedCodim
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s)))
    (hAU : A ≤ U) (hne : A ≠ ⊥) (hq : IsQuadratic H A) : fixedCodim H A = 2 * s := by
  obtain ⟨u, hu, hA⟩ := (quadratic_iff_le_rootLine s A hAU hne).mp hq
  unfold fixedCodim
  rw [fixedSpace_eq_rootLine s A hu hne hA]
  exact (rootLine_calculation s hu).2.2.2.1

omit [NeZero s] in
/-- Binary rank increases with subgroup inclusion. -/
theorem inner_rank_mono {A B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s))}
    (hAB : A ≤ B) : rank A ≤ rank B :=
  Nat.log_mono_right (Nat.card_le_card_of_injective (Subgroup.inclusion hAB)
    (Subgroup.inclusion_injective hAB))

omit [NeZero s] in
/-- Equal elementary ranks force equality of nested actors. -/
theorem inner_eq_of_rank_eq {A B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s))}
    (hA : IsElementaryTwo A) (hB : IsElementaryTwo B) (hAB : A ≤ B)
    (hr : rank A = rank B) : A = B := by
  apply Subgroup.eq_of_le_of_card_ge hAB
  rw [hA.card_eq_two_pow_rank, hB.card_eq_two_pow_rank, hr]

/-- The complete quadratic calculation, including its sharp equality case. -/
theorem quadratic_root_calculation
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s)))
    (hAU : A ≤ U) (hne : A ≠ ⊥) (hq : IsQuadratic H A) :
    fixedCodim H A = 2 * s ∧ 2 ≤ actionRatio H A ∧
      (actionRatio H A = 2 ↔ ∃ u : Field s, u ≠ 0 ∧ A = rootLine s u) := by
  obtain ⟨u, hu, hA⟩ := (quadratic_iff_le_rootLine s A hAU hne).mp hq
  have hc := rootLine_calculation s hu
  have hAE : IsElementaryTwo A := (upper_elementary s).of_le hAU hne
  have hd := quadratic_fixedCodim s A hAU hne hq
  have hr : rank A ≤ s := (inner_rank_mono s hA).trans_eq hc.2.2.1
  have hlow : 2 ≤ actionRatio H A := by
    rw [← hc.2.2.2.2, actionRatio, actionRatio, hc.2.2.2.1, hd]
    exact ENNReal.div_le_div_left (by exact_mod_cast inner_rank_mono s hA) _
  refine ⟨hd, hlow, ?_⟩
  constructor
  · intro he
    have he' := (actionRatio_le_nat_iff H hAE 2).mp he.le
    rw [hd] at he'
    have hr' : rank A = s := by omega
    exact ⟨u, hu, inner_eq_of_rank_eq s hAE hc.1 hA (hr'.trans hc.2.2.1.symm)⟩
  · rintro ⟨v, hv, rfl⟩
    exact (rootLine_calculation s hv).2.2.2.2

/-- A nonquadratic actor has ratio at least 3/2, sharply only for the full root group. -/
theorem nonquadratic_root_calculation
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s)))
    (hAU : A ≤ U) (hne : A ≠ ⊥) (hq : ¬ IsQuadratic H A) :
    IsCubic H A ∧ fixedCodim H A = 3 * s ∧ 3 / 2 ≤ actionRatio H A ∧
      (actionRatio H A = 3 / 2 ↔ A = U) := by
  have hd := fixedCodim_eq_of_not_quadratic s A hAU hq
  have hAE := (upper_elementary s).of_le hAU hne
  have hr : rank A ≤ 2 * s := (inner_rank_mono s hAU).trans_eq (upper_rank s)
  have hlow : 3 / 2 ≤ actionRatio H A := by
    rw [← upper_actionRatio s, actionRatio, actionRatio, upper_fixedCodim, hd]
    exact ENNReal.div_le_div_left (by exact_mod_cast inner_rank_mono s hAU) _
  refine ⟨root_subgroup_cubic s A hAU, hd, hlow, ?_⟩
  constructor
  · intro he
    have h0 : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hAE.rank_pos
    rw [actionRatio, hd] at he
    have he' := (ENNReal.div_eq_div_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by simp : (2 : ℝ≥0∞) ≠ ⊤) h0 (by simp)).mp he
    have heN : 2 * (3 * s) = rank A * 3 := by exact_mod_cast he'
    apply inner_eq_of_rank_eq s hAE (upper_elementary s) hAU
    rw [upper_rank]
    omega
  · rintro rfl
    exact upper_actionRatio s

/-- Adjoining a root outside R_t leaves exactly the full root group's fixed K-line. -/
theorem fixedSpace_adjoin_outside_fixedRoot
    (g : Matrix.SpecialLinearGroup (Fin 2) (Field s))
    (hg : g ∈ U) (hout : g ∉ fixedRootGroup s) :
    fixedSpace H (fixedRootGroup s ⊔ Subgroup.zpowers g) = fixedSpace H U ∧
      Module.finrank (fixedField s)
        (Representation.invariants ((action s).comp
          (fixedRootGroup s ⊔ Subgroup.zpowers g).subtype)) = 1 := by
  let A := fixedRootGroup s ⊔ Subgroup.zpowers g
  have hAU : A ≤ U := sup_le inf_le_left (Subgroup.zpowers_le.mpr hg)
  have hn : ¬ IsQuadratic H A := by
    intro hq
    obtain ⟨v, rfl⟩ := (mem_upperUnipotent _ _).mp hg
    have h1 : upper s 1 ∈ A := (show fixedRootGroup s ≤ A from le_sup_left)
      ((mem_fixedRootGroup_iff s _).mpr ⟨1, rfl⟩)
    have hvA : upper s v ∈ A := (show Subgroup.zpowers (upper s v) ≤ A from le_sup_right) (Subgroup.mem_zpowers _)
    have hf := (root_subgroup_quadratic_iff_fixed_ratios s A hAU one_ne_zero h1).mp hq v hvA
    exact hout ((mem_fixedRootGroup_iff s _).mpr ⟨⟨v, by change conjugation s v = v; simpa using hf⟩, rfl⟩)
  have he := fixedSpace_eq_upper_of_not_quadratic s A hAU hn
  refine ⟨he, ?_⟩
  have heK : Representation.invariants ((action s).comp A.subtype) =
      Representation.invariants ((action s).comp (upperUnipotent (Field s)).subtype) := by
    ext X
    exact SetLike.ext_iff.mp he X
  rw [heK, (upperFixedEquivK s).finrank_eq, Module.finrank_self]

end Representation.OrthogonalFourMinus.RankOne
