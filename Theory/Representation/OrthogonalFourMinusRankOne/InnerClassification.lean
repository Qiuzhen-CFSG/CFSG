module

public import Theory.Representation.OrthogonalFourMinusRankOne.InnerClassification.RootCalculations

/-!
# Inner actors on the Hermitian orthogonal module

Every elementary two-subgroup of SL₂(2²ˢ) is transported into the canonical
Sylow root group. The fixed-field line calculation then gives the exact
quadratic minimum two and cubic minimum 3/2. Quadratic threshold actors are
precisely conjugates of R_t; cubic minimizers are precisely Sylow root groups.
The latter are automatically minimal among minimizing actors.

Source: Aschbacher–Smith, K.3.1.2, printed p.454, and D.2.1, printed p.178.
The statements hold for all positive s, including s=1.
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
local notation "SL" => Matrix.SpecialLinearGroup (Fin 2) (Field s)

omit [NeZero s] in
/-- Sylow transport to the literal canonical root group. -/
theorem elementary_root_transport (A : Subgroup SL) (hA : IsElementaryTwo A) :
    ∃ (g : SL) (B : Subgroup SL), B ≤ U ∧ IsElementaryTwo B ∧
      A = B.map (MulAut.conj g).toMonoidHom := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨P, hP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL (upperUnipotentSylow (Field s) 2) P
  have hPe : (P : Subgroup SL) = (upperUnipotent (Field s)).map (MulAut.conj g).toMonoidHom := by rw [← hg]; rfl
  let B := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hcancel (C : Subgroup SL) :
      (C.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = C := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hBU : B ≤ U := by
    have hh := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hP
    rw [hPe, hcancel] at hh
    exact hh
  refine ⟨g, B, hBU, hA.map_conj g⁻¹, ?_⟩
  ext x
  simp [B, MulAut.conj_apply, mul_assoc]

/-- Every elementary inner actor is cubic. -/
theorem inner_elementary_cubic (A : Subgroup SL) (hA : IsElementaryTwo A) : IsCubic H A := by
  obtain ⟨g, B, hBU, _, rfl⟩ := elementary_root_transport s A hA
  exact (InnerTransport.cubic_conj_iff _ _ _).mpr (root_subgroup_cubic s B hBU)

/-- The sharp quadratic lower bound, with the binary fixed codimension. -/
theorem inner_quadratic_bound (A : Subgroup SL) (hA : IsElementaryTwo A)
    (hq : IsQuadratic H A) : fixedCodim H A = 2 * s ∧ 2 ≤ actionRatio H A := by
  obtain ⟨g, B, hBU, hB, rfl⟩ := elementary_root_transport s A hA
  have hqB := (InnerTransport.quadratic_conj_iff _ _ _).mp hq
  have hc := quadratic_root_calculation s B hBU hB.1 hqB
  rw [fixedCodim_map_conj, InnerTransport.ratio_conj]
  exact ⟨hc.1, hc.2.1⟩

/-- All elementary inner actors satisfy the cubic lower bound. -/
theorem inner_ratio_bound (A : Subgroup SL) (hA : IsElementaryTwo A) :
    3 / 2 ≤ actionRatio H A := by
  by_cases hq : IsQuadratic H A
  · exact (by
      rw [ENNReal.div_le_iff (by norm_num) (by simp)]
      norm_num : (3 / 2 : ℝ≥0∞) ≤ 2).trans (inner_quadratic_bound s A hA hq).2
  · obtain ⟨g, B, hBU, hB, rfl⟩ := elementary_root_transport s A hA
    have hn : ¬ IsQuadratic H B := fun h => hq ((InnerTransport.quadratic_conj_iff _ _ _).mpr h)
    rw [InnerTransport.ratio_conj]
    exact (nonquadratic_root_calculation s B hBU hB.1 hn).2.2.1

/-- Nonquadratic inner actors have the full root fixed codimension. -/
theorem inner_nonquadratic_bound (A : Subgroup SL) (hA : IsElementaryTwo A)
    (hn : ¬ IsQuadratic H A) : fixedCodim H A = 3 * s ∧ 3 / 2 ≤ actionRatio H A := by
  obtain ⟨g, B, hBU, hB, rfl⟩ := elementary_root_transport s A hA
  have hnB : ¬ IsQuadratic H B :=
    fun h => hn ((InnerTransport.quadratic_conj_iff _ _ _).mpr h)
  rw [fixedCodim_map_conj, InnerTransport.ratio_conj]
  have hc := nonquadratic_root_calculation s B hBU hB.1 hnB
  exact ⟨hc.2.1, hc.2.2.1⟩

/-- The exact source minima on the whole inner group, including s=1. -/
theorem inner_ratios : quadraticRatio H = 2 ∧ cubicRatio H = 3 / 2 := by
  have hu := ratio_upper_bounds s
  constructor
  · apply le_antisymm hu.1
    exact le_iInf fun A => le_iInf fun hA => (inner_quadratic_bound s A hA.1 hA.2).2
  · apply le_antisymm hu.2
    exact le_iInf fun A => le_iInf fun hA => inner_ratio_bound s A hA.1

/-- D.2.1's quadratic threshold family consists exactly of conjugates of R_t. -/
theorem inner_quadratic_threshold_iff (A : Subgroup SL) :
    (IsElementaryTwo A ∧ IsQuadratic H A ∧ actionRatio H A ≤ 2) ↔
      ∃ g : SL, A = (fixedRootGroup s).map (MulAut.conj g).toMonoidHom := by
  constructor
  · rintro ⟨hA, hq, hr⟩
    obtain ⟨g, B, hBU, hB, hAB⟩ := elementary_root_transport s A hA
    rw [hAB, InnerTransport.quadratic_conj_iff] at hq
    rw [hAB, InnerTransport.ratio_conj] at hr
    have hc := quadratic_root_calculation s B hBU hB.1 hq
    obtain ⟨u, hu, hBu⟩ := hc.2.2.mp (le_antisymm hr hc.2.1)
    obtain ⟨k, _, hk⟩ := rootLine_eq_normalizer_conjugate s hu
    refine ⟨g * k, ?_⟩
    rw [hAB, hBu, hk, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨g, rfl⟩
    exact ⟨(fixedRoot_elementary s).map_conj g,
      (InnerTransport.quadratic_conj_iff _ _ _).mpr (fixedRoot_quadratic s),
      le_of_eq ((InnerTransport.ratio_conj _ _ _).trans (fixedRoot_actionRatio s))⟩

/-- Threshold and minimum coincide for the inner quadratic actors. -/
theorem inner_quadratic_minimizer_iff (A : Subgroup SL) :
    (IsElementaryTwo A ∧ IsQuadratic H A ∧ actionRatio H A = quadraticRatio H) ↔
      ∃ g : SL, A = (fixedRootGroup s).map (MulAut.conj g).toMonoidHom := by
  rw [(inner_ratios s).1]
  constructor
  · rintro ⟨he, hq, hr⟩
    exact (inner_quadratic_threshold_iff s A).mp ⟨he, hq, hr.le⟩
  · intro h
    obtain ⟨he, hq, hr⟩ := (inner_quadratic_threshold_iff s A).mpr h
    exact ⟨he, hq, le_antisymm hr (inner_quadratic_bound s A he hq).2⟩

/-- The cubic minimum is attained precisely on the conjugate full root groups. -/
theorem inner_cubic_minimizer_iff (A : Subgroup SL) :
    (IsElementaryTwo A ∧ IsCubic H A ∧ actionRatio H A = cubicRatio H) ↔
      ∃ g : SL, A = (upperUnipotent (Field s)).map (MulAut.conj g).toMonoidHom := by
  rw [(inner_ratios s).2]
  constructor
  · rintro ⟨hA, _, hr⟩
    have hn : ¬ IsQuadratic H A := by
      intro hq
      have hh := (inner_quadratic_bound s A hA hq).2
      rw [hr] at hh
      have hh' := (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by simp))).mp hh
      norm_num at hh'
    obtain ⟨g, B, hBU, hB, hAB⟩ := elementary_root_transport s A hA
    have hnB : ¬ IsQuadratic H B := by
      intro hq
      apply hn
      rw [hAB]
      exact (InnerTransport.quadratic_conj_iff _ _ _).mpr hq
    rw [hAB, InnerTransport.ratio_conj] at hr
    have hBUeq := (nonquadratic_root_calculation s B hBU hB.1 hnB).2.2.2.mp hr
    exact ⟨g, hBUeq ▸ hAB⟩
  · rintro ⟨g, rfl⟩
    exact ⟨(upper_elementary s).map_conj g,
      (InnerTransport.cubic_conj_iff _ _ _).mpr (root_subgroup_cubic s U le_rfl),
      (InnerTransport.ratio_conj _ _ _).trans (upper_actionRatio s)⟩

/-- In particular all cubic minimizing actors are minimal under inclusion (Q̂*). -/
theorem inner_cubic_minimizer_minimal {A B : Subgroup SL}
    (hA : IsElementaryTwo A ∧ IsCubic H A ∧ actionRatio H A = cubicRatio H)
    (hB : IsElementaryTwo B ∧ IsCubic H B ∧ actionRatio H B = cubicRatio H)
    (hBA : B ≤ A) : B = A := by
  obtain ⟨g, hg⟩ := (inner_cubic_minimizer_iff s A).mp hA
  obtain ⟨k, hk⟩ := (inner_cubic_minimizer_iff s B).mp hB
  apply inner_eq_of_rank_eq s hB.1 hA.1 hBA
  rw [hg, hk, rank_map_conj, rank_map_conj]

end Representation.OrthogonalFourMinus.RankOne
