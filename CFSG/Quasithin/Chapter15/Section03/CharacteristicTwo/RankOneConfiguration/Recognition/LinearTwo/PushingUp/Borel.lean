module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Local
public import Theory.SpecificGroups.SL2.SylowConsequences

public import CFSG.Quasithin.ChapterB.Section06To07.Elementary

/-!
# The matrix Borel needed for pushing up the L₂ branch

An overgroup of the full upper root group containing an element outside
its normalizer also contains a Weyl element and the full lower root group.
Transvection generation then makes it the whole special linear group.
Consequently the Borel is the unique maximal overgroup of the root group.
In defining characteristic, every two-subgroup of the Borel lies in its
upper root group. This identifies the actual Sylow image in a marked Borel.

These model calculations alone do not lift through the source action kernel.
That transport is required before applying them to L intersect S or to I.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the Borel
calculation in 15.3.30, printed p.1131, and Definition B.6.1, p.112.
-/

@[expose] public section

open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
open Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]
local notation "u" => Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one
local notation "v" => Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero

private def weyl (c : F) (hc : c ≠ 0) : SL(2, F) :=
  ⟨!![0, -c⁻¹; c, 0], by simp [det_fin_two, hc]⟩

private theorem weyl_factor (g : SL(2, F)) (hc : g.val 1 0 ≠ 0) :
    u (-(g.val 0 0) / g.val 1 0) * g * u (-(g.val 1 1) / g.val 1 0) =
      weyl (g.val 1 0) hc := by
  have hd := g.property
  rw [det_fin_two] at hd
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, transvection_coe, weyl]
  all_goals field_simp [hc]
  all_goals first | ring1 | linear_combination -hd

private theorem weyl_conj_upper (c : F) (hc : c ≠ 0) (t : F) :
    weyl c hc * u (-(t / c ^ 2)) * (weyl c hc)⁻¹ = v t := by
  apply Subtype.ext
  change (!![0, -c⁻¹; c, 0] * (u (-(t / c ^ 2))).val) *
    adjugate !![0, -c⁻¹; c, 0] = (v t).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, transvection_coe, adjugate_fin_two, vecMul, dotProduct]
  all_goals field_simp [hc]

/-- Every proper overgroup of the full root group lies in its Borel. -/
theorem proper_overgroup_upper_le_borel (H : Subgroup (SL(2, F)))
    (hUH : upperUnipotent F ≤ H) (hH : H ≠ ⊤) : H ≤ rankOneBorel F := by
  intro g hg
  by_contra hn
  have hc : g.val 1 0 ≠ 0 := by simpa only [mem_rankOneBorel_iff] using hn
  have hu (t : F) : u t ∈ H := hUH ((mem_upperUnipotent F _).mpr ⟨t, rfl⟩)
  have hw : weyl (g.val 1 0) hc ∈ H := by
    rw [← weyl_factor g hc]
    exact H.mul_mem (H.mul_mem (hu _) hg) (hu _)
  have hv (t : F) : v t ∈ H := by
    rw [← weyl_conj_upper (g.val 1 0) hc t]
    exact H.mul_mem (H.mul_mem hw (hu _)) (H.inv_mem hw)
  apply hH
  apply top_unique
  intro x _
  apply SL2.transvection_induction (fun x => x ∈ H) ?_ (fun _ _ => H.mul_mem) x
  intro i j hij t
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact hu t
  · exact hv t
  · exact (hij rfl).elim


theorem rankOneBorel_ne_top : rankOneBorel F ≠ ⊤ := by
  intro h
  exact upperUnipotent_not_normal F (normalizer_eq_top_iff.mp h)

theorem rankOneBorel_isCoatom : IsCoatom (rankOneBorel F) := by
  apply isCoatom_iff_ge_of_le.mpr
  exact ⟨rankOneBorel_ne_top, fun H hH hBH =>
    proper_overgroup_upper_le_borel H ((upperUnipotent F).le_normalizer.trans hBH) hH⟩

theorem rankOneBorel_unique_maximal :
    ∃! B : Subgroup (SL(2, F)), IsCoatom B ∧ upperUnipotent F ≤ B := by
  refine ⟨rankOneBorel F, ⟨rankOneBorel_isCoatom, (upperUnipotent F).le_normalizer⟩, ?_⟩
  intro B hB
  have hle := proper_overgroup_upper_le_borel B hB.2 hB.1.ne_top
  exact le_antisymm hle ((isCoatom_iff_ge_of_le.mp hB.1).2 _ rankOneBorel_ne_top hle)

variable [Finite F] [CharP F 2]

theorem two_subgroup_borel_le_upper (Q : Subgroup (SL(2, F)))
    (hQ : IsPGroup 2 Q) (hQB : Q ≤ rankOneBorel F) : Q ≤ upperUnipotent F := by
  have h := hQ.inf_normalizer_sylow (upperUnipotentSylow F 2)
  change Q ⊓ rankOneBorel F = Q ⊓ upperUnipotent F at h
  rw [inf_eq_left.mpr hQB] at h
  exact h.le.trans inf_le_right

theorem sylow_in_borel_eq_upper (Q : Sylow 2 (SL(2, F)))
    (hQB : (Q : Subgroup (SL(2, F))) ≤ rankOneBorel F) :
    (Q : Subgroup (SL(2, F))) = upperUnipotent F := by
  exact (Q.is_maximal' (upperUnipotentSylow F 2).isPGroup'
    (two_subgroup_borel_le_upper _ Q.isPGroup' hQB)).symm

/-- B.6.1 for the actual linear group, with its canonical Sylow subgroup. -/
theorem linear_minimalParabolic :
    ChapterB.IsMinimalParabolicOver (upperUnipotentSylow F 2) ⊤ := by
  apply (ChapterB.isMinimalParabolicOver_top_iff _).mpr
  exact ⟨rankOneBorel_unique_maximal, upperUnipotent_not_normal F⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp

end
