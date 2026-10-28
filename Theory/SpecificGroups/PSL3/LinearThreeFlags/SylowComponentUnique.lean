module
public import Theory.SpecificGroups.SL2.SylowOvergroupComponentUnique
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSubgroups
public import Theory.SpecificGroups.PSL3Two.SolvableSylowOvergroups

/-!
# Unique C-components in binary PSL₃ Sylow overgroups

Parabolic placement reduces to the vector and covector stabilizers. Their
literal two-core quotients are SL₂ over the original field. The field of
two elements is handled by the solvable proper-overgroup calculation.
Source: Aschbacher--Smith A.3.12, pp.47--48; 1.2.8(1), p.506.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
theorem pointParabolic_sylow_component_unique (hF : 4 ≤ Nat.card F) :
    SylowOvergroupComponentUnique (pointParabolic F) := by
  apply SylowOvergroupComponentUnique.of_residual_image _ _ (PerfectSubgroups.pointParabolic_residual F hF)
  let : Group.IsNilpotent (pCore 2 (pointLocal F)) := pCore_isNilpotent
  apply SylowOvergroupComponentUnique.of_quotient (pCore 2 (pointLocal F))
  exact SylowOvergroupComponentUnique.of_equiv (pointLocalCoreQuotientEquiv F)
    (Matrix.SpecialLinearGroup.sylow_overgroup_component_unique F)

theorem lineParabolic_sylow_component_unique (hF : 4 ≤ Nat.card F) :
    SylowOvergroupComponentUnique (lineParabolic F) := by
  apply SylowOvergroupComponentUnique.of_residual_image _ _ (PerfectSubgroups.lineParabolic_residual F hF)
  let : Group.IsNilpotent (pCore 2 (lineLocal F)) := pCore_isNilpotent
  apply SylowOvergroupComponentUnique.of_quotient (pCore 2 (lineLocal F))
  exact SylowOvergroupComponentUnique.of_equiv (lineLocalCoreQuotientEquiv F)
    (Matrix.SpecialLinearGroup.sylow_overgroup_component_unique F)

theorem sylow_overgroup_component_unique [IsSimpleGroup PSL(3,F)] [Group.IsPerfect PSL(3,F)]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1≤n) : SylowOvergroupComponentUnique PSL(3,F) := by
  by_cases h1 : n = 1
  · subst n
    apply SylowOvergroupComponentUnique.of_solvable_proper_overgroups
    exact Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two (by simpa using hF)
  apply SylowOvergroupComponentUnique.of_proper_conjugate_cover
  intro S P hSP hP
  obtain ⟨g,hg⟩ := UnipotentOvergroups.proper_sylow_overgroup_parabolic_cover F hn hF S P hSP hP
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  rcases hg with hg | hg
  · exact ⟨g,pointParabolic F,hg,pointParabolic_sylow_component_unique F hfour⟩
  · exact ⟨g,lineParabolic F,hg,lineParabolic_sylow_component_unique F hfour⟩
end Matrix.PSL3.LinearThree
