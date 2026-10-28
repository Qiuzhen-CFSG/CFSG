module

public import Theory.SpecificGroups.PSL3.LinearThreeFlags

/-!
# Relative normality of the two PSL₃ local factors

A point parabolic preserves the first coordinate line, so conjugation preserves
the subgroup fixing its first vector. Dually, the line parabolic normalizes
the subgroup fixing the last coordinate covector. The matrix calculations
below prove these assertions before mapping through the central projection.

These are the relative normality inputs to the rank-one argument on printed
p.511 (PDF p.528) of Aschbacher–Smith, `refs/quasithin.pdf`.
-/

public section

open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement.ParabolicBorel
variable (F : Type*) [Field F] [Finite F]

private theorem pointParabolicSL_le_normalizer_local :
    pointParabolicSL F ≤ normalizer (pointLocalSL F : Set SL(3,F)) := by
  apply le_normalizer_iff.mpr
  intro g hg u hu
  obtain ⟨g10,g20⟩ := (mem_pointParabolicSL_iff F g).mp hg
  obtain ⟨i10,i20⟩ := (mem_pointParabolicSL_iff F g⁻¹).mp ((pointParabolicSL F).inv_mem hg)
  obtain ⟨u00,u10,u20⟩ := (mem_pointLocalSL_iff F u).mp hu
  have h00 := congrArg (fun a : SL(3,F) => a.val 0 0) (mul_inv_cancel g)
  change (g.val * g⁻¹.val) 0 0 = 1 at h00
  simp only [mul_apply, Fin.sum_univ_three, i10,i20,mul_zero,add_zero] at h00
  rw [mem_pointLocalSL_iff]
  change (g.val * u.val * g⁻¹.val) 0 0 = 1 ∧
    (g.val * u.val * g⁻¹.val) 1 0 = 0 ∧ (g.val * u.val * g⁻¹.val) 2 0 = 0
  simp only [mul_apply, Fin.sum_univ_three,
    u00,u10,u20,g10,g20,i10,i20,mul_zero,zero_mul,mul_one,add_zero,zero_add,h00]
  trivial

private theorem lineParabolicSL_le_normalizer_local :
    lineParabolicSL F ≤ normalizer (lineLocalSL F : Set SL(3,F)) := by
  apply le_normalizer_iff.mpr
  intro g hg u hu
  obtain ⟨g20,g21⟩ := (mem_lineParabolicSL_iff F g).mp hg
  obtain ⟨i20,i21⟩ := (mem_lineParabolicSL_iff F g⁻¹).mp ((lineParabolicSL F).inv_mem hg)
  obtain ⟨u20,u21,u22⟩ := (mem_lineLocalSL_iff F u).mp hu
  have h22 := congrArg (fun a : SL(3,F) => a.val 2 2) (mul_inv_cancel g)
  change (g.val * g⁻¹.val) 2 2 = 1 at h22
  simp only [mul_apply, Fin.sum_univ_three, g20,g21,zero_mul,zero_add] at h22
  rw [mem_lineLocalSL_iff]
  change (g.val * u.val * g⁻¹.val) 2 0 = 0 ∧
    (g.val * u.val * g⁻¹.val) 2 1 = 0 ∧ (g.val * u.val * g⁻¹.val) 2 2 = 1
  simp only [mul_apply, Fin.sum_univ_three,
    u20,u21,u22,g20,g21,i20,i21,mul_zero,zero_mul,mul_one,add_zero,zero_add,h22]
  trivial

/-- The point parabolic normalizes the actual vector-fixing local subgroup. -/
theorem pointParabolic_le_normalizer_local :
    pointParabolic F ≤ normalizer (pointLocal F : Set PSL(3,F)) :=
  (map_mono (pointParabolicSL_le_normalizer_local F)).trans
    ((pointLocalSL F).le_normalizer_map (projection F))

/-- The line parabolic normalizes the actual covector-fixing local subgroup. -/
theorem lineParabolic_le_normalizer_local :
    lineParabolic F ≤ normalizer (lineLocal F : Set PSL(3,F)) :=
  (map_mono (lineParabolicSL_le_normalizer_local F)).trans
    ((lineLocalSL F).le_normalizer_map (projection F))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement.ParabolicBorel
