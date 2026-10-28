module
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.RankTwoGeneration
public import Theory.SpecificGroups.PSL3.LinearThreeLocalStructure
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.BorelOvergroups
public import Theory.SpecificGroups.PSL2.AutomorphismModel


/-!
# Solvable residuals of the degree-three flag parabolics

For a finite field with at least four elements, the solvable residuals of
its point and line parabolics in SL₃ are exactly the vector and covector
stabilizers. Their scalar characters have abelian image, whereas the
stabilizers are perfect affine groups. These two residuals generate SL₃:
the missing scalar action of either parabolic already lies in the other
local factor, so rank-two flag generation applies.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the SL₃ case
of 13.6.19, printed p.931. This intrinsic result does not identify a
parabolic preimage in an ambient extension, or its action on a module.
-/

public section

open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

private def pointScalar : pointParabolicSL F →* F where
  toFun g := g.val.val 0 0
  map_one' := by simp
  map_mul' g h := by
    have hh := (mem_pointParabolicSL_iff F h).mp h.property
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hh.1, hh.2]

private def lineScalar : lineParabolicSL F →* F where
  toFun g := g.val.val 2 2
  map_one' := by simp
  map_mul' g h := by
    have hg := (mem_lineParabolicSL_iff F g).mp g.property
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2]

theorem pointParabolicSL_residual (hcard : 4 ≤ Nat.card F) :
    (solvableResidual (pointParabolicSL F)).map (pointParabolicSL F).subtype =
      pointLocalSL F := by
  apply le_antisymm
  · have h := map_solvableResidual_le (pointScalar F).toHomUnits
    rw [solvableResidual_eq_bot (G := Fˣ), le_bot_iff, Subgroup.map_eq_bot_iff] at h
    rintro g ⟨x, hx, rfl⟩
    have he := congrArg (fun a : Fˣ => (a : F)) (h hx)
    have hp := (mem_pointParabolicSL_iff F x).mp x.property
    exact (mem_pointLocalSL_iff F x).mpr ⟨he, hp⟩
  · let := pointLocalSL_isPerfect F hcard
    exact le_map_solvableResidual_of_isPerfect _ _ (pointLocalSL_le F)

theorem lineParabolicSL_residual (hcard : 4 ≤ Nat.card F) :
    (solvableResidual (lineParabolicSL F)).map (lineParabolicSL F).subtype =
      lineLocalSL F := by
  apply le_antisymm
  · have h := map_solvableResidual_le (lineScalar F).toHomUnits
    rw [solvableResidual_eq_bot (G := Fˣ), le_bot_iff, Subgroup.map_eq_bot_iff] at h
    rintro g ⟨x, hx, rfl⟩
    have he := congrArg (fun a : Fˣ => (a : F)) (h hx)
    have hp := (mem_lineParabolicSL_iff F x).mp x.property
    exact (mem_lineLocalSL_iff F x).mpr ⟨hp.1, hp.2, he⟩
  · let := lineLocalSL_isPerfect F hcard
    exact le_map_solvableResidual_of_isPerfect _ _ (lineLocalSL_le F)

private theorem point_le_locals :
    pointParabolicSL F ≤ pointLocalSL F ⊔ lineLocalSL F := by
  intro g hg
  have hp := (mem_pointParabolicSL_iff F g).mp hg
  have hn : g.val 0 0 ≠ 0 := by
    intro hz
    have h := congrArg (fun a : SL(3, F) => a.val 0 0) (inv_mul_cancel g)
    change (g⁻¹.val * g.val) 0 0 = 1 at h
    simp [Matrix.mul_apply, Fin.sum_univ_three, hp.1, hp.2, hz] at h
  let a := Units.mk0 (g.val 0 0) hn
  let b := pointTorus F a⁻¹
  have hb : b ∈ lineLocalSL F := by
    rw [mem_lineLocalSL_iff]
    simp [b, pointTorus]
  have hl : g * b ∈ pointLocalSL F := by
    rw [mem_pointLocalSL_iff]
    change (g.val * b.val) 0 0 = 1 ∧ (g.val * b.val) 1 0 = 0 ∧
      (g.val * b.val) 2 0 = 0
    simp [b, pointTorus, Matrix.mul_diagonal, a, hp.1, hp.2, hn]
  simpa only [mul_inv_cancel_right] using
    (pointLocalSL F ⊔ lineLocalSL F).mul_mem (mem_sup_left hl)
      (mem_sup_right ((lineLocalSL F).inv_mem hb))

private theorem line_le_locals :
    lineParabolicSL F ≤ pointLocalSL F ⊔ lineLocalSL F := by
  intro g hg
  have hp := (mem_lineParabolicSL_iff F g).mp hg
  have hn : g.val 2 2 ≠ 0 := by
    intro hz
    have h := congrArg (fun a : SL(3, F) => a.val 2 2) (mul_inv_cancel g)
    change (g.val * g⁻¹.val) 2 2 = 1 at h
    simp [Matrix.mul_apply, Fin.sum_univ_three, hp.1, hp.2, hz] at h
  let a := Units.mk0 (g.val 2 2) hn
  let b := lineTorus F a⁻¹
  have hb : b ∈ pointLocalSL F := by
    rw [mem_pointLocalSL_iff]
    simp [b, lineTorus]
  have hl : g * b ∈ lineLocalSL F := by
    rw [mem_lineLocalSL_iff]
    change (g.val * b.val) 2 0 = 0 ∧ (g.val * b.val) 2 1 = 0 ∧
      (g.val * b.val) 2 2 = 1
    simp [b, lineTorus, Matrix.mul_diagonal, a, hp.1, hp.2, hn]
  simpa only [mul_inv_cancel_right] using
    (pointLocalSL F ⊔ lineLocalSL F).mul_mem (mem_sup_right hl)
      (mem_sup_left ((pointLocalSL F).inv_mem hb))

theorem localsSL_sup_eq_top : pointLocalSL F ⊔ lineLocalSL F = ⊤ := by
  apply top_unique
  rw [← parabolicsSL_sup_eq_top F]
  exact sup_le (point_le_locals F) (line_le_locals F)

theorem parabolicResidualsSL_sup_eq_top (hcard : 4 ≤ Nat.card F) :
    (solvableResidual (pointParabolicSL F)).map (pointParabolicSL F).subtype ⊔
      (solvableResidual (lineParabolicSL F)).map (lineParabolicSL F).subtype = ⊤ := by
  rw [pointParabolicSL_residual F hcard, lineParabolicSL_residual F hcard,
    localsSL_sup_eq_top]

private theorem point_not_le_line : ¬ pointParabolicSL F ≤ lineParabolicSL F := by
  intro h
  let g := SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : F)
  have hg : g ∈ pointParabolicSL F := by
    rw [mem_pointParabolicSL_iff]
    simp [g, SpecialLinearGroup.transvection_coe]
  have he := (mem_lineParabolicSL_iff F g).mp (h hg)
  simpa [g, SpecialLinearGroup.transvection_coe] using he.2

private theorem line_not_le_point : ¬ lineParabolicSL F ≤ pointParabolicSL F := by
  intro h
  let g := SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : F)
  have hg : g ∈ lineParabolicSL F := by
    rw [mem_lineParabolicSL_iff]
    simp [g, SpecialLinearGroup.transvection_coe]
  have he := (mem_pointParabolicSL_iff F g).mp (h hg)
  simpa [g, SpecialLinearGroup.transvection_coe] using he.1

/-- The standard point stabilizer is a maximal proper subgroup of SL₃. -/
theorem pointParabolicSL_isCoatom : IsCoatom (pointParabolicSL F) := by
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨fun h => line_not_le_point F (h ▸ le_top), ?_⟩
  intro H hH hp
  rcases BorelOvergroups.overgroup_borelSL F H (inf_le_left.trans hp) hH with h | h
  · exact h
  · exact (point_not_le_line F (hp.trans h)).elim

/-- The standard plane stabilizer is a maximal proper subgroup of SL₃. -/
theorem lineParabolicSL_isCoatom : IsCoatom (lineParabolicSL F) := by
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨fun h => point_not_le_line F (h ▸ le_top), ?_⟩
  intro H hH hp
  rcases BorelOvergroups.overgroup_borelSL F H (inf_le_right.trans hp) hH with h | h
  · exact (line_not_le_point F (hp.trans h)).elim
  · exact h

variable [CharP F 2]

/-- The intrinsic two-core quotient of the embedded point-parabolic residual. -/
noncomputable def pointParabolicSLResidualCoreEquiv (hcard : 4 ≤ Nat.card F) :
    ((solvableResidual (pointParabolicSL F)).map (pointParabolicSL F).subtype ⧸
      pCore 2 ((solvableResidual (pointParabolicSL F)).map (pointParabolicSL F).subtype)) ≃*
      PSL(2, F) :=
  let e := MulEquiv.subgroupCongr (pointParabolicSL_residual F hcard)
  (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    ((pointLocalSLCoreQuotientEquiv F).trans (Theory.PSL2.sl2QuotientEquiv F))

/-- The intrinsic two-core quotient of the embedded line-parabolic residual. -/
noncomputable def lineParabolicSLResidualCoreEquiv (hcard : 4 ≤ Nat.card F) :
    ((solvableResidual (lineParabolicSL F)).map (lineParabolicSL F).subtype ⧸
      pCore 2 ((solvableResidual (lineParabolicSL F)).map (lineParabolicSL F).subtype)) ≃*
      PSL(2, F) :=
  let e := MulEquiv.subgroupCongr (lineParabolicSL_residual F hcard)
  (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    ((lineLocalSLCoreQuotientEquiv F).trans (Theory.PSL2.sl2QuotientEquiv F))
end Matrix.PSL3.LinearThree
