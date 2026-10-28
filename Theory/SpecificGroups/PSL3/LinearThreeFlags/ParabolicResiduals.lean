module

public import Theory.SpecificGroups.PSL3.LinearThreeFlags.BorelOvergroups
public import Theory.SpecificGroups.PSL3.LinearThreeLocalStructure

/-!
# Solvable residuals of the degree-three maximal parabolics

The point and line parabolics in SL₃(F) act by scalars on their fixed line
and plane quotient, respectively. The kernels are the perfect local factors
when |F| ≥ 4. The abelian scalar images therefore identify the full
parabolic residuals with those factors. Functoriality of the finite solvable
residual gives the corresponding equalities in the actual PSL₃ quotient.

Properness of both stabilizers upgrades Borel-overgroup coverage to equality
for maximal subgroups. Together these facts identify both classes of
maximal parabolic residuals, without asserting that SL₃ → PSL₃ is injective.

Source: Aschbacher–Smith, A.3.14(1), printed pp.49–50, and the concrete
linear-three local description in F.1.12(I)(1), printed pp.262–264.
-/

public section

open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.ParabolicResiduals
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

/-- The scalar action on the fixed line kills the solvable residual. -/
theorem pointParabolicSL_residual (hF : 4 ≤ Nat.card F) :
    (solvableResidual (pointParabolicSL F)).map (pointParabolicSL F).subtype =
      pointLocalSL F := by
  let := pointLocalSL_isPerfect F hF
  apply le_antisymm _ (le_map_solvableResidual_of_isPerfect _ _ (pointLocalSL_le F))
  rintro _ ⟨x, hx, rfl⟩
  have hh := map_solvableResidual_le (pointScalar F).toHomUnits
    (mem_map_of_mem _ hx)
  rw [solvableResidual_eq_bot, mem_bot] at hh
  have hs : x.val.val 0 0 = 1 := congrArg (fun u : Fˣ => (u : F)) hh
  exact (mem_pointLocalSL_iff F x).mpr
    ⟨hs, (mem_pointParabolicSL_iff F x).mp x.property⟩

/-- The scalar action on the plane quotient kills the solvable residual. -/
theorem lineParabolicSL_residual (hF : 4 ≤ Nat.card F) :
    (solvableResidual (lineParabolicSL F)).map (lineParabolicSL F).subtype =
      lineLocalSL F := by
  let := lineLocalSL_isPerfect F hF
  apply le_antisymm _ (le_map_solvableResidual_of_isPerfect _ _ (lineLocalSL_le F))
  rintro _ ⟨x, hx, rfl⟩
  have hh := map_solvableResidual_le (lineScalar F).toHomUnits
    (mem_map_of_mem _ hx)
  rw [solvableResidual_eq_bot, mem_bot] at hh
  have hs : x.val.val 2 2 = 1 := congrArg (fun u : Fˣ => (u : F)) hh
  have hp := (mem_lineParabolicSL_iff F x).mp x.property
  exact (mem_lineLocalSL_iff F x).mpr ⟨hp.1, hp.2, hs⟩

/-- Residuals descend through the actual central quotient. -/
theorem pointParabolic_residual (hF : 4 ≤ Nat.card F) :
    (solvableResidual (pointParabolic F)).map (pointParabolic F).subtype =
      pointLocal F := by
  have h := map_solvableResidual_comap (projection F) (projection_surjective F)
    (pointParabolic F)
  rw [pointParabolic_comap, pointParabolicSL_residual F hF] at h
  exact h.symm

/-- Residuals descend through the actual central quotient. -/
theorem lineParabolic_residual (hF : 4 ≤ Nat.card F) :
    (solvableResidual (lineParabolic F)).map (lineParabolic F).subtype =
      lineLocal F := by
  have h := map_solvableResidual_comap (projection F) (projection_surjective F)
    (lineParabolic F)
  rw [lineParabolic_comap, lineParabolicSL_residual F hF] at h
  exact h.symm

private theorem point_ne_top : pointParabolicSL F ≠ ⊤ := by
  intro he
  let u : SL(3,F) := SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 0)
    (by decide) (1 : F)
  have h := ((mem_pointParabolicSL_iff F u).mp (he.symm ▸ mem_top u)).1
  simp [u, SpecialLinearGroup.transvection_coe] at h

private theorem line_ne_top : lineParabolicSL F ≠ ⊤ := by
  intro he
  let u : SL(3,F) := SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 1)
    (by decide) (1 : F)
  have h := ((mem_lineParabolicSL_iff F u).mp (he.symm ▸ mem_top u)).2
  simp [u, SpecialLinearGroup.transvection_coe] at h

/-- A maximal standard Borel overgroup in SL₃ is one of the two full parabolics. -/
theorem coatom_over_borelSL (P : Subgroup SL(3,F)) (hP : borelSL F ≤ P)
    (hmax : IsCoatom P) : P = pointParabolicSL F ∨ P = lineParabolicSL F := by
  rcases BorelOvergroups.overgroup_borelSL F P hP hmax.1 with hp | hp
  · exact Or.inl ((hmax.le_iff_eq (point_ne_top F)).mp hp).symm
  · exact Or.inr ((hmax.le_iff_eq (line_ne_top F)).mp hp).symm

/-- A maximal standard Borel overgroup in PSL₃ is one of the two full parabolics. -/
theorem coatom_over_borel (P : Subgroup PSL(3,F)) (hP : borel F ≤ P)
    (hmax : IsCoatom P) : P = pointParabolic F ∨ P = lineParabolic F := by
  have hp : pointParabolic F ≠ ⊤ := by
    intro he
    apply point_ne_top F
    rw [← pointParabolic_comap F, he, comap_top]
  have hl : lineParabolic F ≠ ⊤ := by
    intro he
    apply line_ne_top F
    rw [← lineParabolic_comap F, he, comap_top]
  rcases BorelOvergroups.overgroup_borel F P hP hmax.1 with h | h
  · exact Or.inl ((hmax.le_iff_eq hp).mp h).symm
  · exact Or.inr ((hmax.le_iff_eq hl).mp h).symm

end Matrix.PSL3.LinearThree.ParabolicResiduals
