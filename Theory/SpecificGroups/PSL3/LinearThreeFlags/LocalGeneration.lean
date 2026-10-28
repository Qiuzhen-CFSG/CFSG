module

public import Theory.SpecificGroups.PSL3.LinearThreeFlags.RankTwoGeneration

/-!
# Generation by the two determinant-one local factors

The point torus lies in the line local, and the line torus lies in the point
local. Multiplying a parabolic element by the appropriate torus element
therefore puts it in its determinant-one local. Thus the two locals contain
both parabolics in their join and generate PSL₃, including over the binary
field. This avoids assuming that an inner Borel normalizes an ambient Sylow
subgroup when field automorphisms are present.

Source: Aschbacher--Smith, F.1.12(I)(1), pp.263--264, and the PSL₃ case of
E.1.14(1), p.214; the matrix factorizations are those of `LinearThreeFlags`.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

private theorem pointParabolicSL_le_locals :
    pointParabolicSL F ≤ pointLocalSL F ⊔ lineLocalSL F := by
  intro g hg
  have hg := (mem_pointParabolicSL_iff F g).mp hg
  have hn : g.val 0 0 ≠ 0 := by
    intro hz
    have h := congrArg (fun a : SL(3,F) => a.val 0 0) (inv_mul_cancel g)
    change (g⁻¹.val * g.val) 0 0 = 1 at h
    simp [Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2, hz] at h
  let a := Units.mk0 (g.val 0 0) hn
  let b := pointTorus F a⁻¹
  have hb : b ∈ lineLocalSL F := by
    rw [mem_lineLocalSL_iff]
    simp [b, pointTorus]
  have hl : g * b ∈ pointLocalSL F := by
    rw [mem_pointLocalSL_iff]
    change (g.val * b.val) 0 0 = 1 ∧ (g.val * b.val) 1 0 = 0 ∧
      (g.val * b.val) 2 0 = 0
    simp [b, pointTorus, Matrix.mul_diagonal, a, hg.1, hg.2, hn]
  have h := (pointLocalSL F ⊔ lineLocalSL F).mul_mem
    (mem_sup_left hl) (mem_sup_right ((lineLocalSL F).inv_mem hb))
  simpa using h

private theorem lineParabolicSL_le_locals :
    lineParabolicSL F ≤ pointLocalSL F ⊔ lineLocalSL F := by
  intro g hg
  have hg := (mem_lineParabolicSL_iff F g).mp hg
  have hn : g.val 2 2 ≠ 0 := by
    intro hz
    have h := congrArg (fun a : SL(3,F) => a.val 2 2) (mul_inv_cancel g)
    change (g.val * g⁻¹.val) 2 2 = 1 at h
    simp [Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2, hz] at h
  let a := Units.mk0 (g.val 2 2) hn
  let b := lineTorus F a⁻¹
  have hb : b ∈ pointLocalSL F := by
    rw [mem_pointLocalSL_iff]
    simp [b, lineTorus]
  have hl : g * b ∈ lineLocalSL F := by
    rw [mem_lineLocalSL_iff]
    change (g.val * b.val) 2 0 = 0 ∧ (g.val * b.val) 2 1 = 0 ∧
      (g.val * b.val) 2 2 = 1
    simp [b, lineTorus, Matrix.mul_diagonal, a, hg.1, hg.2, hn]
  have h := (pointLocalSL F ⊔ lineLocalSL F).mul_mem
    (mem_sup_right hl) (mem_sup_left ((pointLocalSL F).inv_mem hb))
  simpa using h

/-- The two actual local factors already generate SL₃, without adding a Borel. -/
theorem localsSL_sup_eq_top : pointLocalSL F ⊔ lineLocalSL F = ⊤ := by
  apply top_unique
  rw [← parabolicsSL_sup_eq_top F]
  exact sup_le (pointParabolicSL_le_locals F) (lineParabolicSL_le_locals F)

/-- The literal projective local factors generate PSL₃ over every finite field. -/
theorem locals_sup_eq_top : pointLocal F ⊔ lineLocal F = ⊤ := by
  rw [pointLocal, lineLocal, ← Subgroup.map_sup, localsSL_sup_eq_top]
  exact Subgroup.map_top_of_surjective _ (projection_surjective F)

end Matrix.PSL3.LinearThree
