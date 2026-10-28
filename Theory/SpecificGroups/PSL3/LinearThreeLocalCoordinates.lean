module

public import Theory.SpecificGroups.PSL3.LinearThreeLocalStructure

/-!
# Marked coordinates of the degree-three local factors

The affine isomorphisms retain the literal two-by-two matrix blocks. In
characteristic two, reversal after contragredience identifies the point
radical's row `(x,y)` with the natural column `(y,x)`, and the linear part
is the original lower-right block. The line coordinates are already natural.
The quotient formulas below use the actual projection to PSL₃.

We also express perfectness as equality of the ambient image of the solvable
residual with the local subgroup, retaining its inclusion into PSL₃.

Source: Aschbacher–Smith, F.1.12(I)(1),(II), printed pp.262–264.
-/

public section

open Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree

variable (F : Type*) [Field F]

/-- The line affine quotient is its upper-left determinant-one block. -/
theorem lineLocalAffineEquiv_right_val (g : lineLocalSL F) :
    (lineLocalAffineEquiv F g).right.val =
      !![g.val.val 0 0, g.val.val 0 1; g.val.val 1 0, g.val.val 1 1] := rfl

/-- Line translations retain their original column coordinates. -/
theorem lineLocalAffineEquiv_left (g : lineLocalSL F) :
    Multiplicative.toAdd (lineLocalAffineEquiv F g).left =
      ![g.val.val 0 2, g.val.val 1 2] := rfl

variable [CharP F 2]

/-- In characteristic two the duality marking keeps the original point Levi block. -/
theorem pointLocalAffineEquiv_right_val (g : pointLocalSL F) :
    (pointLocalAffineEquiv F g).right.val =
      !![g.val.val 1 1, g.val.val 1 2; g.val.val 2 1, g.val.val 2 2] := by
  have hg := (mem_pointLocalSL_iff F g.val).mp g.property
  change !![g.val⁻¹.val 2 2, g.val⁻¹.val 1 2;
    g.val⁻¹.val 2 1, g.val⁻¹.val 1 1] = _
  simp [SpecialLinearGroup.coe_inv, adjugate_fin_three,
    hg.1, hg.2.1, hg.2.2, CharTwo.neg_eq]

/-- The point root row is identified with the reversed natural column. -/
theorem pointLocalAffineEquiv_left_of_mem_radical (g : pointLocalSL F)
    (hg : g ∈ pointRadicalSL F) :
    Multiplicative.toAdd (pointLocalAffineEquiv F g).left =
      ![g.val.val 0 2, g.val.val 0 1] := by
  have hr := (mem_pointRadicalSL_iff F g).mp hg
  change ![g.val⁻¹.val 0 2, g.val⁻¹.val 0 1] = _
  simp [SpecialLinearGroup.coe_inv, adjugate_fin_three,
    hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, CharTwo.neg_eq]

variable [Finite F]

/-- The literal point-local quotient map reads the original lower-right block. -/
theorem pointLocalCoreQuotientEquiv_project_val (g : pointLocalSL F) :
    (pointLocalCoreQuotientEquiv F
      (QuotientGroup.mk' (pCore 2 (pointLocal F)) (pointLocalProjectEquiv F g))).val =
      !![g.val.val 1 1, g.val.val 1 2; g.val.val 2 1, g.val.val 2 2] := by
  rw [pointLocalCoreQuotientEquiv_mk, pointLocalEquivAffine_project]
  exact pointLocalAffineEquiv_right_val F g

/-- The literal line-local quotient map reads the original upper-left block. -/
theorem lineLocalCoreQuotientEquiv_project_val (g : lineLocalSL F) :
    (lineLocalCoreQuotientEquiv F
      (QuotientGroup.mk' (pCore 2 (lineLocal F)) (lineLocalProjectEquiv F g))).val =
      !![g.val.val 0 0, g.val.val 0 1; g.val.val 1 0, g.val.val 1 1] := by
  rw [lineLocalCoreQuotientEquiv_mk, lineLocalEquivAffine_project]
  exact lineLocalAffineEquiv_right_val F g

omit [CharP F 2] in
/-- The point-local equality L∞ = L as subgroups of the actual projective group. -/
theorem pointLocal_map_solvableResidual (hcard : 4 ≤ Nat.card F) :
    (Subgroup.solvableResidual (pointLocal F)).map (pointLocal F).subtype =
      pointLocal F := by
  rw [pointLocal_solvableResidual_eq_top F hcard, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

omit [CharP F 2] in
/-- The line-local equality L∞ = L as subgroups of the actual projective group. -/
theorem lineLocal_map_solvableResidual (hcard : 4 ≤ Nat.card F) :
    (Subgroup.solvableResidual (lineLocal F)).map (lineLocal F).subtype =
      lineLocal F := by
  rw [lineLocal_solvableResidual_eq_top F hcard, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

end Matrix.PSL3.LinearThree
