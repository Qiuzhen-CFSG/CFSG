module
public import Theory.GroupTheory.Recognition.Brauer.ContainingBlocks
public import Theory.GroupTheory.Recognition.Brauer.BlockIntersection

/-!
# Simultaneous point-line stabilizers in Brauer's geometry

A conjugating element fixes both the point and the line associated with an
involution exactly when it centralizes that involution. This is Brauer,
*On finite Desarguesian planes I*, (4A), article page 123, stated uniformly
for all involutions as needed for the kernel intersection in (4B).

If both blocks are fixed, the conjugate involution lies in their intersection,
whose only element is the original involution by the proved (2C). Conversely,
a conjugation fixing the involution preserves its unique containing point
and line. The proof uses the original block actions and the seed-layer
intersection theorem; it requires no coordinate recognition or faithfulness.
-/

open scoped Pointwise

namespace Theory.GroupTheory.BrauerPlaneSeed

public theorem fixes_point_and_line_iff_mem_centralizer
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G)
    (x : G) (hx : orderOf x = 2) (g : ConjAct G) :
    (g • S.pointOf x hx = S.pointOf x hx ∧
      g • S.lineOf x hx = S.lineOf x hx) ↔
      ConjAct.ofConjAct g ∈ Subgroup.centralizer ({x} : Set G) := by
  constructor
  · rintro ⟨hp, hl⟩
    have hgp : g • x ∈ (S.pointOf x hx : Set G) := by
      have h := Set.smul_mem_smul_set (a := g) (S.mem_pointOf x hx)
      change g • x ∈ ((g • S.pointOf x hx : S.Point) : Set G) at h
      rwa [hp] at h
    have hgl : g • x ∈ (S.lineOf x hx : Set G) := by
      have h := Set.smul_mem_smul_set (a := g) (S.mem_lineOf x hx)
      change g • x ∈ ((g • S.lineOf x hx : S.Line) : Set G) at h
      rwa [hl] at h
    have hfix : g • x = x := S.point_line_intersection_subsingleton _ _
      ⟨hgp, hgl⟩ ⟨S.mem_pointOf x hx, S.mem_lineOf x hx⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)
  · intro hg
    have hfix : g • x = x := mul_inv_eq_iff_eq_mul.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hg)
    constructor
    · apply ((S.pointOf_eq_iff x hx (g • S.pointOf x hx)).mpr ?_).symm
      have h := Set.smul_mem_smul_set (a := g) (S.mem_pointOf x hx)
      change g • x ∈ ((g • S.pointOf x hx : S.Point) : Set G) at h
      rwa [hfix] at h
    · apply ((S.lineOf_eq_iff x hx (g • S.lineOf x hx)).mpr ?_).symm
      have h := Set.smul_mem_smul_set (a := g) (S.mem_lineOf x hx)
      change g • x ∈ ((g • S.lineOf x hx : S.Line) : Set G) at h
      rwa [hfix] at h

end Theory.GroupTheory.BrauerPlaneSeed

