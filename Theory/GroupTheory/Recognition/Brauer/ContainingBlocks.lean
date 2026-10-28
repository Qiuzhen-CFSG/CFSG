module
public import Theory.GroupTheory.Recognition.Brauer.InvolutionBlocks

/-!
# The point and line of an involution

Brauer, *On finite Desarguesian planes I*, p. 119 after (2B), denotes by
`(x)` and `[x]` the unique point and line containing an involution `x`.
This module defines those actual blocks as `pointOf` and `lineOf`, using
the proved existence and uniqueness theorem. Their implementation is kept
private; public membership and equality characterizations provide the API.

The same uniqueness makes both constructions equivariant under conjugation:
conjugating a containing block gives the unique block containing the
conjugated involution. These selectors support the source's incidence
and counting arguments without introducing another geometry or assuming
any of its later projective-plane properties. The original group and
orbit action instances are retained throughout.
-/

open scoped Pointwise

namespace Theory.GroupTheory.BrauerPlaneSeed

variable {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G)

/-- Brauer's point `(x)`, the unique point containing the involution `x`. -/
public noncomputable def pointOf (x : G) (hx : orderOf x = 2) : S.Point :=
  (S.existsUnique_blocks_of_involution hx).1.exists.choose

/-- Brauer's line `[x]`, the unique line containing the involution `x`. -/
public noncomputable def lineOf (x : G) (hx : orderOf x = 2) : S.Line :=
  (S.existsUnique_blocks_of_involution hx).2.exists.choose

/-- An involution belongs to the underlying set of its point. -/
public theorem mem_pointOf (x : G) (hx : orderOf x = 2) :
    x ∈ (S.pointOf x hx : Set G) :=
  (S.existsUnique_blocks_of_involution hx).1.exists.choose_spec

/-- An involution belongs to the underlying set of its line. -/
public theorem mem_lineOf (x : G) (hx : orderOf x = 2) :
    x ∈ (S.lineOf x hx : Set G) :=
  (S.existsUnique_blocks_of_involution hx).2.exists.choose_spec

/-- A point is the point of `x` exactly when its underlying set contains `x`. -/
public theorem pointOf_eq_iff (x : G) (hx : orderOf x = 2) (p : S.Point) :
    S.pointOf x hx = p ↔ x ∈ (p : Set G) := by
  constructor
  · rintro rfl
    exact S.mem_pointOf x hx
  · intro hp
    exact (S.existsUnique_blocks_of_involution hx).1.unique (S.mem_pointOf x hx) hp

/-- A line is the line of `x` exactly when its underlying set contains `x`. -/
public theorem lineOf_eq_iff (x : G) (hx : orderOf x = 2) (l : S.Line) :
    S.lineOf x hx = l ↔ x ∈ (l : Set G) := by
  constructor
  · rintro rfl
    exact S.mem_lineOf x hx
  · intro hl
    exact (S.existsUnique_blocks_of_involution hx).2.unique (S.mem_lineOf x hx) hl

/-- The point of an involution respects conjugation. The order proof for the
conjugated involution can be any proof of its order, by proof irrelevance. -/
public theorem pointOf_smul (g : ConjAct G) (x : G) (hx : orderOf x = 2)
    (hgx : orderOf (g • x) = 2) : S.pointOf (g • x) hgx = g • S.pointOf x hx := by
  apply (S.pointOf_eq_iff (g • x) hgx (g • S.pointOf x hx)).mpr
  exact Set.smul_mem_smul_set (S.mem_pointOf x hx)

/-- The line of an involution respects conjugation, independently of the
chosen proof that the conjugated involution has order two. -/
public theorem lineOf_smul (g : ConjAct G) (x : G) (hx : orderOf x = 2)
    (hgx : orderOf (g • x) = 2) : S.lineOf (g • x) hgx = g • S.lineOf x hx := by
  apply (S.lineOf_eq_iff (g • x) hgx (g • S.lineOf x hx)).mpr
  exact Set.smul_mem_smul_set (S.mem_lineOf x hx)

end Theory.GroupTheory.BrauerPlaneSeed
