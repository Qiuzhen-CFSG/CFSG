module
public import Theory.GroupTheory.Recognition.Brauer.PlaneData
public import Mathlib.Algebra.Group.Prod

/-!
# The actual Brauer collineation action

Package the existing conjugation actions on Brauer's point and line block
families as a homomorphism from the source group to their permutation-group
product. Its elements preserve the original incidence relation, and its
kernel consists exactly of elements fixing every point and every line.

This is the representation gamma used in Brauer, *On finite Desarguesian
planes I*, Section 4, article page 123. The definition composes the existing
ConjAct permutation homomorphisms with the canonical group equivalence.
Its body stays unexposed: the public point/line evaluation lemmas, incidence
equivalence, and kernel criterion supply the behavior needed by the kernel
and image arguments. No coordinate model or new action is introduced.
-/

open scoped Pointwise

namespace Theory.GroupTheory.BrauerPlaneSeed

public noncomputable def collineationRepresentation
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G) :
    G →* Equiv.Perm S.Point × Equiv.Perm S.Line :=
  ((MulAction.toPermHom (ConjAct G) S.Point).prod
    (MulAction.toPermHom (ConjAct G) S.Line)).comp ConjAct.toConjAct.toMonoidHom

public theorem collineationRepresentation_point_apply
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G) (g : G) (p : S.Point) :
    (S.collineationRepresentation g).1 p = ConjAct.toConjAct g • p := by rfl

public theorem collineationRepresentation_line_apply
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G) (g : G) (l : S.Line) :
    (S.collineationRepresentation g).2 l = ConjAct.toConjAct g • l := by rfl

public theorem mem_collineationRepresentation_ker_iff
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G) (g : G) :
    g ∈ S.collineationRepresentation.ker ↔
      (∀ p : S.Point, ConjAct.toConjAct g • p = p) ∧
      (∀ l : S.Line, ConjAct.toConjAct g • l = l) := by
  change S.collineationRepresentation g = 1 ↔ _
  constructor
  · intro h
    constructor
    · intro p
      exact congrArg (fun e : Equiv.Perm S.Point × Equiv.Perm S.Line => e.1 p) h
    · intro l
      exact congrArg (fun e : Equiv.Perm S.Point × Equiv.Perm S.Line => e.2 l) h
  · rintro ⟨hp, hl⟩
    apply Prod.ext
    · exact Equiv.ext hp
    · exact Equiv.ext hl

public theorem collineationRepresentation_incident_iff
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G)
    (g : G) (p : S.Point) (l : S.Line) :
    (S.collineationRepresentation g).1 p ∈ (S.collineationRepresentation g).2 l ↔
      p ∈ l := by
  exact Set.disjoint_smul_set

end Theory.GroupTheory.BrauerPlaneSeed

