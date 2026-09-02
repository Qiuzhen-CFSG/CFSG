module

public import Theory.GroupAction.Defs

@[expose] public section

open scoped Pointwise

section FixedPointTransportSet

variable {G A : Type*} [Group G] [Group A] [MulAction A G]

omit [Group G] in
/-- Triviality of the action on a set is equivalent to containment in the fixed-point set. -/
theorem isTrivialActionOnSet_iff_subset_fixedPoints (S : Set G)
    : IsTrivialActionOnSet (A := A) (G := G) S ↔ S ⊆ MulAction.fixedPoints A G := by
  constructor
  · intro htriv x hx
    change ∀ a : A, a • x = x
    intro a
    exact htriv.acts_trivially a x hx
  · intro hle
    constructor
    intro a x hx
    have hxfix : x ∈ MulAction.fixedPoints A G := hle hx
    have hxfix' : ∀ b : A, b • x = x := by simpa [MulAction.fixedPoints] using hxfix
    exact hxfix' a

end FixedPointTransportSet

section FixedPointTransport

variable {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]

/-- Triviality on a subgroup is equivalent to subgroup containment in fixed points. -/
theorem isTrivialActionOnSubgroup_iff_le_fixedPoints_subgroup (H : Subgroup G)
    : IsTrivialActionOnSubgroup (A := A) (G := G) H ↔ H ≤ FixedPoints.subgroup A G := by
  constructor
  · intro htriv x hx
    change ∀ a : A, a • x = x
    intro a
    exact htriv.acts_trivially a x hx
  · intro hle
    constructor
    intro a x hx
    have hxfix : x ∈ FixedPoints.subgroup A G := hle hx
    have hxfix' : ∀ b : A, b • x = x :=
      (FixedPoints.mem_subgroup (M := A) (a := x)).1 hxfix
    exact hxfix' a

/-- A subgroup contained in fixed points is fixed pointwise. -/
theorem isTrivialActionOnSubgroup_of_le_fixedPoints_subgroup {H : Subgroup G}
    (hle : H ≤ FixedPoints.subgroup A G)
    : IsTrivialActionOnSubgroup (A := A) (G := G) H :=
  (isTrivialActionOnSubgroup_iff_le_fixedPoints_subgroup (A := A) (G := G) H).2 hle

/-! Functional spellings used by the group-action interfaces. -/

theorem actsTriviallyOnSubgroup_of_le_fixedPoints_subgroup {H : Subgroup G}
    (hle : H ≤ FixedPoints.subgroup A G)
    : ActsTriviallyOnSubgroup (A := A) (G := G) H := by
  intro a x hx
  exact (FixedPoints.mem_subgroup (M := A) (a := x)).1 (hle hx) a

end FixedPointTransport
