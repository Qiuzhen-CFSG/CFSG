module

public import Mathlib.GroupTheory.Solvable
public import Theory.AlgebraicGroup.Morphism.CodRestrict

universe u

/-! Solvability transported through algebraic-group morphisms. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A closed preimage is solvable when its restricted kernel and target are
solvable. -/
public theorem Morphism.closedSubgroupPreimage_isSolvable_of_kernel
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (S : ClosedSubgroup H)
    (hS : Group.IsSolvable (Variety.Point S.carrierVariety))
    (hker : Group.IsSolvable (f.preimageRestriction S).kernel) :
    Group.IsSolvable (Variety.Point (f.closedSubgroupPreimage S).carrierVariety) := by
  let g := f.preimageRestriction S
  let : Group.IsSolvable (Variety.Point S.carrierVariety) := hS
  let : Group.IsSolvable g.kernel := hker
  exact Group.isSolvable_of_ker_le_range g.kernel.subtype g.onPoints (by
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩)

/-- The kernel of a closed-preimage restriction is solvable whenever the
ambient morphism kernel is solvable. -/
public theorem Morphism.preimageRestriction_kernel_isSolvable_of_kernel
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (S : ClosedSubgroup H)
    (hker : Group.IsSolvable f.kernel) :
    Group.IsSolvable (f.preimageRestriction S).kernel := by
  let P := f.closedSubgroupPreimage S
  let g := f.preimageRestriction S
  let j : g.kernel →* f.kernel :=
    { toFun := fun x => ⟨P.inclusion.onPoints x.1, by
          change f.onPoints (P.inclusion.onPoints x.1) = 1
          rw [← f.preimageRestriction_inclusion_apply S]
          simpa using congrArg S.inclusion.onPoints x.2⟩
      map_one' := by
        apply Subtype.ext
        exact P.inclusion.onPoints.map_one
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact P.inclusion.onPoints.map_mul x.1 y.1 }
  have hj : Function.Injective j := by
    intro x y hxy
    have hxyG : P.inclusion.onPoints x.1 = P.inclusion.onPoints y.1 := by
      have h := congrArg Subtype.val hxy
      simpa [j] using h
    apply Subtype.ext
    exact P.inclusion_injective hxyG
  let : Group.IsSolvable f.kernel := hker
  exact Group.isSolvable_of_isSolvable_injective hj

end Theory.AlgebraicGroup
