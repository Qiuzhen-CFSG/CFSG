module

public import Theory.GroupAction.Invariant

open scoped FixedPoints

section GroupActionDefs

variable {G A : Type*} [Group G] [Group A]

/-- Compatibility alias for the generic invariant-subgroup predicate. -/
public abbrev IsInvariant
    (A : Type*) (G : Type*) [Group G] [SMul A G] (H : Subgroup G) : Prop :=
  Theory.GroupAction.IsInvariant A G H

/-- Compatibility alias for the induced action on an invariant subgroup. -/
public abbrev instMulDistribMulAction_subtype
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    {H : Subgroup G} [IsInvariant A G H] : MulDistribMulAction A H :=
  Theory.GroupAction.instMulDistribMulAction_subtype

/-- `C_G(A)`: the subgroup of elements of `G` fixed by the `A`-action. -/
public abbrev fixedPointSubgroup (A : Type*) (G : Type*) [Group A] [Group G]
    [MulDistribMulAction A G] : Subgroup G :=
  FixedPoints.subgroup A G

/-- `C_A(S)`: the subgroup of `A` fixing every element of `S` pointwise. -/
public abbrev fixingSubgroupOf (A : Type*) (G : Type*) [Group A] [MulAction A G]
    (S : Set G) : Subgroup A :=
  fixingSubgroup (M := A) (α := G) S

/-- Compatibility spelling for a trivial action. -/
@[expose] public def ActsTrivially (A : Type*) (G : Type*) [SMul A G] : Prop :=
  ∀ a : A, ∀ g : G, a • g = g

/-- Compatibility spelling for an action trivial on a subgroup. -/
@[expose] public def ActsTriviallyOnSubgroup
    (A : Type*) (G : Type*) [Group G] [SMul A G] (H : Subgroup G) : Prop :=
  ∀ a : A, ∀ g : G, g ∈ H → a • g = g

end GroupActionDefs

namespace IsInvariant

/-- Compatibility projection for `Theory.GroupAction.IsInvariant.invariant`. -/
public theorem invariant
    {G A : Type*} [Group G] [SMul A G] {H : Subgroup G}
    [IsInvariant A G H] (a : A) (g : G) : g ∈ H ↔ a • g ∈ H :=
  Theory.GroupAction.IsInvariant.invariant a g

end IsInvariant

/-- Compatibility spelling for an action stabilizing a normal series. -/
@[expose] public def StabilizesNormalSeries
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    {ι : Type*} (Gi : ι → Subgroup G) (next : ι → ι) : Prop :=
  (∃ top bottom : ι,
      Gi top = ⊤ ∧
      Gi bottom = ⊥ ∧
      (∃ n : ℕ, Nat.iterate next n top = bottom)) ∧
    (∀ i, Gi (next i) ≤ Gi i) ∧
    (∀ i, (Gi i).Normal) ∧
    (∀ i, IsInvariant A G (Gi i)) ∧
      ∀ i (a : A) (g : G), g ∈ Gi i → (a • g) * g⁻¹ ∈ Gi (next i)
