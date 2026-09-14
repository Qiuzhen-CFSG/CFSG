module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Bracket
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Basic
import FeitThompson.Commutator.Core
public import Theory.GroupAction.Defs
public import Theory.GroupAction.Invariant

open scoped FixedPoints
open Theory.GroupAction

section GroupActionDefs

variable {G A : Type*} [Group G] [Group A]

/-- `C_G(A)`: the subgroup of elements of `G` fixed by the `A`-action. -/
public abbrev fixedPointSubgroup (A : Type*) (G : Type*) [Group A] [Group G] [MulDistribMulAction A G] :
    Subgroup G :=
  FixedPoints.subgroup A G

/-- `C_A(S)`: the subgroup of `A` fixing every element of `S` pointwise. -/
public abbrev fixingSubgroupOf (A : Type*) (G : Type*) [Group A] [MulAction A G]
    (S : Set G) :
    Subgroup A :=
  fixingSubgroup (M := A) (α := G) S

/-- The action of `A` on `G` is trivial. -/
@[expose] public def ActsTrivially (A : Type*) (G :Type*) [SMul A G] : Prop :=
  ∀ a : A, ∀ g : G, a • g = g

/-- `A` acts trivially on a subgroup `H ≤ G` (as a set), i.e. fixes all its elements. -/
@[expose] public def ActsTriviallyOnSubgroup (A : Type*) (G : Type*) [Group G] [SMul A G]
    (H : Subgroup G) : Prop :=
  ∀ a : A, ∀ g : G, g ∈ H → a • g = g

end GroupActionDefs

/-- `A` stabilizes a normal series if:
- the series has explicit top and bottom endpoints,
- each step moves downward (`Gi (next i) ≤ Gi i`),
- every term is normal in `G`,
- repeatedly applying `next` from the top eventually reaches the bottom,
- every term is `A`-invariant,
- and the action on each factor is trivial (`(a • g) * g⁻¹ ∈ Gi (next i)` for `g ∈ Gi i`).
-/
@[expose]
public def StabilizesNormalSeries {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    {ι : Type*} (Gi : ι → Subgroup G) (next : ι → ι) : Prop :=
  (∃ top bottom : ι,
      Gi top = ⊤ ∧
      Gi bottom = ⊥ ∧
      (∃ n : ℕ, Nat.iterate next n top = bottom)) ∧
    (∀ i, Gi (next i) ≤ Gi i) ∧
    (∀ i, (Gi i).Normal) ∧
    (∀ i, IsInvariant A G (Gi i)) ∧
      ∀ i (a : A) (g : G), g ∈ Gi i → (a • g) * g⁻¹ ∈ Gi (next i)
