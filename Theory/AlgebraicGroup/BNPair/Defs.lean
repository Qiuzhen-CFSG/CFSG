module

public import Mathlib.Data.Finite.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs

universe u

/-! Tits systems and BN-pairs. -/

namespace Theory.AlgebraicGroup

open scoped Pointwise

variable {X : Type u} [Group X]

namespace TitsSystem

/-- The subset of `X` consisting of all representatives of a class in
`N / (B ∩ N)`.  Using all representatives keeps the BN axioms independent of
any chosen transversal. -/
@[expose]
public def representativeSet (B N : Subgroup X)
    [((B ⊓ N).subgroupOf N).Normal]
    (w : N ⧸ (B ⊓ N).subgroupOf N) : Set X :=
  {x | ∃ n : N,
      QuotientGroup.mk' ((B ⊓ N).subgroupOf N) n = w ∧ (n : X) = x}

end TitsSystem

/-- A Tits system, or BN-pair, in a group.

The quotient expressions in the exchange and nontriviality axioms use every
representative of each class in `N / (B ∩ N)`, so the definition does not
include a choice of quotient representatives. -/
public structure TitsSystem where
  B : Subgroup X
  N : Subgroup X
  generate : Subgroup.closure ((B : Set X) ∪ (N : Set X)) = ⊤
  [intersection_normal : ((B ⊓ N).subgroupOf N).Normal]
  S : Set (N ⧸ (B ⊓ N).subgroupOf N)
  finite_S : S.Finite
  involutions :
    ∀ s ∈ S, s ≠ (1 : N ⧸ (B ⊓ N).subgroupOf N) ∧ s ^ 2 = 1
  quotient_generate :
    Subgroup.closure (S : Set (N ⧸ (B ⊓ N).subgroupOf N)) = ⊤
  exchange :
    ∀ s ∈ S, ∀ w : N ⧸ (B ⊓ N).subgroupOf N,
      TitsSystem.representativeSet B N s * (B : Set X) *
          TitsSystem.representativeSet B N w ⊆
        ((B : Set X) * TitsSystem.representativeSet B N (s * w) *
            (B : Set X)) ∪
          ((B : Set X) * TitsSystem.representativeSet B N w * (B : Set X))
  nontrivial :
    ∀ s ∈ S,
      TitsSystem.representativeSet B N s * (B : Set X) *
          TitsSystem.representativeSet B N s ≠ (B : Set X)

/-- The normality stored in a Tits system is available to quotient-group
constructions depending on its intersection subgroup. -/
public instance TitsSystem.instIntersectionNormal (T : TitsSystem (X := X)) :
    ((T.B ⊓ T.N).subgroupOf T.N).Normal := T.intersection_normal

end Theory.AlgebraicGroup
