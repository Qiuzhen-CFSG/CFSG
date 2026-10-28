module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_9_5_g

/-!
This module isolates `theorem_1_9_5_h` from `Theory.AlgebraicGroup.RootSystems.AlgebraicGroups`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

universe u v w

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

noncomputable local instance pslCarrierAlgebraicGroup (m : ℕ) :
    AlgebraicGroup
      (pslClosedSubgroupOf k (Fin (m + 1) → k)).carrierVariety :=
  (pslClosedSubgroupOf k (Fin (m + 1) → k)).carrierAlgebraicGroup

local instance torusNormalInNormalizer
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K) :
    (T.toSubgroup.subgroupOf T.normalizer.toSubgroup).Normal :=
  T.toSubgroup.normal_in_normalizer

public theorem theorem_1_9_5_h
    {K : Variety k} [AlgebraicGroup K] (hK : IsReductiveAlgebraicGroup K)
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T) :
    Subgroup.center (Variety.Point K) ≤ T.toSubgroup := by sorry

public structure InvariantOrderedRootSubgroupProduct
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (X : ClosedSubgroup K) (D : RootGroupData K T) where
  roots : List D.Root
  nodup : roots.Nodup
  contains_iff : ∀ α, α ∈ roots ↔ D.rootSubgroup α ≤ X
  mem_iff : ∀ x : Variety.Point K, x ∈ X ↔
    ∃ xs : List (Variety.Point K),
      List.Forall₂ (fun α y => y ∈ D.rootSubgroup α) roots xs ∧ xs.prod = x

end Theory.AlgebraicGroup
