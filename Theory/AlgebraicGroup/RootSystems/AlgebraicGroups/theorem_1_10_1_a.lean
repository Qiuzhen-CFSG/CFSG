module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_9_5_i

/-!
This module isolates `theorem_1_10_1_a` from `Theory.AlgebraicGroup.RootSystems.AlgebraicGroups`.
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

public theorem theorem_1_10_1_a
    {K : Variety k} [AlgebraicGroup K] (hK : IsReductiveAlgebraicGroup K)
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T) :
    ∃ D : RootGroupData K T, D.IsRealization ∧
      ⁅(⊤ : Subgroup (Variety.Point K)), ⊤⁆ = RootSubgroupGenerated D Set.univ := by sorry

end Theory.AlgebraicGroup
