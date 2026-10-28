module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_9_5_h

/-!
This module isolates `theorem_1_9_5_i` from `Theory.AlgebraicGroup.RootSystems.AlgebraicGroups`.
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

public theorem theorem_1_9_5_i
    {K : Variety k} [AlgebraicGroup K] (hK : IsReductiveAlgebraicGroup K)
    (T X : ClosedSubgroup K) (hT : IsMaximalTorus T)
    (hX : IsClosedSubgroupInvariant T X)
    (D : RootGroupData K T) (hD : D.IsRealization) :
    (IsUnipotentAlgebraicGroup X.carrierVariety →
      Nonempty (InvariantOrderedRootSubgroupProduct X D)) ∧
    (T ≤ X →
      (X : Set (Variety.Point K)) =
        setMul (X.identityComponentAmbient : Set (Variety.Point K))
          ((X.toSubgroup ⊓ Subgroup.normalizer
            (T : Set (Variety.Point K))) : Set (Variety.Point K))) ∧
    (IsReductiveAlgebraicGroup X.carrierVariety →
      {Y : ClosedSubgroup K | IsTorusRootSubgroup T Y ∧ Y ≤ X} =
        Set.range (fun α : {α : D.Root // D.rootSubgroup α ≤ X} ↦
          D.rootSubgroup α.1)) := by sorry

end Theory.AlgebraicGroup
