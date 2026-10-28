module

public import Theory.AlgebraicGroup.QuotientData

/-!
This module isolates `theorem_1_9_5_a` from `Theory.AlgebraicGroup.RootSystems.AlgebraicGroups`.
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

public theorem theorem_1_9_5_a
    {K : Variety k} [AlgebraicGroup K] (hK : IsReductiveAlgebraicGroup K)
    (T X : ClosedSubgroup K) (hT : IsMaximalTorus T) :
    IsTorusRootSubgroup T X ↔
      IsClosedSubgroupInvariant T X ∧
      IsUnipotentAlgebraicGroup X.carrierVariety ∧ X.toSubgroup ≠ ⊥ ∧
      (∀ Y : ClosedSubgroup K, IsClosedSubgroupInvariant T Y →
        IsUnipotentAlgebraicGroup Y.carrierVariety → Y ≤ X →
        Y.toSubgroup = ⊥ ∨ Y = X) := by sorry

end Theory.AlgebraicGroup
