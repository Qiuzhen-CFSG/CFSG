module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_4_a

/-!
This module isolates `theorem_1_10_4_b` from `Theory.AlgebraicGroup.RootSystems.AlgebraicGroups`.
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

public theorem theorem_1_10_4_b
    {ι E E' : Type u} [Finite ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    (P : RootPairing ι ℝ E E') [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] :
    (∃ V : SemisimpleVersion (k := k) P, IsUniversalRootVersion V) ∧
    (∃ V : SemisimpleVersion (k := k) P, IsAdjointRootVersion V) ∧
    (∀ V W : SemisimpleVersion (k := k) P,
      IsUniversalRootVersion V → IsUniversalRootVersion W →
        SemisimpleVersion.Isomorphic (P := P) V W) ∧
    (∀ V W : SemisimpleVersion (k := k) P,
      IsAdjointRootVersion V → IsAdjointRootVersion W →
        SemisimpleVersion.Isomorphic (P := P) V W) := by sorry

end Theory.AlgebraicGroup
