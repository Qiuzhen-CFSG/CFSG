module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups
public import Theory.AlgebraicGroup.Cartan.Exceptional
public import Theory.AlgebraicGroup.Borel.StandardPositiveSystemClassification

/-!
This module isolates `theorem_1_11_2` from `Theory.AlgebraicGroup.Borel.RootStructure`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/


set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]


public theorem theorem_1_11_2
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsReductiveAlgebraicGroup K)
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T)
    (D : RootGroupData K T) (hD : D.IsRealization) :
    (∃ classify :
        {positiveRoots : Set D.Root // IsPositiveSystem D positiveRoots} ≃
          BorelContaining T,
      ∀ positiveRoots,
        Nonempty (IsBorelOfPositiveSystem D positiveRoots.1
          (classify positiveRoots).carrier)) ∧
    (∀ (C : ClosedSubgroup K),
      _root_.IsConnected (C : Set (Variety.Point K)) →
      Group.IsSolvable (Variety.Point C.carrierVariety) →
      T ≤ C →
      ∃ U : {U : ClosedSubgroup K // IsUnipotentRadicalOf C U},
        U.1.toSubgroup =
          RootSubgroupGenerated D
            {α | (D.rootSubgroup α).toSubgroup ≤ U.1.toSubgroup}) := by sorry

end Theory.AlgebraicGroup
