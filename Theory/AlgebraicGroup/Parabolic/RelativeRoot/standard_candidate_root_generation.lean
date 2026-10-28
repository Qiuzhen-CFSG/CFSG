module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.theorem_1_13_2

/-!
This module combines the ambient root-generation bridge with the standard
candidate specifications.  The generation hypothesis proves only the ambient
clause; the Levi and unipotent closure identities come from the unconditional
public specifications in their owning modules.
-/

set_option warningAsError false

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem standardCandidate_rootGeneration
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (D : RootGroupData K T)
    (hgen : RootSubgroupGenerated D (Set.univ : Set D.Root) ⊔ T.toSubgroup = ⊤)
    (positiveRoots J : Set D.Root) :
    RootSubgroupGenerated D (Set.univ : Set D.Root) ⊔ T.toSubgroup = ⊤ ∧
      leviCandidate T D J =
        subgroupZariskiClosure K
          (T.toSubgroup ⊔ standardLeviRootFactor D (RootSubsystemSpan D J)) ∧
      unipotentCandidate T D positiveRoots J =
        subgroupZariskiClosure K
          (standardUnipotentRootFactor D positiveRoots
            (RootSubsystemSpan D J)) := by
  exact
    ⟨hgen, leviCandidate_spec T D J,
      unipotentCandidate_spec T D positiveRoots J⟩

end Theory.AlgebraicGroup
