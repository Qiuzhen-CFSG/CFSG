module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Structure
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer.Initial
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer.PairEnumeration
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer.PairRigidity
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer.Reduction

/-!
# Self-centralization of Held's max5 core

The checked pair enumeration and refinement certificates leave only the
identity and the actual involution `representation (max5First ^ 4)` among
graph permutations centralizing the embedded core. The involution composition
argument gives the ambient graph bound. Faithful transport, together with
membership of the first core generator, proves intrinsic self-centralization.
Both conclusions are unconditional for the literal ATLAS max5 core.

Source: GLS3 Table 5.3p, the extraspecial core of the 2B centralizer.
-/

namespace Held.TwoLocalCandidates.Cores

/-- Every graph permutation centralizing the actual embedded max5 core is
a power of the fourth power of its first local generator. -/
public theorem Max5Centralizer.graphCentralizer_le_zpowers :
    Held.NormalizerGraph.preservingGroup ⊓
      Subgroup.centralizer ((core 2).map (embedding 2) : Set (Equiv.Perm (Fin 2058))) ≤
        Subgroup.zpowers (Held.representation (Held.TwoLocalCandidates.max5First ^ 4)) :=
  Max5Centralizer.graphCentralizer_le_zpowers_of_pair_certificates
    Max5Centralizer.pair_candidates Max5Centralizer.fixed_pair_eq_one
    Max5Centralizer.exceptional_pair_impossible

/-- The intrinsic centralizer of the max5 core is contained in that core. -/
public theorem max5_selfCentralizing :
    Subgroup.centralizer (core 2 : Set (Held.TwoLocalCandidates.subgroup 2)) ≤ core 2 :=
  Max5Centralizer.selfCentralizing_of_graph_bound Max5Centralizer.graphCentralizer_le_zpowers

end Held.TwoLocalCandidates.Cores
