module
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts

/-!
# Neighbor-center joins inside the vertex core

If the critical length is greater than one, the join of all centers at
neighbors of any vertex d lies in the two-core of its stabilizer. Each
neighbor has distance one from d, strictly below the critical length, so
critical minimality puts its center in that core; the supremum stays there.

This is the repeated Vd≤Qd observation in Stellmacher (8.2), printed pp.37–38,
refs/latex/stellmacher-n-group.tex. The result uses only the original graph
and critical path, without a Section Eight context or noncentrality premise.
-/

namespace Stellmacher.SectionsFiveToSeven.SevenSix
open CosetGraphContext
universe u

public theorem neighbor_join_le_core_of_length_gt_one
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (hlen : 1 < cp.length) (vertex : Γ.Vertex) :
    v Γ vertex ≤ q Γ vertex := by
  rw [v, Γ.vAt_def]
  apply sSup_le
  rintro Z ⟨neighbor, hneighbor, rfl⟩
  apply critical_minimality Γ cp
  have hdistance : Γ.distance neighbor vertex = 1 := by
    simpa only [Γ.neighbors_def, Set.mem_ofPred_eq] using hneighbor
  omega

end Stellmacher.SectionsFiveToSeven.SevenSix
