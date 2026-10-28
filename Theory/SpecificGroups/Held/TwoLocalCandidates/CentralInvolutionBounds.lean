module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.CentralInvolutionBounds.Identities
public import Theory.SpecificGroups.Held.TwoLocalCandidates.CentralInvolutionBounds.LowerBound
public import Theory.SpecificGroups.Held.TwoLocalCandidates.CentralInvolutionBounds.UpperBound

/-!
# Finite bounds at the central max5 involution

For the actual element `max5First ^ 4`, the imported certificates prove order
two, centralization by max5, and the lower bound 21504 for that subgroup.
The full graph-preserving centralizer has order at most 43008. Thus these
bounds can bound the index in the Held centralizer without using an ambient
Held order, a centralizer identification, or simplicity.

The lower certificate uses orbit trees at 0, 1, 2. The upper certificate uses
invariant cells at 48, 191, 877, 65, 0, 1, 2 and a discrete terminal coloring.
Every finite check uses kernel reduction. Reproduction and action conventions
are recorded in `CentralInvolutionBounds/source/README.md`.
Source leads: GLS3 Table 5.3p; quasithin Theorem 0.1.2(5).
-/

namespace Held.TwoLocalCandidates.CentralInvolutionBounds

/-- The full preserving group centralizing the represented involution has at
most 43008 elements. This assertion concerns the actual representation. -/
public theorem graph_centralizer_card_le :
    Nat.card ↥(NormalizerGraph.preservingGroup ⊓
      Subgroup.centralizer ({representation (max5First ^ 4)} :
        Set (Equiv.Perm (Fin 2058)))) ≤ 43008 := by
  rw [← p2_eq_representation]
  exact graphCentralizer_card_le

end Held.TwoLocalCandidates.CentralInvolutionBounds
