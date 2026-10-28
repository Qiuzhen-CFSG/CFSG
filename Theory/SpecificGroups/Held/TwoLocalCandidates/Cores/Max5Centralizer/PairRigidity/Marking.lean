module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer.PairRigidity.MarkedData

/-!+# Certified marking of the two ordered pairs

The labels are decoded from the published initial weight, individualized
at `(48,0)` and `(334,990)`. A common decoder therefore transports the
labels whenever a graph-centralizer element transports the ordered pair.
This only relabels the marked initial weight; it performs no refinement.
Source: GLS3 Table 5.3p, the Held 2B extraspecial centralizer.
-/

namespace Held.TwoLocalCandidates.Cores.Max5Centralizer.PairRigidity.Certificate

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem left_mark : ∀ x : Fin 2058,
    left0 x.val = decodeMarked (markPair weight0 48 0 x) := by
  apply allLetters
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem right_mark : ∀ x : Fin 2058,
    right0 x.val = decodeMarked (markPair weight0 334 990 x) := by
  apply allLetters
  decide +kernel

public theorem fixed_mark_transport (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphCentralizer) (h48 : σ 48 = 48) (h0 : σ 0 = 0) :
    Transports σ left0 left0 := by
  intro x
  rw [left_mark, left_mark]
  simpa only [h48, h0] using
    congrArg decodeMarked (markPair_transport σ (invariant0 σ hσ) 48 0 x)

public theorem exceptional_mark_transport (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphCentralizer) (h48 : σ 48 = 334) (h0 : σ 0 = 990) :
    Transports σ left0 right0 := by
  intro x
  rw [right_mark, left_mark]
  simpa only [h48, h0] using
    congrArg decodeMarked (markPair_transport σ (invariant0 σ hσ) 48 0 x)

end Held.TwoLocalCandidates.Cores.Max5Centralizer.PairRigidity.Certificate
