module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer.Data

/-!
# Certified initial cells for the max5 core centralizer

A commuting graph permutation preserves equality and adjacency with each
of the seven core actors. The finite decoding check ties the first color
table to precisely these invariants. The designated cells restrict the
possible images of `(48,0)` to `2*64` pairs. Exhaustion of these pairs and
marked-pair rigidity are separate calculations.
-/

namespace Held.TwoLocalCandidates.Cores.Max5Centralizer

public theorem invariant0 : Invariant weight0 := by
  apply decoded_initial weight0 decode0
  apply allLetters
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem cell48 : ∀ x : Fin 2058,
    weight0 x.val = weight0 48 ↔ x = 48 ∨ x = 334 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem cell0_count : colorCount weight0 (weight0 0) = 64 := by
  decide +kernel

public theorem image48 (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ graphCentralizer) :
    σ 48 = 48 ∨ σ 48 = 334 :=
  (cell48 (σ 48)).mp (invariant0 σ hσ 48)

public theorem image0 (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ graphCentralizer) :
    weight0 (σ 0).val = weight0 0 := invariant0 σ hσ 0

end Held.TwoLocalCandidates.Cores.Max5Centralizer
