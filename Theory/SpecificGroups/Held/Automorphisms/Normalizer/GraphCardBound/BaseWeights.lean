module

public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphCardBound.Data

/-!
# The first refinement

Fixing the initial base points preserves their equality and adjacency
signatures. Every displayed label is checked against that signature.

-/

namespace Held.NormalizerGraph.CardBound

public theorem invariant11 : Invariant 1 weight11 := by
  apply base_invariant [0] (by simp) weight11 decode11
  intro x
  have h : ∀ y : Fin 2058, weight11 y.val = decode11 (baseSignature [0] y) := by
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 8000000 in
      decide +kernel
  exact h x

public theorem invariant21 : Invariant 2 weight21 := by
  apply base_invariant [0, 1] (by simp) weight21 decode21
  intro x
  have h : ∀ y : Fin 2058, weight21 y.val = decode21 (baseSignature [0, 1] y) := by
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 8000000 in
      decide +kernel
  exact h x

public theorem invariant31 : Invariant 3 weight31 := by
  apply base_invariant [0, 1, 2] (by simp) weight31 decode31
  intro x
  have h : ∀ y : Fin 2058, weight31 y.val = decode31 (baseSignature [0, 1, 2] y) := by
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 8000000 in
      decide +kernel
  exact h x

public theorem invariant41 : Invariant 4 weight41 := by
  apply base_invariant [0, 1, 2, 3] (by simp) weight41 decode41
  intro x
  have h : ∀ y : Fin 2058, weight41 y.val = decode41 (baseSignature [0, 1, 2, 3] y) := by
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 8000000 in
      decide +kernel
  exact h x

end Held.NormalizerGraph.CardBound
