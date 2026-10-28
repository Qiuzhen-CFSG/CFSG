module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.SextetStabilizer.GraphBound.Basic

/-!
# Small adjacency certificates for the pointwise sextet stabilizer

The sample sets are complete adjacency-signature classes relative to the fixed
vertices. Their sizes are at most sixteen. Neighbor counts into these classes
leave 64 candidates for vertex 0 and three for vertex 1. After both are fixed,
they determine vertices 2 and 3. All sample identifications and separations are
checked against the actual published relation by the Lean kernel.

Source: ATLAS HeG1-p2058B0; see `SextetStabilizer/Source/README.md`.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
namespace SextetGraphBound
open Held.NormalizerGraph Held.NormalizerGraph.CardBound

private def base1 : List (Fin 2058) := 0 :: sextetBase

private def sample1_0 : Finset (Fin 2058) := {135, 194, 872, 1331, 1573, 1997}

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem sample1_0_spec : ∀ x : Fin 2058,
    x ∈ sample1_0 ↔ baseSignature base1 x = 273 := by
  decide +kernel

private def sample1_1 : Finset (Fin 2058) := {285, 293, 532, 1170, 1276, 2026}

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem sample1_1_spec : ∀ x : Fin 2058,
    x ∈ sample1_1 ↔ baseSignature base1 x = 81 := by
  decide +kernel

@[expose] public def candidates1 : Finset (Fin 2058) := {1, 1386, 1422}

public theorem candidates1_card : candidates1.card = 3 := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem check1 : ∀ x : Fin 2058,
    baseSignature base1 x = baseSignature base1 1 →
    neighborCount sample1_0 x = neighborCount sample1_0 1 →
    neighborCount sample1_1 x = neighborCount sample1_1 1 →
    x ∈ candidates1 := by
  decide +kernel

public theorem one_image_mem (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ preservingGroup) (hs : ∀ b ∈ sextetBase, σ b = b)
    (h0 : σ 0 = 0)
    : σ 1 ∈ candidates1 := by
  have hf : ∀ b ∈ base1, σ b = b := by
    intro b hb
    rcases (show b = 0 ∨ b ∈ sextetBase from List.mem_cons.mp hb) with rfl | hb
    · exact h0
    · exact hs b hb
  apply check1 (σ 1) (baseSignature_invariant base1 σ hσ hf 1)
  · exact neighborCount_invariant sample1_0 σ hσ
      (sample_invariant base1 sample1_0 273 sample1_0_spec σ hσ hf) 1
  · exact neighborCount_invariant sample1_1 σ hσ
      (sample_invariant base1 sample1_1 81 sample1_1_spec σ hσ hf) 1

end SextetGraphBound
end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
