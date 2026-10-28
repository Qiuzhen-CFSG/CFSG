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

private def sample0_0 : Finset (Fin 2058) := {8, 99, 161, 278, 311, 692, 734, 742, 762, 1237, 1238, 1266, 1378, 1401, 1608, 1955}

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem sample0_0_spec : ∀ x : Fin 2058,
    x ∈ sample0_0 ↔ baseSignature sextetBase x = 1109 := by
  decide +kernel

@[expose] public def candidates0 : Finset (Fin 2058) := {0, 18, 49, 52, 55, 63, 66, 121, 125, 168, 219, 334, 336, 355, 371, 374, 384, 417, 444, 450, 528, 533, 581, 617, 732, 810, 829, 875, 891, 919, 925, 941, 947, 1044, 1054, 1058, 1077, 1093, 1112, 1150, 1157, 1189, 1367, 1395, 1419, 1450, 1455, 1514, 1523, 1619, 1631, 1640, 1647, 1654, 1715, 1730, 1758, 1796, 1802, 1841, 1846, 1853, 1865, 1994}

public theorem candidates0_card : candidates0.card = 64 := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem check0 : ∀ x : Fin 2058,
    baseSignature sextetBase x = baseSignature sextetBase 0 →
    neighborCount sample0_0 x = neighborCount sample0_0 0 →
    x ∈ candidates0 := by
  decide +kernel

public theorem zero_image_mem (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ preservingGroup) (hs : ∀ b ∈ sextetBase, σ b = b)
    : σ 0 ∈ candidates0 := by
  have hf := hs
  apply check0 (σ 0) (baseSignature_invariant sextetBase σ hσ hf 0)
  · exact neighborCount_invariant sample0_0 σ hσ
      (sample_invariant sextetBase sample0_0 1109 sample0_0_spec σ hσ hf) 0

end SextetGraphBound
end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
