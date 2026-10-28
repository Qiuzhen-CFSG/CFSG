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

private def base2 : List (Fin 2058) := 0 :: 1 :: sextetBase

private def sample2_0 : Finset (Fin 2058) := {193, 913, 1000, 1972}

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem sample2_0_spec : ∀ x : Fin 2058,
    x ∈ sample2_0 ↔ baseSignature base2 x = 21589 := by
  decide +kernel

private def sample2_1 : Finset (Fin 2058) := {1642, 2055}

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem sample2_1_spec : ∀ x : Fin 2058,
    x ∈ sample2_1 ↔ baseSignature base2 x = 4357 := by
  decide +kernel

private def sample2_2 : Finset (Fin 2058) := {46, 610, 1688, 1752}

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem sample2_2_spec : ∀ x : Fin 2058,
    x ∈ sample2_2 ↔ baseSignature base2 x = 1045 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem check2 : ∀ x : Fin 2058,
    baseSignature base2 x = baseSignature base2 2 →
    neighborCount sample2_0 x = neighborCount sample2_0 2 →
    neighborCount sample2_1 x = neighborCount sample2_1 2 →
    neighborCount sample2_2 x = neighborCount sample2_2 2 →
    x = 2 := by
  decide +kernel

public theorem two_fixed (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ preservingGroup) (hs : ∀ b ∈ sextetBase, σ b = b)
    (h0 : σ 0 = 0)
    (h1 : σ 1 = 1)
    : σ 2 = 2 := by
  have hf : ∀ b ∈ base2, σ b = b := by
    intro b hb
    simp only [base2, List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · exact h0
    · exact h1
    · exact hs b hb
  apply check2 (σ 2) (baseSignature_invariant base2 σ hσ hf 2)
  · exact neighborCount_invariant sample2_0 σ hσ
      (sample_invariant base2 sample2_0 21589 sample2_0_spec σ hσ hf) 2
  · exact neighborCount_invariant sample2_1 σ hσ
      (sample_invariant base2 sample2_1 4357 sample2_1_spec σ hσ hf) 2
  · exact neighborCount_invariant sample2_2 σ hσ
      (sample_invariant base2 sample2_2 1045 sample2_2_spec σ hσ hf) 2

end SextetGraphBound
end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
