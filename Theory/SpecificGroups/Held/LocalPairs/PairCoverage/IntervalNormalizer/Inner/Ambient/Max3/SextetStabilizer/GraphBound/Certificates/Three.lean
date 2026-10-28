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

private def sample3_0 : Finset (Fin 2058) := {852}

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem sample3_0_spec : ∀ x : Fin 2058,
    x ∈ sample3_0 ↔ baseSignature base2 x = 21825 := by
  decide +kernel

private def sample3_1 : Finset (Fin 2058) := {1793, 2023}

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem sample3_1_spec : ∀ x : Fin 2058,
    x ∈ sample3_1 ↔ baseSignature base2 x = 5125 := by
  decide +kernel

private def sample3_2 : Finset (Fin 2058) := {462, 1098, 1442, 1687}

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem sample3_2_spec : ∀ x : Fin 2058,
    x ∈ sample3_2 ↔ baseSignature base2 x = 4165 := by
  decide +kernel

private def sample3_3 : Finset (Fin 2058) := {69, 102}

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem sample3_3_spec : ∀ x : Fin 2058,
    x ∈ sample3_3 ↔ baseSignature base2 x = 1285 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem check3 : ∀ x : Fin 2058,
    baseSignature base2 x = baseSignature base2 3 →
    neighborCount sample3_0 x = neighborCount sample3_0 3 →
    neighborCount sample3_1 x = neighborCount sample3_1 3 →
    neighborCount sample3_2 x = neighborCount sample3_2 3 →
    neighborCount sample3_3 x = neighborCount sample3_3 3 →
    x = 3 := by
  decide +kernel

public theorem three_fixed (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ preservingGroup) (hs : ∀ b ∈ sextetBase, σ b = b)
    (h0 : σ 0 = 0)
    (h1 : σ 1 = 1)
    : σ 3 = 3 := by
  have hf : ∀ b ∈ base2, σ b = b := by
    intro b hb
    simp only [base2, List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · exact h0
    · exact h1
    · exact hs b hb
  apply check3 (σ 3) (baseSignature_invariant base2 σ hσ hf 3)
  · exact neighborCount_invariant sample3_0 σ hσ
      (sample_invariant base2 sample3_0 21825 sample3_0_spec σ hσ hf) 3
  · exact neighborCount_invariant sample3_1 σ hσ
      (sample_invariant base2 sample3_1 5125 sample3_1_spec σ hσ hf) 3
  · exact neighborCount_invariant sample3_2 σ hσ
      (sample_invariant base2 sample3_2 4165 sample3_2_spec σ hσ hf) 3
  · exact neighborCount_invariant sample3_3 σ hσ
      (sample_invariant base2 sample3_3 1285 sample3_3_spec σ hσ hf) 3

end SextetGraphBound
end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
