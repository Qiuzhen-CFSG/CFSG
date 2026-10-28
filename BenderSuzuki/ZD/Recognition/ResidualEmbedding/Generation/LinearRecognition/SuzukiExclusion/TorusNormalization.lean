module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity.OddNormalizer

/-!
# Normalization of the actual residual torus

The source identity K = D ∩ L and normalization of L by D show that the
actual pair stabilizer normalizes K. Both the prime weak-closure and quotient
fusion branches use this single declaration, preserving their common public
name and the original ambient normalizer.

Source: GLS IV, Chapter 2, Lemma 12.2(d,f), used in Propositions 12.13 and 14.1.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

namespace SuzukiExclusion

/-- The source torus is normal relative to the actual two-point stabilizer. -/
public theorem Context.pair_normalizes_torus (d : Context Z M z t m) :
    residualPairStabilizer M t ≤ normalizer (residualCommutator M t : Set G) := by
  rw [d.torus_structure.1]
  have hn := residualPairStabilizer_le_normalizer_residualGenerated d.minimal d.reduction
    d.action d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
  intro a ha
  rw [mem_normalizer_iff]
  intro b
  exact and_congr
    (mem_normalizer_iff.mp ((residualPairStabilizer M t).le_normalizer ha) b)
    (mem_normalizer_iff.mp (hn ha) b)


end SuzukiExclusion

end BenderSuzuki.ZD
