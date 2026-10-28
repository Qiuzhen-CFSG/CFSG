module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.GeometryContract

/-!
# The Sylow step in the torus fixed-point argument

This is the interface between (12G) and (12H) in the proof of GLS4,
Chapter 2, Proposition 12.13. The Sylow subgroup is a subgroup of the
ambient group, lies in the literal two-point stabilizer, contains the
specified prime-order torus element, and is normalized by the specified
swapping involution. The fixed-point clause concerns the whole intersection
of that Sylow subgroup with the torus, not its prime-order subgroup.

The record does not assert existence or weak closure. Its producer must
supply the invariant Sylow construction, ambient Sylow promotion and (12G).
The weak-closure proof may consume this record independently; the final
Proposition 12.13 assembly must discharge its existence.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Proposition 12.13, lines 2297–2310.
-/

namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup

universe u

/-- The ambient Sylow and fixed-intersection data preceding (12H). -/
public structure TorusSylowData {G : Type u} [Group G]
    (M : Subgroup G) (t x : G) (p : ℕ) where
  P : Sylow p G
  le_pair : (P : Subgroup G) ≤ residualPairStabilizer M t
  mem : x ∈ (P : Subgroup G)
  invariant : t ∈ normalizer ((P : Subgroup G) : Set G)
  fixed_torus : ∀ beta : G ⧸ M,
    (∀ y ∈ residualCommutator M t ⊓ (P : Subgroup G), y • beta = beta) ↔
      beta = QuotientGroup.mk 1 ∨ beta = QuotientGroup.mk t

end BenderSuzuki.ZD.SuzukiExclusion
