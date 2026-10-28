module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.GeometryContract

/-!
# The Sylow configuration preceding Lemma 14.3

This intermediate output separates the Sylow construction in (14B)–(14C)
from the centralizer and conjugate-subgroup argument of Lemma 14.3. It is
not an additional hypothesis of the final local-geometry constructor: that
constructor must produce this configuration from `Context`.

Every Sylow is represented by its literal ambient image. The source P is
still `borelTwoCore M z t`, and the two direct factors in T are P and U.
Source: GLS4, Chapter 2, (14B)–(14C) and the Sylow enlargement in 14.3(b).
-/

namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup
open scoped Pointwise

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The output of the Sylow construction, before any assertion that U is
elementary abelian or that J is solvable. -/
public structure SylowConfiguration (M : Subgroup G) (z t : G) where
  T : Subgroup G
  U : Subgroup G
  S : Subgroup G
  T_sylow : ∃ V : Sylow 2 (normalizer (residualGenerated M z t : Set G)),
    (V : Subgroup (normalizer (residualGenerated M z t : Set G))).map
      (normalizer (residualGenerated M z t : Set G)).subtype = T
  S_sylow : ∃ V : Sylow 2 (normalizer (T : Set G)),
    (V : Subgroup (normalizer (T : Set G))).map (normalizer (T : Set G)).subtype = S
  U_eq : U = T ⊓ centralizer (residualGenerated M z t : Set G)
  U_sylow_pair : ∃ V : Sylow 2 (residualPairStabilizer M t),
    (V : Subgroup (residualPairStabilizer M t)).map
      (residualPairStabilizer M t).subtype = U
  U_sylow_centralizer : ∃ V : Sylow 2 (centralizer (residualGenerated M z t : Set G)),
    (V : Subgroup (centralizer (residualGenerated M z t : Set G))).map
      (centralizer (residualGenerated M z t : Set G)).subtype = U
  P_eq : borelTwoCore M z t = T ⊓ residualGenerated M z t
  T_product : (T : Set G) = (borelTwoCore M z t : Set G) * (U : Set G)
  P_disjoint_U : Disjoint (borelTwoCore M z t) U
  T_lt_S : T < S
  S_le_M : S ≤ M

end BenderSuzuki.ZD.SuzukiExclusion
