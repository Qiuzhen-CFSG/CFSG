module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Setup

/-!
# The intermediate geometry in the Suzuki exclusion

This is the output contract for GLS4, Chapter 2, Lemmas 14.2–14.3 and
(14A)–(14C). Its construction takes the centralizer embedding from Lemma
12.14. The later Sylow and fusion argument may use this geometry explicitly;
the final Proposition 14.1 assembly must construct it. No inhabitant or
source theorem is asserted in this module.

All Sylow assertions use the literal ambient images of Sylow subgroups of
the stated normalizer or subgroup. The source `P` is the two-core of
`M ∩ L`, and the source `A = M°` is the distinguished closure in `M`.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped Pointwise

universe u
variable {G : Type u} [Group G]

/-- Proposition 12.13, on the actual cosets: the only fixed points of
a nonidentity split-torus element are the two distinguished points. -/
@[expose] public def TorusSemiregular (M : Subgroup G) (t : G) : Prop :=
  ∀ x ∈ residualCommutator M t, x ≠ 1 → ∀ beta : G ⧸ M,
    x • beta = beta ↔ beta = QuotientGroup.mk 1 ∨ beta = QuotientGroup.mk t

/-- The ambient image of the two-core of the local Borel, source `P`. -/
@[expose] public def borelTwoCore (M : Subgroup G) (z t : G) : Subgroup G :=
  let B := M ⊓ residualGenerated M z t
  (pCore 2 B).map B.subtype

/-- The shared, conditional output of Lemmas 14.2–14.3. In particular,
this does not assert Sylow maximality of `S` in `G`, the size of `U`, or
weak closure in `M/A`; those are later conclusions. -/
public structure LocalGeometry [Finite G]
    (Z : Set G) (M : Subgroup G) (z t : G) (m : ℕ) where
  T : Subgroup G
  U : Subgroup G
  S : Subgroup G
  normalizer_control : ∀ Y : Subgroup G,
    Y ≤ centralizer (residualGenerated M z t : Set G) → Y ≠ ⊥ →
      normalizer (Y : Set G) ≤ normalizer (residualGenerated M z t : Set G)
  pair_card_dvd : Nat.card (residualPairStabilizer M t) ∣
    (2 ^ (2 * m + 1) - 1) * Nat.card (residualGenerated M z t) * (2 * m + 1)
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
  P_card : Nat.card (borelTwoCore M z t) = (2 ^ (2 * m + 1)) ^ 2
  P_center : (center (borelTwoCore M z t)).map (borelTwoCore M z t).subtype =
    closure (Z ∩ (M : Set G))
  P_involutions : {x : G | x ∈ borelTwoCore M z t ∧ x ^ 2 = 1} =
    (closure (Z ∩ (M : Set G)) : Set G)
  centralizer_in_normalizer :
    ((normalizer (residualGenerated M z t : Set G) ⊓
      centralizer (closure (Z ∩ (M : Set G)) : Set G) : Subgroup G) : Set G) =
      (borelTwoCore M z t : Set G) * (centralizer (residualGenerated M z t : Set G) : Set G)
  centralizer_U : ∀ u ∈ U, u ≠ 1 →
    centralizer (closure (Z ∩ (M : Set G)) : Set G) ⊓ centralizer ({u} : Set G) = T
  U_elementary : IsElementaryAbelian 2 U
  centralizer_solvable : Group.IsSolvable (centralizer (residualGenerated M z t : Set G))

end BenderSuzuki.ZD.SuzukiExclusion
