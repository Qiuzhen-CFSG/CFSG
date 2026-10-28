module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.GeometryContract

/-!
# Interfaces for the remaining Suzuki Sylow and fusion argument

`SylowGeometry` records exactly the intermediate source conclusions of
Lemma 14.4(b), Lemma 14.5 and Lemma 14.6. In particular it identifies the
actual ambient Sylow subgroup and retains the quotient and conjugation
orbits. `QuotientFusion` means weak closure under the literal map from M
to M/A, with A normal in M. No inhabitant of either interface is asserted.

Independent proofs of the later complement/fusion argument and the final
Z-star descent may take these intermediates explicitly. The assembly in
`Fusion` must construct them before concluding the contradiction from the
original `Context`, `LocalGeometry`, torus semiregularity and embedding.
Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 14.4–14.9 and Proposition 14.1.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The source conclusions of 14.4(b), 14.5 and 14.6. This is a contract,
not an assertion that these conclusions have been established. -/
public structure SylowGeometry (g : LocalGeometry Z M z t m) : Prop where
  common_prime : ∃ s : ℕ, s.Prime ∧
    s ∣ Nat.card (centralizer (residualGenerated M z t : Set G)) ∧
    s ∣ 2 ^ (2 * m + 1) - 1
  M_product : (M : Set G) =
    (centralizer (closure (Z ∩ (M : Set G)) : Set G) : Set G) *
      (residualPairStabilizer M t : Set G)
  centralizer_normal :
    ((centralizer (closure (Z ∩ (M : Set G)) : Set G)).subgroupOf M).Normal
  centralizer_odd_index :
    Odd ((centralizer (closure (Z ∩ (M : Set G)) : Set G)).subgroupOf M).index
  S_sylow : ∃ V : Sylow 2 G, (V : Subgroup G) = g.S
  S_normal : (g.S.subgroupOf (normalizer (g.T : Set G))).Normal
  S_center : (center g.S).map g.S.subtype = closure (Z ∩ (M : Set G))
  T_normal : (g.T.subgroupOf g.S).Normal
  quotient_equiv : letI := T_normal
    Nonempty ((g.S ⧸ g.T.subgroupOf g.S) ≃* closure (Z ∩ (M : Set G)))
  central_mod_A : ⁅g.S, g.U⁆ ≤ closure (Z ∩ (M : Set G))
  normalizer_product : (normalizer (g.T : Set G) : Set G) =
    (g.S : Set G) * ((residualPairStabilizer M t ⊓ normalizer (g.U : Set G) : Subgroup G) : Set G)
  U_orbits : ∀ u ∈ g.U, u ≠ 1 → ∀ v : G,
    (∃ s ∈ g.S, MulAut.conj s u = v) ↔
      ∃ a ∈ closure (Z ∩ (M : Set G)), v = a * u

/-- Weak closure in the literal quotient `M / (A.subgroupOf M)`, using
the actual images of `U` and `S` and normality relative to `M`. -/
@[expose] public def QuotientFusion (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) : Prop :=
  let A := closure (Z ∩ (M : Set G))
  letI : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  let pi := QuotientGroup.mk' (A.subgroupOf M)
  BenderSuzuki.External.WeaklyClosedIn ((g.S.subgroupOf M).map pi)
    ((g.U.subgroupOf M).map pi)

end BenderSuzuki.ZD.SuzukiExclusion
