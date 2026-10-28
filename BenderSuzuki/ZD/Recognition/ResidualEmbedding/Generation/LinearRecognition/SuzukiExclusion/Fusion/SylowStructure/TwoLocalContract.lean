module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.Factorization

/-!+# The remaining two-local conclusions of the Suzuki argument

This is the output contract of GLS4, Chapter 2, Lemma 14.6. The preceding
factorization has already proved that S centralizes A and T is normal in S.
The quotient below is the actual group S/T with that normality instance.

No inhabitant is asserted here. The proof of this contract must still supply
ambient Sylow maximality, the center, the quotient isomorphism, normality in
N_G(T), its product decomposition, and the full conjugation orbits on Au.
The enclosing SylowStructure assembly retains the original SylowGeometry
target. Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemma 14.6.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The source conclusions still needed from Lemma 14.6. -/
public structure TwoLocalSylowGeometry (g : LocalGeometry Z M z t m) : Prop where
  S_sylow : ∃ V : Sylow 2 G, (V : Subgroup G) = g.S
  S_normal : (g.S.subgroupOf (normalizer (g.T : Set G))).Normal
  S_center : (center g.S).map g.S.subtype = closure (Z ∩ (M : Set G))
  quotient_equiv : letI := g.T_normal_in_S
    Nonempty ((g.S ⧸ g.T.subgroupOf g.S) ≃* closure (Z ∩ (M : Set G)))
  central_mod_A : ⁅g.S, g.U⁆ ≤ closure (Z ∩ (M : Set G))
  normalizer_product : (normalizer (g.T : Set G) : Set G) =
    (g.S : Set G) *
      ((residualPairStabilizer M t ⊓ normalizer (g.U : Set G) : Subgroup G) : Set G)
  U_orbits : ∀ u ∈ g.U, u ≠ 1 → ∀ v : G,
    (∃ s ∈ g.S, MulAut.conj s u = v) ↔
      ∃ a ∈ closure (Z ∩ (M : Set G)), v = a * u

end BenderSuzuki.ZD.SuzukiExclusion
