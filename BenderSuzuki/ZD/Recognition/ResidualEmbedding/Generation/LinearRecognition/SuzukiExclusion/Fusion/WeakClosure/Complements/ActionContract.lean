module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Interfaces

/-!
# The marked torus action on S/T

This contract specifies normalization and transitivity of the original K
on the literal nonidentity cosets of T in S. It is the action input used
in both parts of GLS4, Chapter 2, Lemma 14.7. No inhabitant is asserted;
Complements must construct it before claiming either source result.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The precise source torus action required in Lemma 14.7. The last field
states transitivity on nonidentity cosets using literal representatives. -/
public structure TorusQuotientAction (g : LocalGeometry Z M z t m) : Prop where
  normalizes_T : residualCommutator M t ≤ normalizer (g.T : Set G)
  normalizes_S : residualCommutator M t ≤ normalizer (g.S : Set G)
  transitive : ∀ a ∈ g.S, a ∉ g.T → ∀ b ∈ g.S, b ∉ g.T →
    ∃ k ∈ residualCommutator M t, b * (MulAut.conj k a)⁻¹ ∈ g.T


end BenderSuzuki.ZD.SuzukiExclusion
