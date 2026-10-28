module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# The remaining normalizer geometry for the diagonal choice

This is an explicit proof contract, not a proved source assertion. Its first
clause excludes square roots of the diagonal involution in C(t). Its second
clause uses a supplied diagonal four and chooses between its two remaining
generators. The chosen preimage has nontrivial square, and its diagonal
normalizes a literal outside conjugate factor containing t.

The selected v is outside Hᵍ. This condition must survive the permitted
Sylow reselection, and is stronger than merely lying outside A₂.
The algebraic consumer constructs v and the four, and proves that the chosen
preimage has order four. No centrality is assumed.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, from “as v ∉ Hᵍ” through “Then u² = z”.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

/-- The pair-action and Sylow-placement input, with both conjugators retained. -/
structure DiagonalNormalizerGeometry {G : Type*} [Group G]
    (A₁ A₂ : Subgroup G) (g t : G) : Prop where
  rootless : ∀ v ∈ A₁, orderOf v = 2 → v ∉ A₂ →
    v ∉ conjugate (intersectionGenerated A₁ A₂) g →
    ∀ w ∈ centralizer ({t} : Set G), w ^ 2 ≠ v * (t⁻¹ * v * t)
  placement : ∀ v ∈ A₁, orderOf v = 2 → v ∉ A₂ →
    v ∉ conjugate (intersectionGenerated A₁ A₂) g →
    ∀ u ∈ A₁, orderOf (u * (t⁻¹ * u * t)) = 2 →
    IsKleinFour (closure ({v * (t⁻¹ * v * t), u * (t⁻¹ * u * t)} : Set G)) →
    ∃ u' ∈ ({u, v * u} : Set G), u' ^ 2 ≠ 1 ∧
      ∃ k : G, k ∉ intersectionGenerated A₁ A₂ ∧
        ((t ∈ conjugate A₁ k ∧
          u' * (t⁻¹ * u' * t) ∈ normalizer (conjugate A₁ k : Set G)) ∨
         (t ∈ conjugate A₂ k ∧
          u' * (t⁻¹ * u' * t) ∈ normalizer (conjugate A₂ k : Set G)))

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
