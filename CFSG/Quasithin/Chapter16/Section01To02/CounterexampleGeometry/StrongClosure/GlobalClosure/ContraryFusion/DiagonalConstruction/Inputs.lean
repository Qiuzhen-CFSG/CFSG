module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalControl
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.CentralDiagonal
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Remaining inputs to the central diagonal construction

These are proof contracts for two independent pieces of source mathematics:
the rootless-involution/four-group choice, and the two-group recognition and
rank facts. Neither assumes centrality of the diagonal. The assembly theorem
uses the actual normalizer of an outside conjugate, and keeps these premises
explicit until their producers prove them.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, from “A is not dihedral” to “Thus y ∈ Z(G)”.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

/-- The geometric choice before applying source (d). No centrality is assumed. -/
def DiagonalChoice {G : Type*} [Group G] (A₁ A₂ : Subgroup G) (t : G) : Prop :=
  ∃ u ∈ A₁, orderOf u = 4 ∧ orderOf (u * (t⁻¹ * u * t)) = 2 ∧
    (∃ v ∈ A₁, orderOf v = 2 ∧ v ∉ A₂ ∧
      (∀ w ∈ A₁, w ^ 2 ≠ v) ∧
      (∀ w ∈ centralizer ({t} : Set G), w ^ 2 ≠ v * (t⁻¹ * v * t)) ∧
      IsKleinFour (closure ({v * (t⁻¹ * v * t), u * (t⁻¹ * u * t)} : Set G))) ∧
    ∃ k : G, k ∉ intersectionGenerated A₁ A₂ ∧
      ((t ∈ conjugate A₁ k ∧
        u * (t⁻¹ * u * t) ∈ normalizer (conjugate A₁ k : Set G)) ∨
       (t ∈ conjugate A₂ k ∧
        u * (t⁻¹ * u * t) ∈ normalizer (conjugate A₂ k : Set G)))

/-- The two-group recognition input used only in the proper-centralizer branch. -/
def SmallFixedModel (G : Type*) [Group G] : Prop :=
  ∀ (B : Subgroup G), IsPGroup 2 B → TwoRankAtLeastTwo B →
    ∀ y : G, orderOf y = 2 → y ∈ normalizer (B : Set G) →
      Nat.card (B ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ 2 →
        DihedralOrSemidihedral B

/-- The rank input for the literal centralizers in source (d).
This is an obligation for the two-group producer, not a proved recognition result. -/
def DiagonalCentralizerRanks {G : Type*} [Group G]
    (S : Sylow 2 G) (A₁ A₂ : Subgroup G) : Prop :=
  ∀ (_h : Hypotheses S A₁ A₂) (t u : G),
    conjugate A₁ t = A₂ → conjugate A₂ t = A₁ → orderOf t = 2 →
    Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2 →
    (¬ DihedralOrSemidihedral A₁) → u ∈ A₁ → orderOf u = 4 →
    orderOf (u * (t⁻¹ * u * t)) = 2 →
    TwoRankAtLeastTwo (A₁.subgroupOf (centralizer ({u * (t⁻¹ * u * t)} : Set G))) ∧
    TwoRankAtLeastTwo (A₂.subgroupOf (centralizer ({u * (t⁻¹ * u * t)} : Set G)))


end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
