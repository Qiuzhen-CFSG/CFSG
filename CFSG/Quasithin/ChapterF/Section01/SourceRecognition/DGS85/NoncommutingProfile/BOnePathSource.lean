module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOnePaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneOrderSource

/-!
# The Chapter 10 b=1 order and odd-path source application

For the actual reduced F.1.11 graph, the earlier marked natural actions and
source actor identities give equal fixed-field orders, the two exact core
orders and their literal common Sylow orders. In the center-free branch the
actual path stabilizers of length at least four are odd; with nontrivial
actor centers they are odd from length five. The full reduced Borel
normalizes the marked actors by the source Chapter 6 normalization.

The original parabolic cores and actor centers are transported through the
actual reduced completion inclusion. No identification of the original
F.1.11 S with the reduced common Sylow is made. The extremal regular-path
parameters r,s remain separate Chapter 10 obligations.

Source: DGS, *Groups and Graphs* (1985), (10.5)(a-d), pp.155–156,
using the marked Chapter 7 natural actions, (6.0), and the reduction
pp.95–96 (AS F.1.9, pp.261–262).
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory.WeakBNPair.RegularTree
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : HypothesisF11 L S)
    (c₀ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) false)
      (base (reducedFamily L S) true) k₀ W₀)
    (c₁ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) true)
      (base (reducedFamily L S) false) k₁ W₁)
    (hactor₀ : c₀.actor =
      ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 0).subgroupOf (G₀ L S))
    (hactor₁ : c₁.actor =
      ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 1).subgroupOf (G₀ L S))
include h c₀ c₁ hactor₀ hactor₁

/-- The actual reduced graph has odd stabilizers on all paths of length at least five. -/
theorem reduced_pathFixer_odd_of_actions
    {a b : Vertex (reducedFamily L S)} (p : (graph (reducedFamily L S)).Walk a b)
    (hp : p.IsPath) (hlen : 5 ≤ p.length) :
    Odd (Nat.card (pathFixer (X := G₀ L S) p)) := by
  have hn₀ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₀.actor : Set (G₀ L S)) := by
    rw [hactor₀]
    exact reduced_borel_normalizes_source_actor h 0
  have hn₁ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₁.actor : Set (G₀ L S)) := by
    rw [hactor₁]
    exact reduced_borel_normalizes_source_actor h 1
  exact pathFixer_odd_of_five_le (reduced_triple h) c₀ c₁ hn₀ hn₁ p hp hlen

/-- The stabilizer is embedded through the literal reduced-to-original inclusion. -/
theorem reduced_pathFixer_original_image_odd
    {a b : Vertex (reducedFamily L S)} (p : (graph (reducedFamily L S)).Walk a b)
    (hp : p.IsPath) (hlen : 5 ≤ p.length) :
    Odd (Nat.card ((pathFixer (X := G₀ L S) p).map (G₀ L S).subtype)) := by
  rw [card_map_of_injective (G₀ L S).subtype_injective]
  exact reduced_pathFixer_odd_of_actions h c₀ c₁ hactor₀ hactor₁ p hp hlen

local instance bOnePathSourceFieldAlgebra {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k :=
  ZMod.algebra k 2

/-- The original core-product order dichotomy now includes actual odd path
stabilizers at lengths four and five, respectively, in the same reduced graph. -/
theorem original_core_orders_with_reduced_pathFixers
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁)) :
    Nat.card k₀ = Nat.card k₁ ∧
    ((centerIn (c₀.actor.map (G₀ L S).subtype) = ⊥ ∧
      centerIn (c₁.actor.map (G₀ L S).subtype) = ⊥ ∧
      Nat.card ((parabolic L S 0).pCoreIn 2) = Nat.card k₀ ^ 2 ∧
      Nat.card ((parabolic L S 1).pCoreIn 2) = Nat.card k₁ ^ 2 ∧
      Nat.card ((parabolic L S 0).pCoreIn 2 ⊔ (parabolic L S 1).pCoreIn 2 : Subgroup G) =
        Nat.card k₀ ^ 3 ∧
      ∀ {a b : Vertex (reducedFamily L S)} (p : (graph (reducedFamily L S)).Walk a b),
        p.IsPath → 4 ≤ p.length → Odd (Nat.card (pathFixer (X := G₀ L S) p))) ∨
    (Nat.card (centerIn (c₀.actor.map (G₀ L S).subtype)) = Nat.card k₀ ∧
      Nat.card (centerIn (c₁.actor.map (G₀ L S).subtype)) = Nat.card k₁ ∧
      Nat.card ((parabolic L S 0).pCoreIn 2) = Nat.card k₀ ^ 3 ∧
      Nat.card ((parabolic L S 1).pCoreIn 2) = Nat.card k₁ ^ 3 ∧
      Nat.card ((parabolic L S 0).pCoreIn 2 ⊔ (parabolic L S 1).pCoreIn 2 : Subgroup G) =
        Nat.card k₀ ^ 4 ∧
      ∀ {a b : Vertex (reducedFamily L S)} (p : (graph (reducedFamily L S)).Walk a b),
        p.IsPath → 5 ≤ p.length → Odd (Nat.card (pathFixer (X := G₀ L S) p)))) := by
  obtain ⟨hfields,hcases⟩ := original_center_and_core_product_orders h c₀ c₁ E₀ E₁ hactor₀ hactor₁
  refine ⟨hfields,?_⟩
  rcases hcases with ⟨hc₀,hc₁,hq₀,hq₁,hS⟩ | ⟨hc₀,hc₁,hq₀,hq₁,hS⟩
  · left
    refine ⟨hc₀,hc₁,hq₀,hq₁,hS,?_⟩
    have hn₀ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₀.actor : Set (G₀ L S)) := by
      rw [hactor₀]
      exact reduced_borel_normalizes_source_actor h 0
    have hn₁ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₁.actor : Set (G₀ L S)) := by
      rw [hactor₁]
      exact reduced_borel_normalizes_source_actor h 1
    rw [←reduced_actor_center_map,map_eq_bot_iff_of_injective _ (G₀ L S).subtype_injective] at hc₀ hc₁
    exact fun {_ _} p hp hl => pathFixer_odd_of_four_le_of_centers_bot
      (reduced_triple h) c₀ c₁ hn₀ hn₁ hc₀ hc₁ p hp hl
  · right
    exact ⟨hc₀,hc₁,hq₀,hq₁,hS,fun {_ _} p hp hl =>
      reduced_pathFixer_odd_of_actions h c₀ c₁ hactor₀ hactor₁ p hp hl⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
