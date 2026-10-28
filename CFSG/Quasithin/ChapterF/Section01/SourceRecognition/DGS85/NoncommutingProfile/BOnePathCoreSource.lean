module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOnePathCores
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOnePathSource

/-!
# Exact short-path Sylows on the original reduced F.1.11 graph

The two earlier natural actions, with their actual source actor markings,
give the normal Sylow of each reduced path stabilizer as the literal
intersection of its interior cores. Its image in the original completion
is transported through the reduced-to-original inclusion, and the orders
q²c, qc, c retain the full original actor center. The parity dichotomy gives
sharp oddness thresholds on this same graph.

The source actor identities discharge Borel normalization; neither a local
kernel substitution nor identification of the reduced Sylow with the
original F.1.11 S is used. Endpoint transitivity and hence exact DGS r,s
remain distinct obligations of Chapter 10.

Source: DGS, *Groups and Graphs* (1985), (10.5)(c,d), p.156, with
reduction pp.95--96 (AS F.1.9, pp.261--262).
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

private theorem source_normalizes_actors :
    (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₀.actor : Set (G₀ L S)) ∧
    (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₁.actor : Set (G₀ L S)) := by
  rw [hactor₀,hactor₁]
  exact ⟨reduced_borel_normalizes_source_actor h 0,reduced_borel_normalizes_source_actor h 1⟩

/-- The unique reduced path Sylow and its two-core have the same literal
interior-core intersection, including after the original completion inclusion. -/
theorem reduced_path_sylow_core_original_image
    {a b : Vertex (reducedFamily L S)} (p : (graph (reducedFamily L S)).Walk a b)
    (hp : p.IsPath) (hlen : 2 ≤ p.length)
    (T : Sylow 2 (pathFixer (X := G₀ L S) p)) :
    (pathFixer (X := G₀ L S) p).pCoreIn 2 = pathInteriorCore p ∧
    ((T : Subgroup (pathFixer (X := G₀ L S) p)).map
      (pathFixer (X := G₀ L S) p).subtype).map (G₀ L S).subtype =
        (pathInteriorCore p).map (G₀ L S).subtype := by
  obtain ⟨hn₀,hn₁⟩ := source_normalizes_actors h c₀ c₁ hactor₀ hactor₁
  exact ⟨pathFixer_core_eq_interior (reduced_triple h) c₀ c₁ hn₀ hn₁ p hp hlen,
    congrArg (map (G₀ L S).subtype)
      (pathFixer_sylow_eq_interior (reduced_triple h) c₀ c₁ hn₀ hn₁ p hp hlen T)⟩

local instance pathCoreSourceFieldAlgebra {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k :=
  ZMod.algebra k 2

/-- Exact orders of the actual reduced short-path Sylows, expressed with the
full original actor center through its given inclusion. -/
theorem reduced_short_path_sylow_original_center_orders
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    {a b : Vertex (reducedFamily L S)} (p : (graph (reducedFamily L S)).Walk a b)
    (hp : p.IsPath) (T : Sylow 2 (pathFixer (X := G₀ L S) p)) :
    (p.length = 2 → Nat.card T =
      Nat.card k₀ ^ 2 * Nat.card (centerIn (c₀.actor.map (G₀ L S).subtype))) ∧
    (p.length = 3 → Nat.card T =
      Nat.card k₀ * Nat.card (centerIn (c₀.actor.map (G₀ L S).subtype))) ∧
    (p.length = 4 → Nat.card T = Nat.card (centerIn (c₀.actor.map (G₀ L S).subtype))) := by
  obtain ⟨hn₀,hn₁⟩ := source_normalizes_actors h c₀ c₁ hactor₀ hactor₁
  rw [←reduced_actor_center_map,card_map_of_injective (G₀ L S).subtype_injective]
  exact short_path_sylow_orders (reduced_triple h) c₀ c₁ hn₀ hn₁ E₀ E₁ p hp T

/-- The sharp parity alternative on the actual reduced graph, with the
full centers marked in the original completion. -/
theorem original_centers_reduced_path_odd_thresholds
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁)) :
    (centerIn (c₀.actor.map (G₀ L S).subtype) = ⊥ ∧
      centerIn (c₁.actor.map (G₀ L S).subtype) = ⊥ ∧
      ∀ {a b : Vertex (reducedFamily L S)} (p : (graph (reducedFamily L S)).Walk a b),
        p.IsPath → 3 ≤ p.length →
          (Odd (Nat.card (pathFixer (X := G₀ L S) p)) ↔ 4 ≤ p.length)) ∨
    (Nat.card (centerIn (c₀.actor.map (G₀ L S).subtype)) = Nat.card k₀ ∧
      Nat.card (centerIn (c₁.actor.map (G₀ L S).subtype)) = Nat.card k₁ ∧
      ∀ {a b : Vertex (reducedFamily L S)} (p : (graph (reducedFamily L S)).Walk a b),
        p.IsPath → 3 ≤ p.length →
          (Odd (Nat.card (pathFixer (X := G₀ L S) p)) ↔ 5 ≤ p.length)) := by
  obtain ⟨hn₀,hn₁⟩ := source_normalizes_actors h c₀ c₁ hactor₀ hactor₁
  rw [←reduced_actor_center_map,←reduced_actor_center_map,
    map_eq_bot_iff_of_injective _ (G₀ L S).subtype_injective,
    map_eq_bot_iff_of_injective _ (G₀ L S).subtype_injective,
    card_map_of_injective (G₀ L S).subtype_injective,
    card_map_of_injective (G₀ L S).subtype_injective]
  exact pathFixer_odd_thresholds (reduced_triple h) c₀ c₁ hn₀ hn₁ E₀ E₁

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
