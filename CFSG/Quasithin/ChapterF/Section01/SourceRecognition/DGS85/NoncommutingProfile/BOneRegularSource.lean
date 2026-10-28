module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneClosedPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneOrderSource

/-!
# The complete b=1 profile on the original F.1.11 markings

Apply the regularity proof to the actual reduced graph. The full reduced
Borel normalizes both source actors, and the reduced completion inclusion
carries their full centers to the original actor centers. Thus the same
original cores and natural quotient coordinates have (r,s)=(3,4) or (4,5),
with the stated center orders, genuine based path transitivity, and odd
length-s stabilizers. The extrema range over both vertex orbits, including the closed paths
allowed on source p.60.

The only action inputs are the marked earlier Chapter 6--7 data. Source
assembly retains their discharge. This completes the conditional b=1
application of DGS (10.5); it does not settle the b=2 alternatives or assert
an ambient completion isomorphism.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.156--157, the path
conventions pp.73--74, and reduction pp.95--96; AS F.1.9, pp.261--262.
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
local instance bOneRegularSourceAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
include h c₀ c₁ hactor₀ hactor₁

/-- The source actor markings discharge both Borel-normalization premises. -/
private theorem source_actor_normalization :
    (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₀.actor : Set (G₀ L S)) ∧
    (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₁.actor : Set (G₀ L S)) := by
  rw [hactor₀,hactor₁]
  exact ⟨reduced_borel_normalizes_source_actor h 0,reduced_borel_normalizes_source_actor h 1⟩

/-- Source 10.5(c,d) on the same reduced graph, with the full original actor centers. -/
theorem original_centers_reduced_path_parameters
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁)) :
    (centerIn (c₀.actor.map (G₀ L S).subtype) = ⊥ ∧
      centerIn (c₁.actor.map (G₀ L S).subtype) = ⊥ ∧
      HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4 ∧
      BasedPathTransitive (X := G₀ L S) (graph (reducedFamily L S)) 4 ∧
      ∀ {a b : Vertex (reducedFamily L S)} (p : (graph (reducedFamily L S)).Walk a b),
        IsSourcePath p → 4 ≤ p.length → Odd (Nat.card (pathFixer (X := G₀ L S) p))) ∨
    (Nat.card (centerIn (c₀.actor.map (G₀ L S).subtype)) = Nat.card k₀ ∧
      Nat.card (centerIn (c₁.actor.map (G₀ L S).subtype)) = Nat.card k₁ ∧
      HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5 ∧
      BasedPathTransitive (X := G₀ L S) (graph (reducedFamily L S)) 5 ∧
      ∀ {a b : Vertex (reducedFamily L S)} (p : (graph (reducedFamily L S)).Walk a b),
        IsSourcePath p → 5 ≤ p.length → Odd (Nat.card (pathFixer (X := G₀ L S) p))) := by
  obtain ⟨hn₀,hn₁⟩ := source_actor_normalization h c₀ c₁ hactor₀ hactor₁
  rw [←reduced_actor_center_map,←reduced_actor_center_map,
    map_eq_bot_iff_of_injective _ (G₀ L S).subtype_injective,
    map_eq_bot_iff_of_injective _ (G₀ L S).subtype_injective,
    card_map_of_injective (G₀ L S).subtype_injective,
    card_map_of_injective (G₀ L S).subtype_injective]
  exact bOne_source_path_parameters (reduced_triple h) c₀ c₁ hn₀ hn₁ E₀ E₁

/-- Both local quotient markings, core identities, natural core coordinates and the
exact path alternatives are retained in the original F.1.11 application. -/
theorem original_bOne_profile
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁)) :
    Nat.card k₀ = Nat.card k₁ ∧
    (parabolic L S 0).pCoreIn 2 =
      (Z (reducedFamily L S) (base (reducedFamily L S) false)).map (G₀ L S).subtype ∧
    (parabolic L S 1).pCoreIn 2 =
      (Z (reducedFamily L S) (base (reducedFamily L S) true)).map (G₀ L S).subtype ∧
    OriginalNaturalCoreCoordinates false c₀ ∧ OriginalNaturalCoreCoordinates true c₁ ∧
    ((centerIn (c₀.actor.map (G₀ L S).subtype) = ⊥ ∧
      centerIn (c₁.actor.map (G₀ L S).subtype) = ⊥ ∧
      HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4 ∧
      BasedPathTransitive (X := G₀ L S) (graph (reducedFamily L S)) 4 ∧
      ∀ {a b : Vertex (reducedFamily L S)} (p : (graph (reducedFamily L S)).Walk a b),
        IsSourcePath p → 4 ≤ p.length → Odd (Nat.card (pathFixer (X := G₀ L S) p))) ∨
    (Nat.card (centerIn (c₀.actor.map (G₀ L S).subtype)) = Nat.card k₀ ∧
      Nat.card (centerIn (c₁.actor.map (G₀ L S).subtype)) = Nat.card k₁ ∧
      HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5 ∧
      BasedPathTransitive (X := G₀ L S) (graph (reducedFamily L S)) 5 ∧
      ∀ {a b : Vertex (reducedFamily L S)} (p : (graph (reducedFamily L S)).Walk a b),
        IsSourcePath p → 5 ≤ p.length → Odd (Nat.card (pathFixer (X := G₀ L S) p)))) := by
  have hfields := paired_field_orders_eq (reduced_triple h) c₀ c₁ E₀
  obtain ⟨hq₀,hq₁⟩ := original_cores_eq_center_spans_of_actions h c₀ c₁
  obtain ⟨hc₀,hc₁⟩ := original_natural_cores_of_actions h c₀ c₁ E₀ E₁
  exact ⟨hfields,hq₀,hq₁,hc₀,hc₁,
    original_centers_reduced_path_parameters h c₀ c₁ hactor₀ hactor₁ E₀ E₁⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
