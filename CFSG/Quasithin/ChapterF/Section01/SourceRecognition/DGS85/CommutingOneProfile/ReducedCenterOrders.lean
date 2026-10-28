module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourceCenterOrders

/-!
# Original-completion application of the Chapter 11 center counts

Apply the source-path proofs after converting both original local quotient
markings through the actual reduced-group inclusion. Injectivity preserves
the neighboring-core equality, both source indices, the seed intersection,
and the corrected pair span. This supplies the original nonlinear order
inputs without a center-order or neighboring-core hypothesis.

The earlier local and catalogue inputs, path transitivity, and escaping
source-path choice remain explicit for final source assembly. Core upper
bounds, the remaining (11.8) layers, and path fixers are further obligations.
Source: DGS85, Groups and Graphs (1985), reduction pp.95--96 and
(11.6)(a,c), pp.172--174, with the pair count used on p.176.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- The original inclusion preserves the full neighboring-core equality and all four source counts. -/
theorem original_reduced_center_orders_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b)
    (hesc : ¬ (Z F₀ b).map (G₀).subtype ≤ (Q F₀ (g • b)).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices) :
    let qα := ((Q F₀ a).map (G₀).subtype).relIndex
      ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ b).map (G₀).subtype)
    let qβ := ((Q F₀ b).map (G₀).subtype).relIndex ((Z F₀ a).map (G₀).subtype)
    neighborCoreIntersection F₀ b = Z F₀ b ∧
      (neighborCoreIntersection F₀ b).map (G₀).subtype = (Z F₀ b).map (G₀).subtype ∧
      Nat.card ((Z F₀ b).map (G₀).subtype) = qβ ∧
      Nat.card ((Z F₀ a).map (G₀).subtype ⊓ (Q F₀ b).map (G₀).subtype : Subgroup G) = qα*qβ ∧
      Nat.card ((Z F₀ a).map (G₀).subtype) = qα*qβ^2 ∧
      Nat.card (pairSpan ((Z F₀ a).map (G₀).subtype) ((Z F₀ c).map (G₀).subtype)
        ((Q F₀ b).map (G₀).subtype)) = qα^2*qβ := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have he := source_neighbor_intersection_eq_center_on_escaping_path (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) g hga hgb
    (fun hh => hesc (map_mono hh)) ht p hp ha hbp hcp hgbp hgcp
  have hs := source_center_seed_pair_orders_on_escaping_path (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) g hga hgb
    (fun hh => hesc (map_mono hh)) ht p hp ha hbp hcp hgbp hgcp
  change Nat.card (Z F₀ b) = (Q F₀ b).relIndex (Z F₀ a) ∧
    Nat.card (Z F₀ a ⊓ Q F₀ b : Subgroup G₀) =
      (Q F₀ a).relIndex (Z F₀ c ⊓ Q F₀ b) * (Q F₀ b).relIndex (Z F₀ a) ∧
    Nat.card (Z F₀ a) = (Q F₀ a).relIndex (Z F₀ c ⊓ Q F₀ b) *
      ((Q F₀ b).relIndex (Z F₀ a))^2 ∧
    Nat.card (pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b)) =
      ((Q F₀ a).relIndex (Z F₀ c ⊓ Q F₀ b))^2 * (Q F₀ b).relIndex (Z F₀ a) at hs
  dsimp only
  refine ⟨he,congrArg (map (G₀).subtype) he,?_⟩
  simpa only [pairSpan,←map_inf _ _ _ (G₀).subtype_injective,←Subgroup.map_sup,
    card_map_of_injective (G₀).subtype_injective,
    relIndex_map_map_of_injective _ _ (G₀).subtype_injective] using hs

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
