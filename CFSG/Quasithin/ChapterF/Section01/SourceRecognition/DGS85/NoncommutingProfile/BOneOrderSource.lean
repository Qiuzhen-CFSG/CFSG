module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneCenters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneActionSource

/-!
# The b=1 order dichotomy on the original F.1.11 subgroups

The literal reduced-completion inclusion maps each reduced core to the
corresponding full original parabolic core. It therefore maps the common
Sylow product to the product of those original cores, preserving its order
and Sylow status in the embedded reduced endpoints.

For the Chapter 6 actor S₀Gδ*, with S₀=O₂(B₀), the actual reduced Borel
normalizes both factors. Thus the source actor markings discharge the
normalization premises of the paired-center calculation. The transported
centers are full centers, and the two source D intersections retain the
actual chosen conjugators. No identification of the original F.1.11 S
with this reduced common Sylow, and no ambient recognition, is asserted.

This is the order portion of DGS, *Groups and Graphs* (1985), 10.5(c),
p.156, using 6.0 on p.118 and the reduction on pp.95--96 (AS F.1.9,
pp.261--262). The marked natural actions and their source-actor identities
remain earlier Chapter 6--7 inputs for source assembly. The r,s and odd
path-stabilizer clauses, and the b=2 alternatives, remain with Chapter 10.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The reduced core product maps to the two full original parabolic cores. -/
theorem original_core_product_map (h : HypothesisF11 L S) :
    (Q (reducedFamily L S) (base (reducedFamily L S) false) ⊔
      Q (reducedFamily L S) (base (reducedFamily L S) true)).map (G₀ L S).subtype =
        (parabolic L S 0).pCoreIn 2 ⊔ (parabolic L S 1).pCoreIn 2 := by
  rw [Subgroup.map_sup,reduced_base_Q_map h false,reduced_base_Q_map h true]
  rfl

/-- The literal actor S₀Gδ* is normalized by the whole reduced Borel. -/
theorem reduced_borel_normalizes_source_actor (h : HypothesisF11 L S) (i : Fin 2) :
    (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer
      (((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S i).subgroupOf (G₀ L S) : Set (G₀ L S)) := by
  have hnCore : B₀ L S ≤ normalizer ((B₀ L S).pCoreIn 2 : Set G) :=
    (B₀ L S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (B₀ L S)))
  have hnStar : B₀ L S ≤ normalizer (starredParabolic L S i : Set G) :=
    (B₀_le h).trans ((commonBorel_le_parabolic (L := L) (S := S) i).trans
      ((normal_subgroupOf_iff_le_normalizer (starredParabolic_le (L := L) (S := S) i)).mp
        (h.starredParabolic_normal i)))
  have hn := (le_inf hnCore hnStar).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact (comap_mono hn).trans
    (((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S i).le_normalizer_comap (G₀ L S).subtype)

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : HypothesisF11 L S)
    (c₀ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) false)
      (base (reducedFamily L S) true) k₀ W₀)
    (c₁ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) true)
      (base (reducedFamily L S) false) k₁ W₁)

include h c₀ c₁ in
/-- The original core product is Sylow in both actual embedded reduced endpoints. -/
theorem original_core_product_sylow_reduced :
    Stellmacher.IsSylowSubgroupIn
        ((parabolic L S 0).pCoreIn 2 ⊔ (parabolic L S 1).pCoreIn 2) (P₀ L S 0) ∧
      Stellmacher.IsSylowSubgroupIn
        ((parabolic L S 0).pCoreIn 2 ⊔ (parabolic L S 1).pCoreIn 2) (P₀ L S 1) := by
  let := finite_endpoints (reduced_triple h)
  obtain ⟨h₀,h₁⟩ := paired_core_product_sylow (reduced_triple h) c₀ c₁
  have transport (i : Fin 2)
      (hs : Stellmacher.IsSylowSubgroupIn
        (Q (reducedFamily L S) (base (reducedFamily L S) false) ⊔
          Q (reducedFamily L S) (base (reducedFamily L S) true))
          ((P₀ L S i).subgroupOf (G₀ L S))) :
      Stellmacher.IsSylowSubgroupIn
        ((parabolic L S 0).pCoreIn 2 ⊔ (parabolic L S 1).pCoreIn 2) (P₀ L S i) := by
    have hle : P₀ L S i ≤ G₀ L S := by
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    let : Finite ((P₀ L S i).subgroupOf (G₀ L S)) := by
      fin_cases i
      · exact finite_endpoints (reduced_triple h) false
      · exact finite_endpoints (reduced_triple h) true
    have hh := Theory.GroupTheory.AmalgamGraph.sylow_witness_map
      (G₀ L S).subtype (G₀ L S).subtype_injective _ _ hs
    rw [map_subgroupOf_eq_of_le hle,original_core_product_map h] at hh
    exact hh
  exact ⟨transport 0 h₀,transport 1 h₁⟩

local instance bOneOrderSourceFieldAlgebra {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k := ZMod.algebra k 2

include h c₀ c₁ in
/-- The source actor markings give the center, core and product order dichotomy in original G. -/
theorem original_center_and_core_product_orders
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hactor₀ : c₀.actor =
      ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 0).subgroupOf (G₀ L S))
    (hactor₁ : c₁.actor =
      ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 1).subgroupOf (G₀ L S)) :
    Nat.card k₀ = Nat.card k₁ ∧
    ((centerIn (c₀.actor.map (G₀ L S).subtype) = ⊥ ∧
      centerIn (c₁.actor.map (G₀ L S).subtype) = ⊥ ∧
      Nat.card ((parabolic L S 0).pCoreIn 2) = Nat.card k₀ ^ 2 ∧
      Nat.card ((parabolic L S 1).pCoreIn 2) = Nat.card k₁ ^ 2 ∧
      Nat.card ((parabolic L S 0).pCoreIn 2 ⊔ (parabolic L S 1).pCoreIn 2 : Subgroup G) =
        Nat.card k₀ ^ 3) ∨
    (Nat.card (centerIn (c₀.actor.map (G₀ L S).subtype)) = Nat.card k₀ ∧
      Nat.card (centerIn (c₁.actor.map (G₀ L S).subtype)) = Nat.card k₁ ∧
      Nat.card ((parabolic L S 0).pCoreIn 2) = Nat.card k₀ ^ 3 ∧
      Nat.card ((parabolic L S 1).pCoreIn 2) = Nat.card k₁ ^ 3 ∧
      Nat.card ((parabolic L S 0).pCoreIn 2 ⊔ (parabolic L S 1).pCoreIn 2 : Subgroup G) =
        Nat.card k₀ ^ 4)) := by
  have hn₀ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₀.actor : Set (G₀ L S)) := by
    rw [hactor₀]
    exact reduced_borel_normalizes_source_actor h 0
  have hn₁ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₁.actor : Set (G₀ L S)) := by
    rw [hactor₁]
    exact reduced_borel_normalizes_source_actor h 1
  refine ⟨paired_field_orders_eq (reduced_triple h) c₀ c₁ E₀,?_⟩
  have hm₀ := reduced_base_Q_map h false
  have hm₁ := reduced_base_Q_map h true
  simp only [Bool.false_eq_true,↓reduceIte] at hm₀ hm₁
  have hq₀ : Nat.card ((parabolic L S 0).pCoreIn 2) =
      Nat.card (Q (reducedFamily L S) (base (reducedFamily L S) false)) := by
    rw [←hm₀,card_map_of_injective (G₀ L S).subtype_injective]
  have hq₁ : Nat.card ((parabolic L S 1).pCoreIn 2) =
      Nat.card (Q (reducedFamily L S) (base (reducedFamily L S) true)) := by
    rw [←hm₁,card_map_of_injective (G₀ L S).subtype_injective]
  have hs : Nat.card ((parabolic L S 0).pCoreIn 2 ⊔ (parabolic L S 1).pCoreIn 2 : Subgroup G) =
      Nat.card (Q (reducedFamily L S) (base (reducedFamily L S) false) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) true) : Subgroup (G₀ L S)) := by
    rw [←original_core_product_map h,card_map_of_injective (G₀ L S).subtype_injective]
  rw [hq₀,hq₁,hs,←reduced_actor_center_map,←reduced_actor_center_map,
    card_map_of_injective (G₀ L S).subtype_injective,
    card_map_of_injective (G₀ L S).subtype_injective,
    map_eq_bot_iff_of_injective _ (G₀ L S).subtype_injective,
    map_eq_bot_iff_of_injective _ (G₀ L S).subtype_injective]
  exact paired_core_product_order_dichotomy (reduced_triple h) c₀ c₁ E₀ E₁ hn₀ hn₁

include h c₀ c₁ in
/-- The literal D intersections keep their conjugators and have paired orders one or q. -/
theorem original_literal_D_order_dichotomy
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hactor₀ : c₀.actor =
      ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 0).subgroupOf (G₀ L S))
    (hactor₁ : c₁.actor =
      ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 1).subgroupOf (G₀ L S)) :
    ∃ g₀ : c₀.actor, ∃ g₁ : c₁.actor,
      (D (reducedFamily L S) (base (reducedFamily L S) true)
        ((g₀ : G₀ L S) • base (reducedFamily L S) true)).map (G₀ L S).subtype =
          centerIn (c₀.actor.map (G₀ L S).subtype) ∧
      (D (reducedFamily L S) (base (reducedFamily L S) false)
        ((g₁ : G₀ L S) • base (reducedFamily L S) false)).map (G₀ L S).subtype =
          centerIn (c₁.actor.map (G₀ L S).subtype) ∧
      ((Nat.card (D (reducedFamily L S) (base (reducedFamily L S) true)
          ((g₀ : G₀ L S) • base (reducedFamily L S) true)) = 1 ∧
        Nat.card (D (reducedFamily L S) (base (reducedFamily L S) false)
          ((g₁ : G₀ L S) • base (reducedFamily L S) false)) = 1) ∨
       (Nat.card (D (reducedFamily L S) (base (reducedFamily L S) true)
          ((g₀ : G₀ L S) • base (reducedFamily L S) true)) = Nat.card k₀ ∧
        Nat.card (D (reducedFamily L S) (base (reducedFamily L S) false)
          ((g₁ : G₀ L S) • base (reducedFamily L S) false)) = Nat.card k₁)) := by
  obtain ⟨g₀,g₁,he₀,he₁⟩ := original_literal_D_centers_of_actions h c₀ c₁
  refine ⟨g₀,g₁,he₀,he₁,?_⟩
  have hc₀ := congrArg (fun A : Subgroup G => Nat.card A) he₀
  have hc₁ := congrArg (fun A : Subgroup G => Nat.card A) he₁
  rw [card_map_of_injective (G₀ L S).subtype_injective] at hc₀ hc₁
  rw [hc₀,hc₁]
  rcases (original_center_and_core_product_orders h c₀ c₁ E₀ E₁ hactor₀ hactor₁).2 with hb | hq
  · exact Or.inl ⟨card_eq_one.mpr hb.1,card_eq_one.mpr hb.2.1⟩
  · exact Or.inr ⟨hq.1,hq.2.1⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
