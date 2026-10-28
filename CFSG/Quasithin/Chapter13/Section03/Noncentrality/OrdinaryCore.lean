module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryParabolic
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal.Definitions
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.CorePlaneSource

/-!
# The literal ordinary augmentation-core exclusion in 13.3.14(g)

If the selected moved module W_K is marked as the five-dimensional
augmentation core of the six-letter alternating group, the original seed
maps to an invariant plane in its natural quotient. The concrete A₄
core-plane calculation then centralizes the seed by the original point
actor's two-core. This contradicts the unconditional seed movement obtained
from the ordinary natural action.

`OrdinaryCorePlaneCoordinates` retains the actual subgroup W_K, actor,
coordinates, and natural quotient plane. Constructing this marking from
B.5 and the component rows is the subsequent source obligation. No
faithfulness of raw J or incorrect symmetric-five module is assumed.
Source: Aschbacher–Smith, 13.3.14(g), printed p.893.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The original actor preserves its component's actual commutator module. -/
theorem ordinary_actor_normalizes_movedModule (K A T : Subgroup G)
    (hn : A ≤ normalizer (K : Set G)) :
    A ≤ normalizer (Diagonal.movedModule K A T : Set G) := by
  let J := Diagonal.localGroup K A T
  let W := reducedTwoSubgroup J
  have hWN : J ≤ normalizer (W.map J.subtype : Set G) := by
    have hw := W.le_normalizer_map J.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hw
    exact hw
  have hAJ : A ≤ J := le_sup_right.trans le_sup_left
  have hAW : A ≤ normalizer (Diagonal.reducedModule K A T : Set G) := hAJ.trans hWN
  intro a ha
  rw [Diagonal.movedModule, mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hn ha),
    mem_normalizer_iff_map_conj_eq.mp (hAW ha)]

variable {T : Sylow 2 G}
  {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

structure OrdinaryCorePlaneCoordinates (d : NaturalSetup T L V P E U M H) (K : Subgroup G)
    (hn : sourceOne L T P ≤ normalizer (Diagonal.movedModule K (sourceOne L T P) T : Set G)) where
  seed_le : U ≤ Diagonal.movedModule K (sourceOne L T P) T
  actor : sourceOne L T P →* alternatingGroup (Fin 6)
  actor_four : actor.range ≃* alternatingGroup (Fin 4)
  coordinates : Diagonal.movedModule K (sourceOne L T P) T ≃* Multiplicative (core (Fin 6))
  equivariant : ∀ (a : sourceOne L T P) (w : Diagonal.movedModule K (sourceOne L T P) T),
    (coordinates ((Diagonal.movedModule K (sourceOne L T P) T).normalizerMonoidHom
      ⟨a,hn a.property⟩ w)).toAdd =
      alternatingCoreRepresentation (Fin 6) (actor a) (coordinates w).toAdd
  plane : Submodule (ZMod 2) (natural (Fin 6))
  plane_card : Nat.card plane = 4
  plane_invariant : ∀ a : sourceOne L T P, ∀ v ∈ plane,
    alternatingNaturalRepresentation (Fin 6) (actor a) v ∈ plane
  seed_in_plane : ∀ (u : G) (hu : u ∈ U),
    coreToNatural (Fin 6) (coordinates ⟨u,seed_le hu⟩).toAdd ∈ plane

/-- The actual core-plane marking contradicts the original seed movement. -/
theorem ordinary_core_plane_contradiction
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) (K : Subgroup G)
    (hn : sourceOne L T P ≤ normalizer (Diagonal.movedModule K (sourceOne L T P) T : Set G))
    (c : OrdinaryCorePlaneCoordinates d K hn) : False := by
  have hz := source_core_plane_centralized (sourceOne L T P)
    (Diagonal.movedModule K (sourceOne L T P) T) U ordinary_point_residual_twoPerfect
    hn c.seed_le c.actor c.actor_four c.coordinates c.equivariant c.plane c.plane_card
    c.plane_invariant c.seed_in_plane
  exact ordinary_point_core_moves_seed d e
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))

/-- Reduction (g), once the selected component module supplies its true core coordinates. -/
theorem ordinary_reduction_g_of_core_coordinates
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) (K : Subgroup G)
    (hcoords : sourceOne L T P ≤ K →
      ∃ hn : sourceOne L T P ≤ normalizer (Diagonal.movedModule K (sourceOne L T P) T : Set G),
        Nonempty (OrdinaryCorePlaneCoordinates d K hn)) : ¬sourceOne L T P ≤ K := by
  intro hle
  obtain ⟨hn,⟨c⟩⟩ := hcoords hle
  exact ordinary_core_plane_contradiction d e K hn c

/-- The literal selected-component use of (g). The existing point-actor
normalizer is sufficient to supply the moved-module normalizer. -/
theorem ordinary_reduction_g_of_source_coordinates
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) (K : Subgroup H)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hcoords : sourceOne L T P ≤ K.map H.subtype →
      ∀ hnW : sourceOne L T P ≤
        normalizer (Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T : Set G),
        Nonempty (OrdinaryCorePlaneCoordinates d (K.map H.subtype) hnW)) :
    ¬sourceOne L T P ≤ K.map H.subtype := by
  have hnG : sourceOne L T P ≤ normalizer (K.map H.subtype : Set G) := by
    have hh := (map_mono hn).trans (K.le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le (ordinary_point_residual_le_point d)] at hh
  intro hle
  have hnW := ordinary_actor_normalizes_movedModule (K.map H.subtype)
    (sourceOne L T P) T hnG
  obtain ⟨c⟩ := hcoords hle hnW
  exact ordinary_core_plane_contradiction d e (K.map H.subtype) hnW c

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
