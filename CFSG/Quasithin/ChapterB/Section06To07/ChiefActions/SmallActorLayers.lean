module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallActors
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SolvableActorLayers
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallSolvableCubic

/-!
# Matched small chief actors and offender layers

The four source alternatives pair S₃ with S₃, its two-factor wreath group
with S₃ × S₃, S₅ with S₅, and its wreath group with S₅ × S₅. The single
and paired markings retain this correspondence. The solvable alternatives
use the same actual source factor count for both group identifications.

Transport along the literal action-kernel quotient preserves both entries.
Identifying an actual Thompson image with the offender subgroup therefore
retains the source's respective pairing of ambient and layer types.

Source: Aschbacher–Smith, original 3.1.9(5), printed p.578, and 15.1.12(3).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource

/-- The four ambient actors paired with their corresponding offender layers. -/
def ChiefSmallActorLayerTypes (D L : Type*) [Group D] [Group L] : Prop :=
  (Nonempty (D ≃* Equiv.Perm (Fin 3)) ∧ Nonempty (L ≃* Equiv.Perm (Fin 3))) ∨
  (Nonempty (D ≃* RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) ∧
    Nonempty (L ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) ∨
  (Nonempty (D ≃* Equiv.Perm (Fin 5)) ∧ Nonempty (L ≃* Equiv.Perm (Fin 5))) ∨
  (Nonempty (D ≃* RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))) ∧
    Nonempty (L ≃* (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5))))

theorem ChiefSmallActorLayerTypes.of_equiv
    {D L E K : Type*} [Group D] [Group L] [Group E] [Group K]
    (h : ChiefSmallActorLayerTypes D L) (e : E ≃* D) (k : K ≃* L) :
    ChiefSmallActorLayerTypes E K := by
  rcases h with ⟨⟨a⟩,⟨b⟩⟩ | ⟨⟨a⟩,⟨b⟩⟩ | ⟨⟨a⟩,⟨b⟩⟩ | ⟨⟨a⟩,⟨b⟩⟩
  · exact Or.inl ⟨⟨e.trans a⟩,⟨k.trans b⟩⟩
  · exact Or.inr (Or.inl ⟨⟨e.trans a⟩,⟨k.trans b⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨⟨e.trans a⟩,⟨k.trans b⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨⟨e.trans a⟩,⟨k.trans b⟩⟩))

/-- Identify an actual image subgroup with the proved offender layer. -/
theorem ChiefSmallActorLayerTypes.of_subgroup_eq
    {D E : Type*} [Group D] [Group E] {Y N : Subgroup D}
    (h : ChiefSmallActorLayerTypes E Y) (hN : N = Y) :
    ChiefSmallActorLayerTypes E N := by
  subst N
  exact h

/-- The literal centralizer quotient has the same ambient type and layer. -/
theorem ChiefSmallActorLayerTypes.quotient_actor
    {D L W : Type*} [Group D] [Group L] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W}
    (h : ChiefSmallActorLayerTypes (actionImage ρ) L) :
    ChiefSmallActorLayerTypes (D ⧸ (actionHom ρ).ker) L :=
  h.of_equiv (QuotientGroup.quotientKerEquivOfSurjective
    (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective) (MulEquiv.refl L)

variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The marked single-five branch pairs the full actor with its actual layer. -/
theorem minimalParabolic_chief_five_actor_layer_types
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (S : Sylow 2 D) (hS : IsMinimalParabolicOver S ⊤)
    (hff : IsFFModule (imageRepresentation ρ))
    (hmark : ChiefFiveMarkedSection (imageRepresentation ρ)) :
    Nonempty (actionImage ρ ≃* Equiv.Perm (Fin 5)) ∧
      Nonempty (offenderSubgroup (imageRepresentation ρ) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨⟨e⟩,hY⟩ := minimalParabolic_chief_five_of_marked ρ S hS hff hmark
  exact ⟨⟨e.groupEquiv⟩,⟨((MulEquiv.subgroupCongr hY).trans Subgroup.topEquiv).trans e.groupEquiv⟩⟩

/-- The same paired-five marking gives the wreath actor and product layer. -/
theorem minimalParabolic_chief_five_pair_actor_layer_types
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (S : Sylow 2 D) (hS : IsMinimalParabolicOver S ⊤)
    (hff : IsFFModule (imageRepresentation ρ))
    (hmark : ChiefFivePairMarkedSection (imageRepresentation ρ)) :
    Nonempty (actionImage ρ ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))) ∧
      Nonempty (offenderSubgroup (imageRepresentation ρ) ≃*
        (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5))) := by
  obtain ⟨e,_⟩ := minimalParabolic_chief_five_pair_of_marked ρ S hS hff hmark
  obtain ⟨d,⟨c⟩⟩ := hmark
  exact ⟨⟨e.groupEquiv⟩,⟨c.action.groupEquiv⟩⟩

/-- Each small chief branch pairs its full actor with the corresponding
actual offender layer, using one source factor count in the solvable cases. -/
theorem minimalParabolic_chief_small_actor_layer_types
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    {K : GroupClass} (hD : IsSQTK K D)
    (S : Sylow 2 D) (hS : IsMinimalParabolicOver S ⊤)
    (hff : IsFFModule (imageRepresentation ρ))
    (hsmall : SmallNaturalWreathAction (imageRepresentation ρ) ∨
      ChiefFiveMarkedSection (imageRepresentation ρ) ∨
      ChiefFivePairMarkedSection (imageRepresentation ρ)) :
    ChiefSmallActorLayerTypes (actionImage ρ) (offenderSubgroup (imageRepresentation ρ)) := by
  rcases hsmall with hsmall | hsmall | hsmall
  · rcases chief_solvable_image_actor_and_offender_types ρ hD S hS hff hsmall.solvable with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl
      (minimalParabolic_chief_five_actor_layer_types ρ S hS hff hsmall)))
  · exact Or.inr (Or.inr (Or.inr
      (minimalParabolic_chief_five_pair_actor_layer_types ρ S hS hff hsmall)))
end CFSG.Quasithin.ChapterB
