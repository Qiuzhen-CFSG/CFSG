module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.WholeSmall
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# The four named small chief actors

The binary plane actor is SL₂(2), identified with S₃ by its action on the
three nonzero vectors. Apply this equivalence to each wreath coordinate;
the five-point alternatives already use the source symmetric-group names.
The kernel quotient is identified with the faithful action image through
the literal action homomorphism.

Source: Aschbacher–Smith, original 3.1.9(5) and 15.1.12(3).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB

def ChiefSmallActor (D : Type*) [Group D] : Prop :=
  Nonempty (D ≃* Equiv.Perm (Fin 3)) ∨
    Nonempty (D ≃* RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) ∨
    Nonempty (D ≃* Equiv.Perm (Fin 5)) ∨
    Nonempty (D ≃* RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))

variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]

theorem ChiefSmallWholeAction.actor {ρ : Representation (ZMod 2) D W}
    (h : ChiefSmallWholeAction ρ) : ChiefSmallActor D := by
  unfold ChiefSmallWholeAction at h
  unfold ChiefSmallActor
  let e₃ := (BinaryLinear.OuterCyclic.slEquivLinear 2).trans
    BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree
  rcases h with ⟨h,_⟩ | ⟨e⟩ | ⟨e⟩
  · rcases h with ⟨c,e,he⟩ | ⟨e,c,he⟩
    · exact Or.inl ⟨e.trans e₃⟩
    · exact Or.inr (Or.inl ⟨e.trans (RegularWreathProduct.congr e₃ (MulEquiv.refl _))⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨(Classical.choice e).groupEquiv⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨(Classical.choice e).groupEquiv⟩))

theorem ChiefSmallActor.of_equiv {E : Type*} [Group E]
    (h : ChiefSmallActor D) (e : E ≃* D) : ChiefSmallActor E := by
  unfold ChiefSmallActor at *
  rcases h with ⟨h⟩ | ⟨h⟩ | ⟨h⟩ | ⟨h⟩
  · exact Or.inl ⟨e.trans (Classical.choice h)⟩
  · exact Or.inr (Or.inl ⟨e.trans (Classical.choice h)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans (Classical.choice h)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨e.trans (Classical.choice h)⟩))

theorem ChiefSmallWholeAction.quotient_actor
    {ρ : Representation (ZMod 2) D W}
    (h : ChiefSmallWholeAction (imageRepresentation ρ)) :
    ChiefSmallActor (D ⧸ (actionHom ρ).ker) :=
  h.actor.of_equiv (QuotientGroup.quotientKerEquivOfSurjective
    (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective)

end CFSG.Quasithin.ChapterB
