module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Defs
public import Theory.Representation.BinaryPermutation.FiveConjugation
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups

/-!
# The original marked diagonal action

This is the precise earlier selection input on A/⟨z⟩, where
A=[U,i]⟨z⟩ and K₀=O²(C_{C_G(z)}(i)). A quotient homomorphism with
kernel exactly ⟨z⟩ intertwines the original K₀ action with the deleted
five-point module. Its surjective actor map proves nonsolvability of K₀.

Constructing this marking belongs to the selection producer. The existing
Selection.DiagonalModuleData concerns a subgroup of a separate extension;
it cannot supply these quotient coordinates without an additional actual
identification. No cubic fixed-point or exchanged conclusion is assumed.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ExchangedModel
variable {G : Type*} [Group G]

/-- The earlier selected A₅ action on the literal original layer A/⟨z⟩.
These are coordinate maps and an equivariance equation, not any fixed-point
or exchanged-section conclusion. The selection owner supplies this marking. -/
structure OriginalMovedAction (U : Subgroup G) (z i : G) where
  normalizes : diagonalResidual (centralizer ({z}:Set G)) i ≤
    normalizer (liftBase U z i : Set G)
  quotient : liftBase U z i →* Multiplicative (BinaryPermutation.core (Fin 5))
  surjective : Function.Surjective quotient
  kernel : quotient.ker = (zpowers z).subgroupOf (liftBase U z i)
  actor : diagonalResidual (centralizer ({z}:Set G)) i →* alternatingGroup (Fin 5)
  actor_surjective : Function.Surjective actor
  equivariant : ∀ k : diagonalResidual (centralizer ({z}:Set G)) i,
    ∀ a : liftBase U z i,
      quotient ((liftBase U z i).normalizerMonoidHom ⟨k, normalizes k.property⟩ a) =
        Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5)
          (actor k).val (quotient a).toAdd)

/-- Nonsolvability follows from the actual marked diagonal quotient. -/
theorem OriginalMovedAction.nonsolvable {U : Subgroup G} {z i : G}
    (d : OriginalMovedAction U z i) :
    ¬ Group.IsSolvable (diagonalResidual (centralizer ({z}:Set G)) i) := by
  intro hs
  let _ := hs
  let _ : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5))
    (Group.isSolvable_of_surjective d.actor_surjective)


end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ExchangedModel
