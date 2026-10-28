module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.WholeActor
public import Theory.SpecificGroups.OrthogonalFourBinary.WreathAction
-- Internal continuation: eliminate the frozen whole-action witness without widening its public body.
import all CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.WholeActor

/-!
# Converting the whole natural small actor to its wreath convention

The whole moved-action witness uses the original SL₂(2) or O₄⁺(2) action.
The concrete isometry/wreath equivalence preserves all original vector and
actor coordinates, giving the source's S₃≀C₂ convention.

Source: Aschbacher–Smith 13.2.8(3), printed p.880.
-/
@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The source small actor alternative, preserving its actual natural group action. -/
def SmallNaturalWreathAction (ρ : Representation (ZMod 2) G V) : Prop :=
  (∃ (c : subspaceCommutator ρ ⊤ (offenderSubgroup ρ) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
      (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      ∀ g v, c ((SolvableFFFactors.naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g v) =
        (e g).val.mulVec (c v)) ∨
  (∃ (e : G ≃* RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2)))
      (c : Multiplicative (subspaceCommutator ρ ⊤ (offenderSubgroup ρ)) ≃*
        (Multiplicative (ZMod 2) → Multiplicative (Fin 2 → ZMod 2))),
      ∀ g v i, c (Multiplicative.ofAdd
          ((SolvableFFFactors.naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g v.toAdd)) i =
        Multiplicative.ofAdd (Matrix.mulVec ((e g).left i).1
          (Multiplicative.toAdd (c v ((e g).right⁻¹*i)))))

/-- Convert the whole actual orthogonal action to the printed wreath convention. -/
theorem SmallNaturalMovedAction.wreath {ρ : Representation (ZMod 2) G V}
    (h : SmallNaturalMovedAction ρ) : SmallNaturalWreathAction ρ := by
  unfold SmallNaturalMovedAction at h
  rcases h with h | ⟨c,e,he⟩
  · exact Or.inl h
  obtain ⟨eG,eV,hev⟩ := OrthogonalFourBinary.isometry_equiv_natural_wreath
  refine Or.inr ⟨e.trans eG,c.toAddEquiv.toMultiplicative.trans eV,?_⟩
  intro g v i
  change eV (Multiplicative.ofAdd (c
      ((SolvableFFFactors.naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g v.toAdd))) i = _
  exact (congrArg (fun w => eV (Multiplicative.ofAdd w) i) (he g v.toAdd)).trans
    (hev (e g) (Multiplicative.ofAdd (c v.toAdd)) i)
end CFSG.Quasithin.ChapterB

