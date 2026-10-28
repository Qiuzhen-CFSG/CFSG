module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction.CoordinatesContract

/-!
# Separate projections for the ambient parity coordinates

These construction targets retain the whole ambient actions on the original
moved spaces. Their parity fibers mark the same product of the original A₆
and C₃ factors. The coordinate assembly combines the two homomorphisms into
one isomorphism with the literal parity subgroup of S₆ × S₃.

Source: Aschbacher–Smith, B.5.7, printed p.106.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
universe u v
variable {G : Type u} [Group G] [Finite G]
variable (c : ChapterB.OuterSixThreeShape G)
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V)

/-- A six-point projection with its actual ambient intertwiner and parity fiber. -/
structure SixCoordinates where
  projection : G →* Equiv.Perm (Fin 6)
  surjective : Function.Surjective projection
  kernel : projection.ker = c.second
  even : (alternatingGroup (Fin 6)).comap projection = c.first ⊔ c.second
  action :
    (∃ b : (firstMoved c ρ).toSubmodule ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6),
      ∀ (g : G) (w : (firstMoved c ρ).toSubmodule),
        b ((firstMoved c ρ).toRepresentation g w) =
          BinaryPermutation.naturalRepresentation (Fin 6) (projection g) (b w)) ∨
    (∃ b : (firstMoved c ρ).toSubmodule ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6),
      ∀ (g : G) (w : (firstMoved c ρ).toSubmodule),
        b ((firstMoved c ρ).toRepresentation g w) =
          BinaryPermutation.coreRepresentation (Fin 6) (projection g) (b w))

/-- A three-point projection with its actual ambient plane intertwiner and parity fiber. -/
structure CubicCoordinates where
  projection : G →* Equiv.Perm (Fin 3)
  surjective : Function.Surjective projection
  kernel : projection.ker = c.first
  even : (alternatingGroup (Fin 3)).comap projection = c.first ⊔ c.second
  action :
    ∃ b : (secondMoved c ρ).toSubmodule ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 3),
      ∀ (g : G) (w : (secondMoved c ρ).toSubmodule),
        b ((secondMoved c ρ).toRepresentation g w) =
          BinaryPermutation.naturalRepresentation (Fin 3) (projection g) (b w)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
