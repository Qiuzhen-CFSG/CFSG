module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction.Recovery
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.ParityModel

/-!
# The full ambient coordinate target

The target uses one actual isomorphism with the parity subgroup of S₆ × S₃,
both literal coordinate projections, and linear intertwiners on the original
moved spaces. Its kernel clauses mark the original A₆ and C₃ factors. The
natural and augmentation-core alternatives retain their actual carriers.
This interface is a construction target, not a hypothesis of B.5.3 or a
claim that the coordinates have been constructed. `recover` supplies
the marked local action and cubic plane needed for that construction.

Odd averaging already proves faithfulness of the original cubic on its
moved plane, as recorded below. Source: Aschbacher–Smith, B.5.7, p.106.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
universe u v
variable {G : Type u} [Group G] [Finite G]
variable (c : ChapterB.OuterSixThreeShape G)
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}

/-- The whole original actor acting on its first factor's moved space. -/
def firstMoved : Subrepresentation ρ :=
  @normalMoved G _ V _ _ ρ c.first (first_normal c)

/-- The whole original actor acting on its cubic factor's moved plane. -/
def secondMoved : Subrepresentation ρ :=
  @normalMoved G _ V _ _ ρ c.second (second_normal c)

/-- The remaining coordinate-construction target. The two literal projections
use one actor equivalence. Its kernels mark the original factors, and each
linear equivalence intertwines the whole ambient action on an original
moved subspace. This definition does not assert existence of the coordinates. -/
structure AmbientCoordinates where
  actorEquiv : G ≃* SixPoint.Actor
  first_kernel : (SixPoint.firstProjection.comp actorEquiv.toMonoidHom).ker = c.second
  second_kernel : (SixPoint.secondProjection.comp actorEquiv.toMonoidHom).ker = c.first
  six_action :
    (∃ b : (firstMoved c ρ).toSubmodule ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6),
      ∀ (g : G) (w : (firstMoved c ρ).toSubmodule),
        b ((firstMoved c ρ).toRepresentation g w) =
          BinaryPermutation.naturalRepresentation (Fin 6)
            (SixPoint.firstProjection (actorEquiv g)) (b w)) ∨
    (∃ b : (firstMoved c ρ).toSubmodule ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6),
      ∀ (g : G) (w : (firstMoved c ρ).toSubmodule),
        b ((firstMoved c ρ).toRepresentation g w) =
          BinaryPermutation.coreRepresentation (Fin 6)
            (SixPoint.firstProjection (actorEquiv g)) (b w))
  cubic_action :
    ∃ b : (secondMoved c ρ).toSubmodule ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 3),
      ∀ (g : G) (w : (secondMoved c ρ).toSubmodule),
        b ((secondMoved c ρ).toRepresentation g w) =
          BinaryPermutation.naturalRepresentation (Fin 3)
            (SixPoint.secondProjection (actorEquiv g)) (b w)

/-- Faithfulness on the literal cubic moved space follows by odd averaging. -/
theorem second_moved_faithful (hyp : FFHypothesis K ρ) :
    Function.Injective ((secondMoved c ρ).toRepresentation.comp c.second.subtype) := by
  let : c.second.Normal := second_normal c
  exact odd_moved_faithful ρ hyp.faithful c.second (by rw [second_card c]; decide)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
