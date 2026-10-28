module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Models.Reduction

/-!
# Assembly of the residual structural alternatives

The reduction proves every non-Held branch with the literal subgroups and
quotient isomorphisms. The theorem here records its actual source consumer:
an ambient exclusion of the retained Held case completes 15.2.12(2).
That exclusion remains an explicit obligation; this module does not assert
the unconditional source theorem.

Source: Aschbacher--Smith 15.2.12(2), printed p.1111.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

/-- The exact source structural list, conditional only on exclusion of the
explicit actual Held branch of the completed reduction. -/
theorem ResidualInput.structural_of_held_exclusion {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (hHe : ¬ HeldResidualCase T H Mc) :
    StructuralAlternatives T H Mc :=
  d.structural_or_held.resolve_right hHe

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
