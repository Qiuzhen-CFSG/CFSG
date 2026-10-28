module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.SixInspection.Quotient
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.Models

/-!
# The symmetric-six quotient and the original alternating-four actor

The A₆ alternative left by the binary model reduction gives both of the
identifications in the n = 1 paragraph of 15.3.43. The four-group geometry
proves these from the retained configuration itself, so either prescribed
action of the source involution is allowed. The parent retains the final
contradiction with the exclusion of A₄.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
1.1.5(3)(a),(c), printed pp.501--502, and 15.3.43, printed p.1140.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.SixInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- Both identifications required for the remaining binary A₆ branch.
The final `not_alternating_four` obstruction is not used to construct them. -/
theorem identifications (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} (_hz : SourceInvolution S M z)
    (h6 : Nonempty (L ≃* alternatingGroup (Fin 6)))
    (_ha : ActsInner L z ∨ ActsTransposition L z) :
    Nonempty (c.toComponentAction.Quotient ≃* Equiv.Perm (Fin 6)) ∧
      Nonempty (Yplus ≃* alternatingGroup (Fin 4)) :=
  ⟨quotient_symmetric_six c h6, actor_alternating_four c h6⟩

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.SixInspection
