module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ResidualTerminalReduction
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.KernelIdentity

/-!
# Chosen-action contradiction from the action-kernel residual

The terminal reduction already forces the equality row for any surviving
original residual input.  In that row, containment of the embedded
prime-to-three residual of the literal quotient-action kernel supplies the
one residual identity needed by plane uniqueness and the chosen-action
contradiction.  The whole kernel need not be contained in the residual.

This is the consumer of the missing ambient kernel calculation; its
containment premise and the earlier global wreath quotients remain explicit.
No rank-only order-nine exclusion is used.

Source: Aschbacher--Smith 15.2.12(4), 15.2.15 and 15.2.27--28,
printed pp.1111--1112 and 1119--1120, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section02
open Section01 ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The exact remaining kernel-residual containment for one original input
suffices for the chosen-action contradiction.  The equality row itself is
proved by the existing terminal reduction. -/
theorem source_chosen_contradiction_of_action_kernel_residual
    {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (d : ResidualInput h H B)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* Wreath))
    (hker : ∀ he : partnerSpan H Mc = residual H,
      (primeToResidual 3 (partnerQuotientAction H Mc he).ker).map
        (partnerQuotientAction H Mc he).ker.subtype ≤
          (residual H).subgroupOf Mc) : False := by
  have he : partnerSpan H Mc = residual H :=
    (source_chosen_index_two_equality_row h d hquotient).1
  exact source_chosen_contradiction_of_one_residual_identity h d hquotient
    (d.residual_equality_of_eq_of_action_kernel_residual_le he (hker he))

end CFSG.Quasithin.Chapter15.Section02
