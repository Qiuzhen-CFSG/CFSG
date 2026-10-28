module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Obstruction

/-!
# Exclusion of the exceptional K in the original SL₃ geometry

The original solvable residual L₁ lies in its G₁-conjugate span K. If the
containment were strict, the complete preceding alternatives would force
q=4 and case (1). The conjugation action on U/Z(U), for U=E.W, supplies a
section of GL₈(2); the odd-extension obstruction excludes that same section.
Consequently K=L₁.

The statement is conditional on the marked SL₃ datum, the special-structure
fixed subgroup, centralization and elementary rank conclusions, and the
exact preceding relative-component and triangle conclusions. Their producers
are qt-d-1222-sl3-special-factor, qt-d-1222-natural-relative-components and
qt-d-1222-shadow-component-triangle. The outer source assembly remains with
qt-d-1222-sl3-block-exceptional. No action-kernel or nonsection premise is
retained here, and L₁ is the original solvable residual throughout.

Source: Aschbacher--Smith 11.5.7, refs/quasithin.pdf, printed p.782.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)

include d

/-- The exceptional actor equals the original solvable residual, using its
actual central-quotient action and the complete surviving source alternatives. -/
theorem K_eq_pointResidual
    {κ : GroupClass} (hG₁ : IsSQTK κ E.G₁) (hK : Source.NormalComponentIn E.G₁ E.K)
    (hUT : E.W ≤ (T : Subgroup G))
    (hfixed : E.W ⊓ centralizer (E.L₁ : Set G) = closureCenter E)
    (hz : E.K ≤ centralizer (closureCenter E : Set G))
    [IsElementaryAbelian 2 (CentralQuotient E)]
    (hr : Group.rank (CentralQuotient E) = 4 * E.input.field.degree)
    (h : RefinementAlternative T L E.L₁ E.L₂ E.K E.X 0 E.input.field.degree)
    (htriangle : ¬ FieldFourTriangle T L E.L₁ E.L₂ E.K E.X) : E.K = E.L₁ := by
  by_contra hne
  exact Obstruction.strict_case_one_false E d hG₁ hK hUT hfixed hz hr h htriangle
    (lt_of_le_of_ne (pointResidual_le_K E) (Ne.symm hne))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional
