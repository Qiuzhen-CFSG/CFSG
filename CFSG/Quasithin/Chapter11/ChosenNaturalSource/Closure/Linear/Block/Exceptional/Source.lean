module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.PointKernel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Transfer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Sieve
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Section

/-!
# The original exceptional actor reduced to its odd-extension order obstruction

The special-structure conclusions yield both action-kernel bounds, with no
kernel hypothesis. Under L₁<K the complete preceding source alternatives
force q=4 and case (1); rank 4n becomes eight. The actual conjugation action
then realizes K/O₂,Z(K) as a section of GL₈(2), and its order divides
the binary linear group order.

This is the input to the remaining odd-extension nonsection argument,
not yet the equality K=L₁. The special-structure producer is
qt-d-1222-sl3-special-factor. The full 11.1.2 and 11.4.1(2) producers are
qt-d-1222-natural-relative-components and qt-d-1222-shadow-component-triangle;
the outer assembly discharges those explicitly retained earlier conclusions.
The original solvable residual and original K are used throughout.
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

/-- Both kernel bounds on the original K, discharged by the special fixed
subgroup and center-centralization conclusions. -/
theorem action_kernel_bounds
    (hUT : E.W ≤ (T : Subgroup G))
    (hfixed : E.W ⊓ centralizer (E.L₁ : Set G) = closureCenter E)
    (hz : E.K ≤ centralizer (closureCenter E : Set G)) :
    (pointAction E).ker ≤ centralPreimage (pCore 2 E.K) ∧
      (centralAction E).ker ≤ centralPreimage (pCore 2 E.K) := by
  have hp := pointAction_kernel_le_of_special_fixed E d hfixed
  exact ⟨hp,centralAction_kernel_le_of_pointAction_kernel_le E hUT hz hp⟩

/-- The concrete original-action input to the remaining section obstruction.
No kernel bound or nonsection statement is among the premises. -/
theorem strict_case_one_action_order
    (hUT : E.W ≤ (T : Subgroup G))
    (hfixed : E.W ⊓ centralizer (E.L₁ : Set G) = closureCenter E)
    (hz : E.K ≤ centralizer (closureCenter E : Set G))
    [IsElementaryAbelian 2 (CentralQuotient E)]
    (hr : Group.rank (CentralQuotient E) = 4 * E.input.field.degree)
    (h : RefinementAlternative T L E.L₁ E.L₂ E.K E.X 0 E.input.field.degree)
    (htriangle : ¬ FieldFourTriangle T L E.L₁ E.L₂ E.K E.X)
    (hlt : E.L₁ < E.K) :
    E.input.field.degree = 2 ∧ Nat.card E.input.field.Carrier = 4 ∧
      Group.rank (CentralQuotient E) = 8 ∧
      (∃ p : ℕ, (p = 5 ∨ (p.Prime ∧ 11 ≤ p)) ∧
        Source.IsSL (Source.TwoOddQuotient E.K) 2 p) ∧
      Nat.card (coreCentralQuotient E.K) ∣
        Nat.card (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) := by
  obtain ⟨hn,hq,hcase⟩ := case_one_of_strict E d h htriangle hlt
  have hr8 := rank_eight_of_strict E h hlt hr
  refine ⟨hn,hq,hr8,hcase,?_⟩
  exact coreCentral_card_dvd_binary_eight_of_kernel_le E
    (centralQuotient_card_le_of_rank_eight E hr8)
    (action_kernel_bounds E d hUT hfixed hz).2

/-- The actual section required by the source nonsection contradiction;
both action-kernel bounds have been discharged. -/
theorem strict_coreCentral_isSectionOf_binary_eight
    (hUT : E.W ≤ (T : Subgroup G))
    (hfixed : E.W ⊓ centralizer (E.L₁ : Set G) = closureCenter E)
    (hz : E.K ≤ centralizer (closureCenter E : Set G))
    [IsElementaryAbelian 2 (CentralQuotient E)]
    (hr : Group.rank (CentralQuotient E) = 4 * E.input.field.degree)
    (h : RefinementAlternative T L E.L₁ E.L₂ E.K E.X 0 E.input.field.degree)
    (hlt : E.L₁ < E.K) :
    CFSG.Quasithin.ChapterA.Section02.IsSectionOf (coreCentralQuotient E.K)
      (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) := by
  exact coreCentral_isSectionOf_binary_eight_of_kernel_le E
    (centralQuotient_card_le_of_rank_eight E (rank_eight_of_strict E h hlt hr))
    (action_kernel_bounds E d hUT hfixed hz).2

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional
