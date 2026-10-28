module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.RelatorLifts.Conjugates
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.SchreierCertificate
import Mathlib.Tactic.FinCases

/-!
# The marked M₁ words in the source Schreier interpretation

Schreier symbols 1, 2, 3 are exactly the marked generators
`x`, `x^(y²)`, `x^(y⁻²)` of John Bray's `HeG1-P1.M`. Expanding these three
literal words identifies their values in the original abstract presentation.
Induction then identifies the evaluations of every signed marked word,
preserving the source multiplication order.

This bridge allows a consequence of the checked initial Schreier equations
to be applied to a frozen M₁ relator. It does not assert that the remaining
M₁ relators follow from those equations. No coset cover or faithfulness
statement is used.

Sources: `Held/Model/Source/HeG1-P1.M`, `M1Cosets/SchreierCertificate.lean`,
and `M1Restriction/source/README.md`.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
open Subgroup.CosetWordCertificate
open M1Cosets

/-- The protected Schreier symbols have the original, unchanged M₁ marking. -/
theorem schreierSymbol_eq_liftedGenerator (i : Fin 3) :
    Schreier.symbol (i.val + 1) = liftedGenerator i := by
  fin_cases i <;>
    simp [Schreier.symbol, Schreier.symbolWord, subgroupWord, liftedGenerator,
      eval_cons, x, y, pow_two, mul_inv_rev, mul_assoc]

/-- Passing from zero-based marked letters to one-based Schreier letters
preserves their group value, including signs and multiplication order. -/
theorem schreierEval_eq_liftedEval (w : Word (Fin 3)) :
    Theory.GroupTheory.CosetEnumeration.eval Schreier.symbol
      (w.map (fun a => (a.1.val + 1, a.2))) = eval liftedGenerator w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, Theory.GroupTheory.CosetEnumeration.eval,
      List.prod_cons, Theory.GroupTheory.CosetEnumeration.letterValue,
      schreierSymbol_eq_liftedGenerator, eval_cons] at *
    rw [ih]

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
