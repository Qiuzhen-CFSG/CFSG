module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.GroupCore
public import Theory.SpecificGroups.FFLinearPrimeCore

/-!
# Core elimination for every nonquasisimple FF alternative

The actual matrix and permutation models of each direct factor have trivial
three-prime core. Their internal product equivalences transfer the product
calculation to the original actor. This applies equally to the natural,
double-natural and indecomposable summands, and to the nonsplit hyperplane
case. Together with the S₃ and outer A₆–C₃ calculations, it handles all of
B.5.6(2)–(5), using only the source's generation and two-core hypotheses.

No universal classification implication is asserted here.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.6, p.105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {D : Type*} [Group D]

/-- All three families of direct factors have trivial three-prime core. -/
theorem FactorModel.threePrimeCore_eq_bot (h : FactorModel D) : pPrimeCore 3 D = ⊥ := by
  cases h with
  | linearTwo F e =>
    exact pPrimeCore_eq_bot_of_equiv e (Theory.SpecificGroups.sl_two_threePrimeCore F.Carrier)
  | symmetricFive e =>
    exact pPrimeCore_eq_bot_of_equiv e Theory.SpecificGroups.symmetricFive_threePrimeCore
  | linearThree F _ e =>
    exact pPrimeCore_eq_bot_of_equiv e (Theory.SpecificGroups.sl_three_threePrimeCore F.Carrier)

variable [Finite D] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- The two-factor case, including all its module extensions. -/
theorem TwoFactorCase.threePrimeCore_eq_bot (c : TwoFactorCase ρ) : pPrimeCore 3 D = ⊥ :=
  pPrimeCore_eq_bot_of_equiv c.product.equiv.symm
    (pPrimeCore_prod_eq_bot c.firstModel.threePrimeCore_eq_bot c.secondModel.threePrimeCore_eq_bot)

/-- The hyperplane case does not require a splitting of the whole module. -/
theorem HyperplaneCase.threePrimeCore_eq_bot (c : HyperplaneCase ρ) : pPrimeCore 3 D = ⊥ :=
  pPrimeCore_eq_bot_of_equiv c.product.equiv.symm
    (pPrimeCore_prod_eq_bot
      (pPrimeCore_eq_bot_of_equiv c.firstEquiv
        (Theory.SpecificGroups.sl_three_threePrimeCore (ZMod 2)))
      (c.secondCase.factorModel ρ).threePrimeCore_eq_bot)

/-- All four nonquasisimple alternatives eliminate the core from the
actual actor, with no core equality included in the classification data. -/
theorem NonQuasisimpleAlternative.threePrimeCore_eq_bot
    (c : NonQuasisimpleAlternative ρ)
    (hg : offenderSubgroup ρ = ⊤) (h₂ : pCore 2 D = ⊥) : pPrimeCore 3 D = ⊥ := by
  cases c with
  | symmetricThree c => exact c.threePrimeCore_eq_bot ρ
  | twoFactors c => exact c.threePrimeCore_eq_bot ρ
  | outerSixThree c => exact c.threePrimeCore_eq_bot ρ hg h₂
  | hyperplane c => exact c.threePrimeCore_eq_bot ρ

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
