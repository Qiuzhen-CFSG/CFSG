module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.InnerExclusions
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.Statements

/-!
# Intrinsic sporadic residual-fixer obligations

These predicates specify the remaining calculations in the actual models;
they do not assert them. The subgroup being fixed is the embedded two-residual
of the given automorphism's fixed subgroup. Abstract centralizer isomorphisms
alone do not determine this pointwise fixer.

The M₂₂ hypothesis excludes exactly the Sz(2)/E₁₆ outer row of 16.4.7.
The M₁₂ calculation is shared with the A₅-fixer calculation used in 16.3.5;
its lower bound will be established inside the actual H* by this owner.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5, 16.4.7 and proof of 16.4.9(1), printed pp.1171–1172, 1186 and 1189.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.Sporadic
open Subgroup OtherPreliminaries.Mathieu

/-- The exact earlier M₂₂ row excluded by 16.4.7, with its genuine quotient. -/
def M22ExcludedRow (a : MulAut Sporadic.Mathieu.M22) : Prop :=
  Nonempty (GroupExtension (Elementary 4) a.fixedSubgroup SzTwo)

/-- The sufficient intrinsic calculation for J₂ and HS. Simplicity and perfectness
are inherited from the actual component quotient by the consumer. -/
def OuterResidualFixerBound (S : Type*) [Group S] : Prop :=
  ∀ (_ : IsSimpleGroup S) (_ : Group.IsPerfect S), ∀ a : MulAut S, orderOf a = 2 → (¬ ∃ s : S, a = MulAut.conj s) →
    ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut S)
      (LiePreliminaries.fixedTwoResidual S a : Set S))

/-- The M₂₂ calculation retains the precise earlier outer-class exclusion. -/
def M22FixerCalculation : Prop :=
  ∀ a : MulAut Sporadic.Mathieu.M22,
    orderOf a = 2 → (¬ ∃ s, a = MulAut.conj s) → ¬ M22ExcludedRow a →
    ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut Sporadic.Mathieu.M22)
      (LiePreliminaries.fixedTwoResidual Sporadic.Mathieu.M22 a : Set Sporadic.Mathieu.M22))

/-- The full A₅ fixer calculation shared with the 16.3.5 owner. -/
def M12FixerCalculation : Prop :=
  ∀ P : Subgroup Sporadic.Mathieu.M12, Nonempty (P ≃* A5) →
    4 ≤ Nat.card (fixingSubgroup (MulAut Sporadic.Mathieu.M12) (P : Set Sporadic.Mathieu.M12)) →
    Nat.card (fixingSubgroup (MulAut Sporadic.Mathieu.M12) (P : Set Sporadic.Mathieu.M12)) ≤ 4 ∧
      ∀ a : fixingSubgroup (MulAut Sporadic.Mathieu.M12) (P : Set Sporadic.Mathieu.M12),
        a ^ 2 = 1

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.Sporadic
