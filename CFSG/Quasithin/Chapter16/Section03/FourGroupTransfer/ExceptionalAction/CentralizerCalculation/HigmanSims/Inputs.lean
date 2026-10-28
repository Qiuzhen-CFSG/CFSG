module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# The two intrinsic HS component-fixer obligations

The subgroup is the actual component of an involution fixed subgroup in the
fixed degree-100 HS carrier. Its full pointwise fixer in Aut(HS) must have
order at most four and exponent dividing two. The two cases are A₆ and A₈.
Simplicity and perfectness are inherited from the source component quotient;
no new order or simplicity certification is requested here.

These definitions are outstanding obligations. Centralizer shapes or abstract
component isomorphism types alone do not prove the fixer calculations. The
cover projection and final conditional assembly are in the sibling modules.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(10), 16.1.7(3h), and 16.3.5, printed pp.1172–1173 and 1178–1179.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.HigmanSims
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.HS

/-- The intrinsic upper bound, retaining the actual component embedding. -/
def ComponentFixerBound (n : ℕ) : Prop :=
  ∀ [IsSimpleGroup Carrier] [Group.IsPerfect Carrier]
    (r : MulAut Carrier) (K : Subgroup Carrier),
    orderOf r = 2 → IsComponentIn K r.fixedSubgroup →
    Nonempty (K ≃* alternatingGroup (Fin n)) →
    Nat.card (fixingSubgroup (MulAut Carrier) (K : Set Carrier)) ≤ 4 ∧
      ∀ a : fixingSubgroup (MulAut Carrier) (K : Set Carrier), a ^ 2 = 1

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.HigmanSims
