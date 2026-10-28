module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.QuotientConsequences
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.KernelIdentification
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PrimeSL2CoverRigidity
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.OmegaActions

/-!
# The noncentral branch of A.3.6

The actual supercritical action constructs a prime-field SL₂ quotient with
kernel F(L). Its core classification then gives the natural or nilpotent
alternative and every common assertion. The proved prime-field universal
cover theorem discharges the cover-rigidity premise in both steps.

`structure_of_noncentral` proves this branch under the original SQTK,
trivial-two-core and C-component hypotheses. `conclusion_of_noncentral`
applies the existing omega-action strengthening to that result. Both
mod-five congruences and all positive homocyclic exponents are retained.
No center–Frattini equality is added.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.6, printed pp.43–45.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
universe u
variable {G : Type u} [Group G] [Finite G] {L : Subgroup G}

/-- Apply the proved omega-action strengthening to the noncentral branch.
The structural alternatives and all common clauses remain explicit until
the preceding source construction and core-shape arguments are supplied. -/
theorem conclusion_with_omega_actions
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hn : ¬ fittingSubgroup L ≤ center L)
    (hs : A36Natural L ∨ A36Nilpotent L) (hc : A36Common L) :
    A36Conclusion L ∧ CenterFrattiniSource.OmegaActionData L := by
  have h : A36Conclusion L :=
    ⟨hs.elim A36Alternative.natural A36Alternative.nilpotent, hc⟩
  have hw := CenterFrattiniSource.strengthened_omega_actions hG hO hL h
  exact ⟨hw.1, hw.2 (not_quasisimple_of_noncentral_fitting hn)⟩

/-- The full noncentral-Fitting branch of A.3.6, with the actual Fitting
quotient constructed and prime-field cover rigidity discharged. -/
theorem structure_of_noncentral
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hn : ¬ fittingSubgroup L ≤ center L) :
    (A36Natural L ∨ A36Nilpotent L) ∧ A36Common L := by
  have hquot := primeSL2FittingQuotient_of_noncentral
    RankActions.primeSL2CoverRigidity hG hO hL hn
  exact CoreShapes.structure_of_fitting_quotient
    RankActions.primeSL2CoverRigidity hG hO hL hn hquot

/-- The completed noncentral classification and its actual omega actions.
All structural premises of `strengthened_omega_actions` are discharged. -/
theorem conclusion_of_noncentral
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hn : ¬ fittingSubgroup L ≤ center L) :
    A36Conclusion L ∧ CenterFrattiniSource.OmegaActionData L := by
  obtain ⟨hs, hc⟩ := structure_of_noncentral hG hO hL hn
  exact conclusion_with_omega_actions hG hO hL hn hs hc

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
