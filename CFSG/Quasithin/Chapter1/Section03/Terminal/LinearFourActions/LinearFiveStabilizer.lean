module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.LinearFiveStabilizer.Transport
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.LinearFiveStabilizer.Recognition
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.QuotientTransport
public import Theory.SpecificGroups.BinaryLinear.FiveParabolicStabilizer

/-!
# The L₅(2) stabilizer step for the terminal L₄(2) section

An actual point or hyperplane stabilizer in GL₅(2) has inner stabilizer
action, even before quotienting by its two-core. Transport through the
chosen classical model therefore gives the required inner action on
A/O₂(A). The source residual and quotient hypotheses are transported
along this same isomorphism.

Recognition of the embedded residual as an end-node parabolic discharges
the geometric premise in the final theorem. Thus the A.3.12(5) hypotheses
alone give the required stabilizer action, without an additional local-family
or geometric assumption.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.12(5),
printed pp.47–48, and the proof of 1.3.9, printed p.514.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.LinearFiveStabilizer
open BinaryLinear.OuterCyclic BinaryLinear.FiveParabolicStabilizer

/-- A geometric identification of the actual subgroup supplies its inner action. -/
theorem twoStabilizerActsInner_of_endParabolic {Q : Type*} [Group Q]
    {A : Subgroup Q} (e : Q ≃* LinearGroup 5)
    (hA : IsEndParabolic (A.map e.toMonoidHom)) : TwoStabilizerActsInner A := by
  have hinner : A.HasInnerStabilizerAction :=
    Subgroup.HasInnerStabilizerAction.of_map e hA.hasInnerStabilizerAction
  intro α _ hα
  obtain ⟨a, ha, hact⟩ := hinner α hα
  refine ⟨a, ha, fun x hx => ?_⟩
  rw [hact x hx]
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, mul_inv_cancel]
    using (A.pCoreIn 2).one_mem

/-- Conditional assembly retaining the embedded solvable residual from A.3.12(5).
The theorem below discharges its geometric recognition premise. -/
theorem twoStabilizerActsInner_of_recognition
    (hrecognition : ∀ A P : Subgroup (LinearGroup 5),
      Section02.LieParabolicTwo P → (solvableResidual P).map P.subtype = A →
      ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 4 2 → IsEndParabolic A)
    {Q : Type*} [Group Q] [Finite Q] (hQ : ClassicalGroup.IsPSL Q 5 2)
    {A : Subgroup Q} (hA : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 4 2)
    (hres : Section02.IsParabolicResidual A ⊤ false) : TwoStabilizerActsInner A := by
  obtain ⟨hsmall, P, hP, he⟩ := linear_model_residual hQ hA hres
  exact twoStabilizerActsInner_of_endParabolic (binaryFiveEquiv hQ)
    (hrecognition _ P hP he hsmall)

/-- In the A.3.12(5) embedding in L₅(2), every ambient automorphism of
two-power order preserving the residual A acts inner on A/O₂(A).
The residual is recognized with its actual embedding, including its two-core. -/
theorem twoStabilizerActsInner
    {Q : Type*} [Group Q] [Finite Q] (hQ : ClassicalGroup.IsPSL Q 5 2)
    {A : Subgroup Q} (hA : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 4 2)
    (hres : Section02.IsParabolicResidual A ⊤ false) : TwoStabilizerActsInner A :=
  twoStabilizerActsInner_of_recognition endParabolic_of_residual_quotient hQ hA hres

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.LinearFiveStabilizer
