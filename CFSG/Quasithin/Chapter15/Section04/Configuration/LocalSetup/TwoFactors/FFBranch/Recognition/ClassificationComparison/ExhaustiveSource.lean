module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate
/-!+# Source inputs for the exhaustive mixed FF comparison

This combines the corrected projective-line convention in B.4.2/K.1.3 with
the adequate outer A₆–C₃ alternative. All six B.5.1 clauses and every other
B.5.6 module clause are retained. The outer case needs only its actual
group configuration: `OuterGroupComparison` excludes it without invoking
the disputed fixed-space splitting. The old full interfaces are preserved.

The universal implications remain explicit inputs for the chosen source
class K. The three-prime-core conclusion is proved from their actual group
and action alternatives; it is not part of the classification premise.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.1/B.5.3/B.5.6, pp.99–110; K.1.3, p.453; 15.4.18, p.1163.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- Both source corrections on the same original actor and representation. -/
inductive AdequateSourceAlternative : Prop
  | trivial (actor : Subsingleton D)
  | quasisimple (quasisimple : IsQuasisimple (generalizedFitting D))
      (actions : QuasisimpleSourceConclusion ρ (generalizedFitting D))
  | symmetricThree (case : SymmetricThreeCase ρ)
  | twoFactors (case : SourceTwoFactorCase ρ)
  | outerSixThree (shape : ChapterB.OuterSixThreeShape D)
  | hyperplane (case : HyperplaneCase ρ)

/-- Forget only the outer representation claim from the full corrected input. -/
theorem SourceAlternative.toAdequate (h : SourceAlternative ρ) :
    AdequateSourceAlternative ρ := by
  cases h with
  | trivial h => exact .trivial h
  | quasisimple hq ha => exact .quasisimple hq ha
  | symmetricThree h => exact .symmetricThree h
  | twoFactors h => exact .twoFactors h
  | outerSixThree h => exact .outerSixThree h.toGroupShape
  | hyperplane h => exact .hyperplane h

/-- Universal adequate B.5.6, with all the genuine B.5.3 hypotheses. -/
def AdequateGeneralClassificationInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V),
    FFHypothesis K ρ → AdequateSourceAlternative ρ

/-- The corrected full B.5.1 implication and adequate general implication. -/
structure AdequateCompleteClassificationInput (K : GroupClass.{u}) : Prop where
  quasisimple : QuasisimpleClassificationInput.{u,v} K
  general : AdequateGeneralClassificationInput.{u,v} K

/-- The stronger corrected full input remains a supported conditional API. -/
theorem CompleteClassificationInput.toAdequate {K : GroupClass.{u}}
    (h : CompleteClassificationInput.{u,v} K) :
    AdequateCompleteClassificationInput.{u,v} K where
  quasisimple := h.quasisimple
  general := fun D _ _ V _ _ ρ hyp => (h.general D V ρ hyp).toAdequate ρ

/-- Core elimination from actual alternatives, including the group-only outer
case. No offending projective line or fixed-space splitting is used here. -/
theorem AdequateSourceAlternative.threePrimeCore_eq_bot [Finite D]
    {K : GroupClass.{u}} (h : AdequateSourceAlternative ρ)
    (hyp : FFHypothesis K ρ) (hff : IsFFModule ρ) : pPrimeCore 3 D = ⊥ := by
  cases h with
  | trivial ht =>
    let : Subsingleton D := ht
    let : Nontrivial D := nontrivial_of_ff ρ hff
    obtain ⟨g, hg⟩ := exists_ne (1 : D)
    exact (hg (Subsingleton.elim _ _)).elim
  | quasisimple _ c =>
    exact threePrimeCore_eq_bot_of_quasisimple_alternative (c.fittingModel ρ)
      (fun _ => Theory.SpecificGroups.g2_derived_two_center_isThreeGroup)
  | symmetricThree c => exact c.threePrimeCore_eq_bot ρ
  | twoFactors c => exact c.toBasic ρ |>.threePrimeCore_eq_bot ρ
  | outerSixThree c =>
    exact outerSixThreeShape_threePrimeCore_eq_bot c ρ hyp.generated hyp.twoCore
  | hyperplane c => exact c.threePrimeCore_eq_bot ρ

/-- Apply core elimination to the classifier of the same chosen source class. -/
theorem AdequateCompleteClassificationInput.threePrimeCore_eq_bot [Finite D]
    {K : GroupClass.{u}} (h : AdequateCompleteClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (hff : IsFFModule ρ) : pPrimeCore 3 D = ⊥ :=
  (h.general D V ρ hyp).threePrimeCore_eq_bot ρ hyp hff

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine
