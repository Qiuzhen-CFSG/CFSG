module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SourceCases
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct.Rank
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.ClassifiedComponents
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.MixedShape
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ExhaustiveSource

/-!
# Component existence for a contained best offender

Exhaustive B.5.6 case analysis constructs one outside component of the
conjugate span of the selected contained best offender. The quasisimple
generalized Fitting case includes proper outer extensions. The product
and hyperplane cases use their canonical residual components and proved
cubic witnesses. The pure S₃, two-S₃, and mixed A₆–cubic cases contradict
the actual placed actor's local hypotheses.

The universal classification implication remains an explicit input for κ,
with the genuine B.5.3 hypotheses established by `starHypothesis`. The
adequate contract retains all six corrected B.5.1 clauses and all other
module alternatives, but uses only the group configuration in the disputed
outer fixed-space case. The full corrected contract is also supported.
Neither input assumes a component-extraction dichotomy or any local
placement conclusion. All cubic, orbit, lift and commutator premises are
discharged here. Construction of PlacedInput and the later extraspecial
contradiction remain with the parent; no assertion that J is its component
product is made.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed pp.99–103; B.5.3–6, pp.104–105; 15.3.49(i), pp.1143–1144.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence
open ComponentReduction
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : PlacedInput κ H M Y V Y0 T ZS Z E)

/-- Exhaust the actual source alternatives on the literal star action.
Every branch either constructs the required component or contradicts the
placed actor's hypotheses. -/
theorem exists_of_source_alternative
    (h : ProjectiveLine.AdequateSourceAlternative (starAction d)) :
    ∃ L : Subgroup G, OutsideComponent H M Y0 d.selected.carrier L := by
  cases h with
  | trivial ht =>
    let := ht
    let := nontrivial_of_ff (starAction d) (starFFWitness d)
    obtain ⟨x, hx⟩ := exists_ne (1 : starImage H (localSpan d.selected.carrier H))
    exact (hx (Subsingleton.elim _ _)).elim
  | quasisimple hq c =>
    exact exists_of_generalizedFitting_model d hq (c.fittingModel (starAction d))
  | symmetricThree c => exact (not_symmetricThreeCase d c).elim
  | twoFactors c => exact exists_of_twoFactorCase d (c.toBasic (starAction d))
  | outerSixThree c => exact (not_outerSixThreeShape d c).elim
  | hyperplane c => exact exists_of_hyperplaneCase d c

/-- Conditional component existence from the universal, source-correct
B.5.6 implication for κ. Its genuine hypotheses, exact model witnesses,
relative component membership, ambient orbit bound, outside placement and
Y₀-commutator identity are all discharged for the selected actor. -/
theorem exists_of_classification
    (source : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} κ) :
    ∃ L : Subgroup G, OutsideComponent H M Y0 d.selected.carrier L :=
  exists_of_source_alternative d (source _ _ (starAction d) (starHypothesis d))

/-- The full corrected B.5.6 implication also supplies the component.
Its additional outer module clauses are unnecessary for this conclusion. -/
theorem exists_of_full_classification
    (source : ProjectiveLine.GeneralClassificationInput.{u,u} κ) :
    ∃ L : Subgroup G, OutsideComponent H M Y0 d.selected.carrier L :=
  exists_of_source_alternative d
    ((source _ _ (starAction d) (starHypothesis d)).toAdequate (starAction d))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence
