module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Assembly

/-!+# Applying the five local comparisons to the preliminary alternatives

The complete B.5.1 implication on the literal quotient LA/C_LA(U), followed
by the proved comparison of all its source rows, supplies `LocalAlternative`.
The preliminary assembly then transports the actions to the chosen moved
section, proves the non-IV supplements and offender placement, and retains
the natural SL₃ seed in case (IV).

`preliminary_of_prepared_source_classification` discharges the local-action
argument of `preliminary_of_local_alternative`. Its explicit `Prepared`
argument belongs to the independent seed-preparation producer
`qt-b05-preliminary-seed-preparation`. That preparation uses the source
assumption that A centralizes F(G); the comparison needs no further use of it.
Final preparation and natural-seed enlargement belong to
`qt-b05-component-preliminary-actions`.

Earlier-source inventory: the complete projective-line-correct B.5.1 input
is owned by `qt-b05-quasisimple`, and contains the full B.4.2 alternatives
(original owner `qt-b-04`). The complete B.4.8(2) input is owned by
`qt-b-04-natural-extensions` / `qt-b-04`; its faithful, indecomposable,
four-dimensional hypotheses are proved before it is applied. The comparison
uses checked natural-module cohomology for the needed I.1.6 calculation
(original owner `qt-i-01`). No additional I.1.6 or A.1.31 implication
(original owner `qt-a-01`) is assumed here. Final discharge of the two
explicit earlier implications remains with `qt-b05-general-classification`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed pp.107–108, through the non-IV projection arguments. The final
case-(IV) enlargement from U to W is a separate source step.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Apply the exhaustive local comparison to the actual preliminary consumer.
The all-components rank hypothesis is specialized to the chosen component;
every local-action premise is discharged on its prepared faithful quotient. -/
theorem preliminary_of_prepared_source_classification
    (h48 : ThreeCovers.CentralExtension.EarlierB48Two.{u,v})
    {K : GroupClass.{u}}
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (h3 : ∀ M, IsComponent G M → primeRank 3 M = 1)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (s : MovedSection ρ L) (p : Prepared ρ K hLA) :
    PreliminaryConclusion ρ A L s :=
  preliminary_of_local_alternative ρ hyp hA hL hLA s p
    (localAlternative_of_source_classification ρ h48 earlier hyp hA hL hLA p (h3 L hL))

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
