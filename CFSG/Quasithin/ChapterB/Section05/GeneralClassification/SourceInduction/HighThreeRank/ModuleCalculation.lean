module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.Applicability
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.Models
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers

/-!
# Offender-module calculation for the high-three-rank branch

`cubicCentralizers_of_earlier_source` completes the module calculation from
the explicit noncentral cover context. Offender generation selects an actual
best offender moving O₃(G). `Applicability` establishes all B.5.1 hypotheses
on its original LA action, including F*(LA) = L and offender generation of LA.
`NaturalReduction` compares the full earlier classification with the lifted
cover and constructs the marked natural six/seven action on the actual moved
space, retaining the five-dimensional six-point augmentation core.

The concrete commutants and offender bounds in `NaturalCentralizers` exclude
the seven-point action and give a two-dimensional cubic moved space. Its
faithful action identifies the original O₃(G) with C₃. The marked component
action and offender generation then establish both ambient centralizers.
The conclusion contains actual multiplicative equivalences for the original
component and three-core. No marked-model witness or centralizer conclusion
remains as a premise, and no global fixed-space splitting is asserted.

Exactly two universal earlier-source inputs remain explicit: the complete
`ProjectiveLine.QuasisimpleClassificationInput` (B.5.1, producer
`qt-b05-quasisimple`) and the complete `EarlierMultiplierInput` (all six rows
of I.1.3, producer `qt-i-01`, including `qt-i01-lie-a2`). The A.3.18,
B.5.2 and B.5.5 cover consequences are already in `NoncentralContext`;
constructing that context remains with `qt-b05-induction-high-three-rank`
and its cover-source producer, using `qt-b05-quotient-components`.
The module extension and offender endgame need no further earlier-source
parameters. Final source assembly must discharge the two universal inputs.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.7, p.106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation
universe u v
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V)

/-- The offender/module portion of B.5.7 on the original component and
three-core. The supplied noncentral cover context and the two complete
universal earlier-source implications suffice; the moving offender and
marked moved-module witness are constructed in the proof. -/
theorem cubicCentralizers_of_earlier_source
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (multipliers : NaturalReduction.ModelComparison.BinaryG2Exclusion.EarlierMultiplierInput K)
    (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (hr : 1 < primeRank 3 L)
    (d : NoncentralContext K G L) : Nonempty (CubicCentralizers G L) := by
  obtain ⟨A, hA, hm, _, _⟩ := exists_moving_offender ρ hyp hL d
  obtain ⟨m⟩ := NaturalReduction.model_of_earlier_source ρ earlier multipliers hyp hL hr d hA hm
  exact NaturalCentralizers.cubicCentralizers_of_moved_model ρ hyp hL d hA hm m

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation
