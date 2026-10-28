module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalPresentation
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.Contracts
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.WordCalculus
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.CyclicReplay
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates

/-!
# The three mixed local relations from a checked cyclic-factor trace

The replay calculus uses the six original ATLAS relations and the literal
max3 words. A finite trace whose three outputs are the specified root loops
therefore discharges exactly local indices 3, 5 and 6.

This module applies the complete concrete certificate to obtain the three
identities in the original presentation. The derivation does not require the
two remaining local power identities. The power-to-mixed interface is retained
for the parent assembly, which must still discharge its power contract before
asserting all seven local relations.

Source: ATLAS G23G1-P1 and G23G1-max3W1, as fixed in `Subgroup`, and the
literal lists in `LocalPresentation`.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations
open Subgroup.CosetWordCertificate
open MixedRelations.CyclicReplay

/-- A checked source derivation supplies all three fixed mixed words. -/
theorem remaining_mixed_relations_of_checked_trace
    (D : Definitions Bool) (facts : ℕ → Fact) (ops : ℕ → Instruction) (N : ℕ)
    (checked : ∀ n, n < N → check D.parent D.letter facts n (ops n) (facts n) = true)
    (outputs : Fin 3 → ℕ) (hbound : ∀ j, outputs j < N)
    (hwords : ∀ j, facts (outputs j) =
      ⟨0, reduce (Replay.expand boundLetters (localRelatorLetters (![3, 5, 6] j))), 0, 0⟩) :
    RemainingMixedRelations := by
  refine ⟨?_, ?_, ?_⟩
  · exact local_relation_of_checked_trace D facts ops N checked 3 (outputs 0)
      (hbound 0) (hwords 0)
  · exact local_relation_of_checked_trace D facts ops N checked 5 (outputs 1)
      (hbound 1) (hwords 1)
  · exact local_relation_of_checked_trace D facts ops N checked 6 (outputs 2)
      (hbound 2) (hwords 2)

/-- The three literal mixed words hold in the original six-relator group.
Every concrete trace instruction and its exact output word is kernel-checked. -/
theorem remaining_mixed_relations : RemainingMixedRelations :=
  remaining_mixed_relations_of_checked_trace
    MixedRelations.Certificates.traceDefinitions
    MixedRelations.Certificates.traceFacts
    MixedRelations.Certificates.traceInstructions
    MixedRelations.Certificates.traceLength
    MixedRelations.Certificates.traceChecked
    MixedRelations.Certificates.traceOutputs
    MixedRelations.Certificates.traceOutput_lt
    MixedRelations.Certificates.traceOutput_words

set_option linter.unusedVariables false in
/-- The requested power-to-mixed contract. The source derivation already proves
the mixed identities without using the two additional power identities. -/
theorem remaining_mixed_relations_of_power (hp : RemainingPowerRelations) :
    RemainingMixedRelations :=
  remaining_mixed_relations

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations
