module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract

/-!
# The group comparisons consumed by the higher-field G₂ sieve

The variable-field rows of B.4.2 require three group nonisomorphisms. All
remaining fixed binary and alternating models have order at most 9999360,
the order of SL₅(2). The last clause identifies the coefficient-field order
when the G₂ row survives. These are group assertions, with no assumed module
marking, irreducibility, or selected classification alternative.

This record publishes the common interface for the group calculation and
the independent B.5 action comparison. It does not prove those calculations.
Source: Aschbacher–Smith, B.4.2 and B.5.1, printed pp.86 and 99, as used
in the paragraph before 13.6.14 and in 13.6.19, pp.929–931.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition
open ChapterB.QuasisimpleSource

/-- Precisely the group comparisons needed by the full B.5 action sieve. -/
structure ModelSeparation (F : BinaryField) : Prop where
  not_linearTwo : ∀ E : BinaryField,
    ¬ Nonempty (Atlas.G2.Model F.Carrier ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier)
  not_linearThree : ∀ E : BinaryField,
    ¬ Nonempty (Atlas.G2.Model F.Carrier ≃* Matrix.SpecialLinearGroup (Fin 3) E.Carrier)
  not_symplecticFour : ∀ E : BinaryField,
    ¬ Nonempty (Atlas.G2.Model F.Carrier ≃* Matrix.symplecticGroup (Fin 2) E.Carrier)
  large_order : 9999360 < Nat.card (Atlas.G2.Model F.Carrier)
  field_order : ∀ E : BinaryField,
    Nonempty (Atlas.G2.Model E.Carrier ≃* Atlas.G2.Model F.Carrier) →
      Nat.card E.Carrier = Nat.card F.Carrier

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition
