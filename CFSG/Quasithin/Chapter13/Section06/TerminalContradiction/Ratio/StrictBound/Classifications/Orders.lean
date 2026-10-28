module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications.Alternatives
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.Mathieu.M23.Properties.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order

/-!
# Orders of the actual terminal component carriers

These orders come from the existing projective matrix and permutation
carriers. The Hall–Janko order is the checked normal-form enumeration of
the ATLAS permutation carrier, not an assumed comparison with an icosian
model. They are used only to compare the B.4 actors.

Source application: Aschbacher–Smith, terminal §13.6, printed p.935.
The imported J₂ development records attribution for the ATLAS data.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications

/-- The three exact terminal orders, transported from the actual model markings. -/
theorem exceptional_card {L : Type*} [Group L] (h : ExceptionalModel L) :
    Nat.card L = 20160 ∨ Nat.card L = 10200960 ∨ Nat.card L = 604800 := by
  rcases h with h | h | h
  all_goals obtain ⟨e⟩ := h
  · exact .inl ((Nat.card_congr e.toEquiv).trans Matrix.PSL3Four.card_PSL)
  · exact .inr (.inl ((Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m23_order))
  · exact .inr (.inr ((Nat.card_congr e.toEquiv).trans
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier))

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications
