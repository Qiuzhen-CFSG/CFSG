module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness

/-!
# Application of compact lifting to the raw order bound

The literal compact relations and generation proved by `CompactLifting`
discharge two premises of `raw_bound_of_compact`. Only the independently
owned compact order bound remains. The assembly parent does not import this
application module, so there is no import cycle.
-/

public section
namespace Rudvalis.Multiplier.TwoPrimary.LocalPresentation
open PresentationFaithfulness

/-- Compact lifting reduces the raw order bound to the compact order bound alone. -/
theorem raw_bound_of_compact_order
    (hbound : Finite CompactPresentation ∧ Nat.card CompactPresentation ≤ 2048) :
    Finite RawPresentation ∧ Nat.card RawPresentation ≤ 2048 :=
  raw_bound_of_compact compactRelator_eval compactImage_generates hbound

end Rudvalis.Multiplier.TwoPrimary.LocalPresentation
