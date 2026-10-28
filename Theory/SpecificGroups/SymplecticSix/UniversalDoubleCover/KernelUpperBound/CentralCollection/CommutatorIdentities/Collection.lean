module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.CommutatorIdentities
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection

/-!
# Applying both commutator identities to central collection

The commutator certificate discharges the fourth and fifth relator premises
of `collection_of_four_identities`. The two independent mixed-power identities
remain explicit for their assembly owner. This adapter is separate from the
word identities so that the collection module can import those identities
without introducing an import cycle.

Source: the seven ATLAS S62G1-P1.M relators; see
`CommutatorIdentities/source/README.md` for the checked commutator calculation.
-/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection

/-- Actual collection consumer, with both commutator premises discharged. -/
theorem collection_of_two_power_identities
    (hpower : powerDefect = centralRelator 6)
    (hmixed : mixedDefect = centralRelator 6)
    (x : Central) (hxD : x ∈ commutator Central) (hx : centralProjection x = 1) :
    x = 1 ∨ x = defect :=
  collection_of_four_identities hpower hmixed centralRelator_four_eq_six
    centralRelator_five_eq_six x hxD hx


end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection
