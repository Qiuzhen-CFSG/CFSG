module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.PowerIdentities
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection

/-!
# Applying both checked power relations to central collection

This supplies both zero-exponent power premises of `collection_of_four_identities`.
The two independently owned commutator identities remain explicit; their
unconditional assembly belongs to the collection owner. The earlier interface
taking the first power identity explicitly is retained.
Source: the literal seven ATLAS words `S62G1-P1.M`.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection

theorem collection_of_power_and_commutator_identities
    (hpower : powerDefect = centralRelator 6)
    (hfour : centralRelator 4 = centralRelator 6)
    (hfive : centralRelator 5 = centralRelator 6)
    (x : Central) (hxD : x ∈ commutator Central) (hx : centralProjection x = 1) :
    x = 1 ∨ x = defect :=
  collection_of_four_identities hpower mixedDefect_eq_centralRelator_six hfour hfive x hxD hx

/-- Supply both power identities to the literal derived-kernel collection theorem. -/
theorem collection_of_commutator_identities
    (hfour : centralRelator 4 = centralRelator 6)
    (hfive : centralRelator 5 = centralRelator 6)
    (x : Central) (hxD : x ∈ commutator Central) (hx : centralProjection x = 1) :
    x = 1 ∨ x = defect :=
  collection_of_four_identities powerDefect_eq_centralRelator_six
    mixedDefect_eq_centralRelator_six hfour hfive x hxD hx

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection
