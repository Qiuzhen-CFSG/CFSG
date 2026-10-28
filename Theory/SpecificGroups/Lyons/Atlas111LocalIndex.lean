module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexSetup

/-!
# Assembly of the concrete Lyons local-index certificates

Coverage and separation of 8835156 right cosets imply the requested index.
The two certificates concern the exact matrix subgroup of `Atlas111OrderSetup`;
no ambient order or simplicity assumption is used. This module currently proves
that implication. The concrete coverage and separation certificates remain to
be constructed.

Source for the subgroup words: ATLAS of Finite Group Representations,
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/LyG1-max1W1 .
-/

namespace Lyons.OrderCertificate

/-- Assemble independently constructed coverage and separation certificates. -/
public theorem localIndex_eq_of_cover_and_separation
    (C : Subgroup.GeneratorCosetCover localSubgroup indexGenerator (Fin 8835156))
    (r : Fin 8835156 → LyonsGroup)
    (hsep : ∀ i j, r i * (r j)⁻¹ ∈ localSubgroup → i = j) :
    localSubgroup.index = 8835156 :=
  (localIndex_le_of_cover C).antisymm (le_localIndex_of_separation r hsep)

end Lyons.OrderCertificate
