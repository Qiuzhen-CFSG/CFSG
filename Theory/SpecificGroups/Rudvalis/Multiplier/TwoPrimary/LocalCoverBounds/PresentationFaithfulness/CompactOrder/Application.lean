module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactOrder
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness

/-!
# Applying the compact order bound to the original max4 presentation

The order premise of `modelMap_injective_of_compact` is discharged here by
the literal compact-presentation bound. The independently owned lifting
premises remain explicit: the retained raw generators satisfy all compact
relations and generate the raw presentation. The parent faithfulness assembly
owns their final discharge. No reverse dependency from `CompactOrder` to the
parent assembly is introduced.
-/

public section
namespace Rudvalis.Multiplier.TwoPrimary.LocalPresentation.PresentationFaithfulness.CompactOrder
open Subgroup.CosetWordCertificate

/-- Application to the original model map, with only compact lifting left to prove. -/
theorem modelMap_injective_of_lifting
    (hrel : ∀ r : Fin 159, eval compactImage (compactRelator r) = 1)
    (hgen : Subgroup.closure (Set.range compactImage) = ⊤) :
    Function.Injective modelMap :=
  modelMap_injective_of_compact hrel hgen compactPresentation_bound

end Rudvalis.Multiplier.TwoPrimary.LocalPresentation.PresentationFaithfulness.CompactOrder
