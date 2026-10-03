module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RefinedCountData

/-!
# Commuting witnesses and fiber tallies for refined Ree two counts

Kernel reduction verifies the commuting lists, matching cardinality products,
and the two selected fiber tallies. The actual internal-centralizer orders
follow from the conjugacy witnesses and `centralizer_card_bounds` in the final
assembly. The data use the root conventions of Shinoda (1975), (2.3).
-/

@[expose] public section
namespace ReeTwo.SylowModel.RefinedCounting
set_option maxRecDepth 32768

theorem countCentralizers_valid : ∀ c j, countFour c j = true →
    countCentralizerTest c j = true := by
  decide +kernel

theorem countProfile_valid : ∀ c v, (countFiber c v 32, countFiber c v 64) = refinedProfile c v := by
  decide +kernel

end ReeTwo.SylowModel.RefinedCounting
