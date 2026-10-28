module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Level0.Steps
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Level1.Steps
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Level2.Steps
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Level3.Steps
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Level4.Steps
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Level5.Steps
import Mathlib.Tactic.FinCases

/-!
# The certified group has order 44,352,000

Part of the order-divisibility certificate for the exact ATLAS HS carrier.
Source: GLS volume 3, Table 5.3m, printed p.274; ATLAS HSG1-p100B0.
The generator in `OrderBound/source/` supplies witnesses only. Every finite
identity is checked by Lean's kernel.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.OrderCertificate
open Theory.GroupTheory
set_option maxRecDepth 100000
set_option Elab.async false

/-- The auxiliary certified group has the tabulated HS order. -/
theorem H0_card : Nat.card H0 = 44352000 := by
  rw [card0, card1, card2, card3, card4, card5]
  rw [H6, wordSubgroup_fin_zero_card]


end Sporadic.LeechRelated.HS.OrderCertificate
