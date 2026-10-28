module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.SubgroupOrder.LinearOrder.UpperBound.Table0
public import Theory.SpecificGroups.ONan.ProjectiveOrder.SubgroupOrder.LinearOrder.UpperBound.TailAssembly

/-!
# Assembly of the linear local subgroup upper-bound certificate

The supplied word chain has proposed indices 2793, 56, 6, 2, 2, followed by
the subgroup on no generators. This module proves the upper bound from the
five concrete transition statements. The remaining inputs are equalities of
words in the actual GL(45,7) generators, not claims about a permutation action.

The separate first-level and tail interfaces permit independent verification
of the large 2793-representative table and the 1344-element tail. The target
unconditional upper bound requires both concrete certificates.

Source matrices, words and attribution: `refs/original/onan/`,
`ProjectiveOrder/source/`, and `UpperBound/source/`.
-/

namespace ONan.OrderCertificate

open LinearUpperBound

/-- The two independent numerical pieces combine to the requested upper bound. -/
public theorem linearLocalSubgroup_card_le_of_chain_bounds
    (hhead : Nat.card group0 ≤ 2793 * Nat.card group1)
    (htail : Nat.card group1 ≤ 1344) :
    Nat.card linearLocalSubgroup ≤ 3753792 := by
  rw [← group0_eq]
  exact hhead.trans (Nat.mul_le_mul_left 2793 htail)

/-- All five concrete matrix transition tables suffice; no faithfulness or
lower-bound hypothesis is used. -/
public theorem linearLocalSubgroup_card_le_of_chain_steps
    (h0 : Step0) (h1 : Step1) (h2 : Step2) (h3 : Step3) (h4 : Step4) :
    Nat.card linearLocalSubgroup ≤ 3753792 :=
  linearLocalSubgroup_card_le_of_chain_bounds (card_le_of_step0 h0)
    (linearUpperBound_tail_of_steps h1 h2 h3 h4)

end ONan.OrderCertificate
