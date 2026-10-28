module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.SubgroupOrder.LinearOrder.UpperBound.Table1
public import Theory.SpecificGroups.ONan.ProjectiveOrder.SubgroupOrder.LinearOrder.UpperBound.Table2
public import Theory.SpecificGroups.ONan.ProjectiveOrder.SubgroupOrder.LinearOrder.UpperBound.Table3
public import Theory.SpecificGroups.ONan.ProjectiveOrder.SubgroupOrder.LinearOrder.UpperBound.Table4

/-!
# Cardinality assembly for the four smaller levels

The four concrete transition statements imply the bound 56 * 6 * 2 * 2 = 1344
for the first proper word subgroup. This interface is independent of the
2793-representative first level. All subgroups and candidate words are defined
in `Chain.lean` and the four table modules, with sources in `source/`.
-/

namespace ONan.OrderCertificate

open LinearUpperBound

/-- Four certified tail transitions bound the first proper word subgroup. -/
public theorem linearUpperBound_tail_of_steps
    (h1 : Step1) (h2 : Step2) (h3 : Step3) (h4 : Step4) :
    Nat.card group1 ≤ 1344 := by
  have hb4 : Nat.card group4 ≤ 2 := by
    simpa only [group5_card, Nat.mul_one] using card_le_of_step4 h4
  have hb3 : Nat.card group3 ≤ 4 :=
    (card_le_of_step3 h3).trans (Nat.mul_le_mul_left 2 hb4)
  have hb2 : Nat.card group2 ≤ 24 :=
    (card_le_of_step2 h2).trans (Nat.mul_le_mul_left 6 hb3)
  exact (card_le_of_step1 h1).trans (Nat.mul_le_mul_left 56 hb2)

end ONan.OrderCertificate
