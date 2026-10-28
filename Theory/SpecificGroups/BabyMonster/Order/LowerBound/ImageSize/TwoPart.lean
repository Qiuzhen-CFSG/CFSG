module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.Reduction
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.TwoPart.Candidates
public import Theory.GroupTheory.BinaryNormalForm

/-!
# Binary normal-form route to the Baby Monster two-part

A sequence of 41 words in the fixed standard matrix subgroup suffices once
its binary products are closed under division and distinct. The normal-form
count gives a subgroup of order `2^41`, so Lagrange proves the required
divisibility. This assembly does not identify either candidate local subgroup.

The concrete sequence, collection identities, and separation certificate are
still required. Only the conditional assembly is proved in this module.
Candidate source: ATLAS `BG1-max2W1` and `BG1-max4W1`, with provenance in
`ImageSize/source/README.md`.
-/

public section

namespace BabyMonster.OrderLowerBound

/-- Assemble the two independent normal-form certificates for concrete words.
This is not the unconditional two-part certificate. -/
theorem standardImage_twoPart_dvd_of_binaryNormalForm
    (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (g : Fin 41 → standardImage ha hb)
    (hcollect : Subgroup.BinaryNormalForm.DivisionClosed g)
    (hseparate : Function.Injective (Subgroup.BinaryNormalForm.product g)) :
    2 ^ 41 ∣ Nat.card (standardImage ha hb) :=
  Subgroup.BinaryNormalForm.pow_dvd_card g hcollect hseparate

end BabyMonster.OrderLowerBound
