module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Candidates
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Quotients.PureInnerCore.WordOrder
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Quotients.PureInnerCore.CenterImage
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders

/-!
# The intrinsic two-core of Held's pure pair product

The pair product B has order 9216 and contains the certified normal word
subgroup of order 256. The certified action of B on the center of that
subgroup has image of order 36 with trivial two-core. Its kernel therefore
has order 256 and contains O₂(B). The lower bound forces equality. Every
element centralizing O₂(B) fixes that center, so equality also gives
self-centralization.

We retain the conditional reductions and discharge their two action-image
premises in the final intrinsic core theorems. Both conclusions concern
the literal subgroup B = innerLocal true, without any model hypotheses.
Sources: Aschbacher--Smith 15.3.41--42, printed p.1138; GLS3 Table 5.3p.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile

private theorem pure_core_le_centerAction_kernel
    (hbot : pCore 2 pureCenterAction.range = ⊥) :
    pCore 2 (innerLocal true) ≤ pureCenterAction.ker := by
  let f := pureCenterAction.rangeRestrict
  have hn : ((pCore 2 (innerLocal true)).map f).Normal :=
    Normal.map inferInstance f pureCenterAction.rangeRestrict_surjective
  have hm : (pCore 2 (innerLocal true)).map f ≤ pCore 2 pureCenterAction.range :=
    le_sSup ⟨hn, pCore_isPGroup.map f⟩
  rw [hbot] at hm
  intro x hx
  have he : f x = 1 := hm (mem_map.mpr ⟨x, hx, rfl⟩)
  exact congrArg Subtype.val he

theorem pure_inner_core_card_of_centerAction
    (hcard : Nat.card pureCenterAction.range = 36)
    (hbot : pCore 2 pureCenterAction.range = ⊥) :
    Nat.card (pCore 2 (innerLocal true)) = 256 := by
  have hk := pureCenterAction.ker.card_mul_index
  rw [index_ker, hcard] at hk
  have hB : Nat.card (innerLocal true) = 9216 :=
    (Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.candidateOrders false 0).2.2
  rw [hB] at hk
  have hu := card_le_of_le (pure_core_le_centerAction_kernel hbot)
  have hl := pure_inner_core_card_lower
  omega

theorem pure_inner_core_eq_centerAction_kernel
    (hcard : Nat.card pureCenterAction.range = 36)
    (hbot : pCore 2 pureCenterAction.range = ⊥) :
    pCore 2 (innerLocal true) = pureCenterAction.ker := by
  apply eq_of_le_of_card_ge (pure_core_le_centerAction_kernel hbot)
  rw [pure_inner_core_card_of_centerAction hcard hbot]
  have hk := pureCenterAction.ker.card_mul_index
  rw [index_ker, hcard] at hk
  have hB : Nat.card (innerLocal true) = 9216 :=
    (Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.candidateOrders false 0).2.2
  rw [hB] at hk
  omega

theorem pure_inner_core_selfCentralizing_of_centerAction
    (hcard : Nat.card pureCenterAction.range = 36)
    (hbot : pCore 2 pureCenterAction.range = ⊥) :
    centralizer (pCore 2 (innerLocal true) : Set (innerLocal true)) ≤
      pCore 2 (innerLocal true) := by
  intro x hx
  rw [pure_inner_core_eq_centerAction_kernel hcard hbot]
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro z
  apply Subtype.ext
  apply Subtype.ext
  change x * (z : pureWordCore) * x⁻¹ = (z : pureWordCore)
  rw [← mem_centralizer_iff.mp hx (z : pureWordCore)
    (pureWordCore_le_pCore (z : pureWordCore).property)]
  simp only [mul_inv_cancel_right]

/-- The intrinsic two-core of the literal pure pair product has order 256. -/
theorem pure_inner_core_card :
    Nat.card (pCore 2 (innerLocal true)) = 256 :=
  pure_inner_core_card_of_centerAction
    pureCenterAction_range_card pureCenterAction_range_twoCore

/-- The intrinsic two-core is self-centralizing inside the pure pair product. -/
theorem pure_inner_core_selfCentralizing :
    centralizer (pCore 2 (innerLocal true) : Set (innerLocal true)) ≤
      pCore 2 (innerLocal true) :=
  pure_inner_core_selfCentralizing_of_centerAction
    pureCenterAction_range_card pureCenterAction_range_twoCore

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
