module

public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.CoreSplitting
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.NormalizerBound

/-!
# The two-primary HS covering bound

Four does not divide the kernel order of a finite perfect central cover of
the literal HS carrier whose kernel is a two-group. Restriction to the
elementary-eight normalizer preserves the kernel and has perfect domain by
odd-index transfer. Its actual C₄³ core has a section in every central cover.
That section lifts `e0` to an involution, and the checked HS conjugator supplies
the specified noncore involution lift. The normalizer kernel bound then applies
with every local premise discharged.

The conditional local reductions remain reexported from `LocalReduction`,
`CoreSplitting` and `NormalizerBound`. No simplicity or perfectness assumption
on the base carrier, invariant core section, or order-two kernel assumption is
needed. The parent `HSUpperBound` proves that the kernel is a two-group and
owns the final bound-of-two assembly.

Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407; GLS3 §6.1,
Table 6.1.3 and Table 5.3m. The local proofs use independently checked
normalizer geometry, without assuming the I.2.2 double-cover conclusions.
-/

namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary
open Subgroup
open Sporadic.LeechRelated.HS

/-- Four cannot divide a two-group kernel of an arbitrary finite perfect
central cover of the literal HS carrier. Both local premises of the restriction
and fusion reduction are discharged. -/
public theorem not_four_dvd_card_kernel
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Carrier) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hp : IsPGroup 2 f.ker) :
    ¬ 4 ∣ Nat.card f.ker := by
  apply not_four_dvd_of_local_bound f hf hk hp
  intro D _ _ _ g hg hkg hpg hsection hlift
  exact NormalizerBound.card_kernel_le_two g hg hkg hpg hsection hlift

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary
