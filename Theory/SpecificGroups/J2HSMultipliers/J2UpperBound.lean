module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalReduction
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer
public import Theory.SpecificGroups.J2HSMultipliers.J2DoubleCover

/-!
# Upper bounds for perfect central kernels over J₂

Every finite perfect central cover of J₂ has kernel of order at most two.
The odd-primary exclusion in `OddPrimary` first makes the kernel a two-group.
Central transfer at the marked involution centralizer of index 315 then
bounds it by the local universal kernel. The checked presentation calculation
in `LocalCentralizer` bounds that local kernel by two.

The canonical universal projection and the actual icosian comparison are
included, so the local calculation feeds the existing double-cover recognition
without reconstructing the lower bound.
Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407; GLS3 §6.1.
-/

public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2
open Sporadic.LeechRelated.J2 PerfectCentralCovering

/-- Every finite perfect central extension of the literal permutation model
of J₂ has kernel of order at most two. -/
theorem kernel_card_le_two
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Carrier) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) : Nat.card f.ker ≤ 2 :=
  kernel_card_le_two_of_local_bound local_universal_kernel_card_le_two f hf hk

/-- The canonical universal projection already has a two-group kernel. -/
theorem universal_kernel_isPGroup :
    IsPGroup 2 (universalProjection Carrier).ker :=
  kernel_isPGroup _ (universalProjection_surjective _) (universalProjection_ker_le_center _)

/-- Canonical-projection application of the local-to-global upper bound. -/
theorem universal_kernel_card_le_two_of_local_bound
    (hlocal : Nat.card (universalProjection ExceptionalParabolics.Seed.l₁).ker ≤ 2) :
    Nat.card (universalProjection Carrier).ker ≤ 2 :=
  kernel_card_le_two_of_local_bound hlocal _
    (universalProjection_surjective _) (universalProjection_ker_le_center _)

/-- The canonical universal projection of the permutation model has kernel
of order at most two, with the local calculation discharged. -/
theorem universal_kernel_card_le_two :
    Nat.card (universalProjection Carrier).ker ≤ 2 :=
  universal_kernel_card_le_two_of_local_bound local_universal_kernel_card_le_two

/-- Transport through the actual permutation–icosian equivalence, preserving the kernel. -/
theorem icosian_kernel_card_le_two_of_local_bound
    (hlocal : Nat.card (universalProjection ExceptionalParabolics.Seed.l₁).ker ≤ 2)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Atlas.Sporadic.Janko2.Model) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) : Nat.card f.ker ≤ 2 := by
  let e := IcosianComparison.comparison.symm
  let g : E →* Carrier := e.toMonoidHom.comp f
  have hg : g.ker = f.ker := MonoidHom.ker_comp_of_injective _ _ e.injective
  have hb := kernel_card_le_two_of_local_bound hlocal g (e.surjective.comp hf)
    (hg.le.trans hk)
  rwa [hg] at hb

/-- This is the exact upper-bound premise used by `J2DoubleCover.kernel_equiv_two_of_bound`. -/
theorem icosian_universal_kernel_card_le_two_of_local_bound
    (hlocal : Nat.card (universalProjection ExceptionalParabolics.Seed.l₁).ker ≤ 2) :
    Nat.card (universalProjection Atlas.Sporadic.Janko2.Model).ker ≤ 2 :=
  icosian_kernel_card_le_two_of_local_bound hlocal _
    (universalProjection_surjective _) (universalProjection_ker_le_center _)

/-- The same bound for every finite perfect central cover of the actual
icosian model, through the proved permutation–icosian equivalence. -/
theorem icosian_kernel_card_le_two
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Atlas.Sporadic.Janko2.Model) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) : Nat.card f.ker ≤ 2 :=
  icosian_kernel_card_le_two_of_local_bound local_universal_kernel_card_le_two f hf hk

/-- The canonical icosian universal kernel satisfies the exact upper-bound
premise of `kernel_equiv_two_of_bound`. -/
theorem icosian_universal_kernel_card_le_two :
    Nat.card (universalProjection Atlas.Sporadic.Janko2.Model).ker ≤ 2 :=
  icosian_universal_kernel_card_le_two_of_local_bound local_universal_kernel_card_le_two

end Theory.SpecificGroups.J2HSMultipliers.J2
