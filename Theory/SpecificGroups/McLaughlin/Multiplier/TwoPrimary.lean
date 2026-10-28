module

public import Theory.SpecificGroups.McLaughlin.Multiplier.TwoPrimary.Local
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.Transfer
public import Theory.SpecificGroups.McLaughlin.Multiplier.PrimeSupport
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL

/-!
# The local double-cover argument for McLaughlin's two-primary multiplier

Schur's certified universal cover of A₈ splits every finite central extension.
A specified embedding of that very group in McL therefore supplies a section
of any finite perfect central cover over its image. Its order is 40320, so the
image has odd index 22275, and central transfer excludes two from the original
kernel. The specialization retains the literal constructed universal projection.

The actual embedding remains an explicit input here. It is not replaced by an
order identity, a group-family label, or a multiplier assumption. The concrete
involution-centralizer construction must discharge this input before the McL
two-primary exclusion is complete.

Source: R. L. Griess, Jr., The Schur multiplier of McLaughlin's simple group,
Arch. Math. 48 (1987), p.31, doi:10.1007/BF01196350; GLS3, Theorem 5.2.3.
-/

public section

namespace Theory.SpecificGroups.McLaughlin.Multiplier.TwoPrimary

open Subgroup Theory.GroupTheory PerfectCentralCovering
open Atlas.Sporadic.McLaughlin

universe u

/-- Every embedded certified double cover has the source's odd index. -/
theorem doubleCover_embedding_index
    (j : DoubleCover →* Model) (hj : Function.Injective j) :
    j.range.index = 22275 := by
  have h := j.range.card_mul_index
  rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv,
    doubleCover_card, Atlas.Sporadic.McLaughlin.card] at h
  change 40320 * j.range.index = 898128000 at h
  omega

/-- Local splitting and transfer exclude two from the original covering kernel.
Only the actual double-cover embedding remains to be constructed. -/
theorem not_two_dvd_kernel_of_doubleCover_embedding
    (j : DoubleCover →* Model) (hj : Function.Injective j)
    {E : Type u} [Group E] [Finite E] (f : Cover E Model) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨s, hs⟩ := exists_local_section_of_doubleCover_equiv
    f j.range (MonoidHom.ofInjective hj).symm
  exact not_dvd_card_kernel_of_section f j.range
    (by rw [doubleCover_embedding_index j hj]; decide) s hs

/-- The same calculation for an embedding into the literal ATLAS permutation
carrier, transported by the separately supplied actual model comparison. -/
theorem not_two_dvd_kernel_of_carrier_embedding
    (comparison : Sporadic.LeechRelated.McL.Carrier ≃* Model)
    (j : DoubleCover →* Sporadic.LeechRelated.McL.Carrier)
    (hj : Function.Injective j)
    {E : Type u} [Group E] [Finite E] (f : Cover E Model) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker :=
  not_two_dvd_kernel_of_doubleCover_embedding
    (comparison.toMonoidHom.comp j) (comparison.injective.comp hj) f

/-- The local argument specialized to the actual constructed universal map. -/
theorem not_two_dvd_universal_kernel_of_carrier_embedding
    (comparison : Sporadic.LeechRelated.McL.Carrier ≃* Model)
    (j : DoubleCover →* Sporadic.LeechRelated.McL.Carrier)
    (hj : Function.Injective j) :
    ¬ 2 ∣ Nat.card (universalProjection Model).ker :=
  not_two_dvd_kernel_of_carrier_embedding comparison j hj (universalCover Model)

end Theory.SpecificGroups.McLaughlin.Multiplier.TwoPrimary
