module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Quotients.InnerNormalizers
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Coordinates

/-!
# The pure-pair normalizer contains an actual outer actor

The certified quarter-turn preserves both literal factors of the pure pair.
If it were inner, self-normalization of the two-factor would put its conjugator
in that factor, whose checked orbit colors force a diagonal plane action.
The quarter-turn is not diagonal. Thus the full inner index is two, and the
checked inner order 9216 gives full normalizer order 18432.

Source: GLS3 Table 5.3p; the unchanged ATLAS model and the PureActors certificates;
Aschbacher--Smith 15.3.41--42, printed p.1138. No core order is used here.
-/

public section
open Subgroup Theory.GroupTheory Held.LocalPairs
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
open Held.LocalPairs.PairCoverage.LocalActions
open Held.LocalPairs.SylowGeometry.Calculations

open RepresentativeImages

/-- The already certified pure-pair outer actor in the full automorphism group. -/
@[expose] def pureAutomorphism : MulAut Held.He :=
  Held.permutationGroup.normalizerMonoidHom (PureActors.actor false).val

/-- The actor preserves both factors and hence their literal join. -/
theorem pureAutomorphism_mem : pureAutomorphism ∈ candidate true := by
  change (candidateOdd false 0 ⊔ candidateTwo false 0).map pureAutomorphism.toMonoidHom =
    candidateOdd false 0 ⊔ candidateTwo false 0
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (PureActors.actor false).property.2
    (PureActors.actor false).property.1

/-- Inner pair actors preserve the two marked axes; the quarter-turn does not. -/
theorem pureAutomorphism_not_inner : pureAutomorphism ∉ MulAut.innerSubgroup Held.He := by
  rintro ⟨x, hx⟩
  have hn : x ∈ normalizer (candidateTwo false 0 : Set Held.He) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hx]
    exact (PureActors.actor false).property.1
  have hxS : x ∈ candidateTwo false 0 := by
    rwa [InnerImages.candidateTwo_normalizer InnerNormalizer.normalizer_eq false 0] at hn
  apply PureActors.coordinateAction_not_mem_diagonal false
  apply InnerImages.mem_diagonal_of_vectors
  intro k
  apply InnerImages.coordinates_of_conjugation false 0 k x hxS
  rw [InnerImages.markedEmbedding_eq, PureActors.candidateOddEquiv_symm_image]
  apply Held.representation_injective
  rw [← PureActors.actor_conj_basis]
  have he := MulEquiv.congr_fun hx (basisGenerator false 0 k)
  exact (congrArg Held.representation he).symm

/-- The explicit outer actor makes the inner index exactly two. -/
theorem candidate_true_inner_index
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2) :
    ((MulAut.innerSubgroup Held.He).subgroupOf (candidate true)).index = 2 := by
  let I := (MulAut.innerSubgroup Held.He).subgroupOf (candidate true)
  have hp : I ≠ ⊤ := by
    intro he
    have hm : (⟨pureAutomorphism, pureAutomorphism_mem⟩ : candidate true) ∈ I :=
      he ▸ Subgroup.mem_top _
    exact pureAutomorphism_not_inner hm
  have h1 := I.one_lt_index_of_ne_top hp
  have h2 := Nat.le_of_dvd (by decide : 0 < 2) (normalizer_inner_index_dvd_two (innerLocal true) hreal hbound)
  change I.index ≤ 2 at h2
  exact Nat.le_antisymm h2 h1

/-- The second full automorphism normalizer has order 18432. -/
theorem candidate_true_card
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2) :
    Nat.card (candidate true) = 18432 := by
  let I := (MulAut.innerSubgroup Held.He).subgroupOf (candidate true)
  have he := Nat.card_congr (normalizerInnerEquiv (innerLocal true) (innerLocal_self_normalizing true)).toEquiv
  change Nat.card (innerLocal true) = Nat.card I at he
  rw [← I.card_mul_index, candidate_true_inner_index hreal hbound, ← he]
  change Nat.card (Exhaustion.candidateProduct false 0) * 2 = 18432
  rw [(Exhaustion.candidateOrders false 0).2.2]


end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
