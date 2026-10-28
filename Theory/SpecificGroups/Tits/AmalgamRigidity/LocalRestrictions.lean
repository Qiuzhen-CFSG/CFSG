module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.Common
public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.Witnesses
public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.FirstExtension
public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.SecondExtension

/-!
# The two Tits endpoint restriction groups have at least 4096 elements

The common restriction subgroup has proved order 2048. An endpoint extension
whose restriction is outside the other endpoint makes this common subgroup
proper in the first one. Lagrange's theorem then gives at least 4096 distinct
restrictions. The constructed endpoint automorphisms have generator-image pairs
(69,1024) and (76,1168), certified to lie outside the opposite restriction group.
Their compatibility proofs use the literal Sylow inclusions.

The final theorems apply both unconditional counts to the Sylow carrier and
the actual whole overlap, with both original inclusion maps. Every overlap
automorphism factors through the endpoint restrictions. The separate full
binary Ree calculation and the Chapter F source assembly are not asserted here.

Source context: Parrott (1972), §5, p.683; Aschbacher--Smith F.1.11--12,
printed pp.262--263; Fan, Amalgams of prime index, J. Algebra 98 (1986),
375--421. This calculation does not assume any unverified Fan theorem.
-/

public section
noncomputable section
namespace Tits.AmalgamRigidity
open Theory.GroupTheory RankTwoAmalgam ExceptionalParabolics

private theorem double_card_of_extra {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (hcard : Nat.card (H ⊓ K : Subgroup G) = 2048)
    (f : G) (hf : f ∈ H) (hnot : f ∉ K) : 4096 ≤ Nat.card H := by
  have hne : Nat.card H ≠ 2048 := by
    intro he
    have heq : H ⊓ K = H :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [he, hcard])
    exact hnot (show f ∈ H ⊓ K from heq.symm ▸ hf).2
  have hd := Subgroup.card_dvd_of_le (inf_le_left : H ⊓ K ≤ H)
  rw [hcard] at hd
  obtain ⟨k, hk⟩ := hd
  have hp : 0 < Nat.card H := Nat.card_pos
  omega

/-- One additional first endpoint extension gives 4096 distinct restrictions. -/
theorem firstRestrictions_card_ge_of_extra (h : FirstExtraExtension) :
    4096 ≤ Nat.card firstRestrictions := by
  obtain ⟨f, hf, hp⟩ := h
  exact double_card_of_extra _ _ restriction_intersection_card f hf
    (first_pair_not_second f hf hp)

/-- One additional second endpoint extension gives 4096 distinct restrictions. -/
theorem secondRestrictions_card_ge_of_extra (h : SecondExtraExtension) :
    4096 ≤ Nat.card secondRestrictions := by
  obtain ⟨f, hf, hp⟩ := h
  exact double_card_of_extra secondRestrictions firstRestrictions
    (by rw [inf_comm]; exact restriction_intersection_card) f hf
    (second_pair_not_first f hf hp)

/-- The two extension witnesses remove every twist on the literal whole overlap. -/
theorem factorsThrough_of_extra_extensions (hfirst : FirstExtraExtension)
    (hsecond : SecondExtraExtension) (d : MulAut overlap) : FactorsThrough amalgam d :=
  factorsThrough_of_counts (firstRestrictions_card_ge_of_extra hfirst)
    (secondRestrictions_card_ge_of_extra hsecond) d

/-- At least 4096 distinct Sylow automorphisms extend to the actual first endpoint. -/
theorem firstRestrictions_card_ge : 4096 ≤ Nat.card firstRestrictions :=
  firstRestrictions_card_ge_of_extra firstExtraExtension

/-- At least 4096 distinct Sylow automorphisms extend to the actual second endpoint. -/
theorem secondRestrictions_card_ge : 4096 ≤ Nat.card secondRestrictions :=
  secondRestrictions_card_ge_of_extra secondExtraExtension

/-- Every automorphism of the marked Sylow carrier factors through its endpoints. -/
theorem sylow_factorsThrough (d : MulAut S) : FactorsThrough sylowAmalgam d :=
  sylow_factorsThrough_of_counts firstRestrictions_card_ge secondRestrictions_card_ge d

/-- Every twist of the literal whole overlap is removed by endpoint automorphisms. -/
theorem factorsThrough (d : MulAut overlap) : FactorsThrough amalgam d :=
  factorsThrough_of_counts firstRestrictions_card_ge secondRestrictions_card_ge d

end Tits.AmalgamRigidity
