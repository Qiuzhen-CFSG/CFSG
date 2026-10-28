module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Orders

/-!
# The marked overlap of the two Tits parabolics

The overlap contains the Sylow subgroup of order 2048. Its order divides
both 10240 and 6144, so it is exactly that Sylow subgroup. Each Sylow
normalizer is also the Sylow subgroup: its prime index permits no proper
intermediate subgroup, while adjoining a normalizing involution would give
a larger two-subgroup, contradicting Sylow maximality.

This identifies the full common overlap and its inclusions. The compatible
isomorphism with the earlier intersection amalgam preserves the existing API.
The local two-cores and the full automorphism extension are separate calculations.

Source: Parrott (1972), pp. 672, 683--684; Aschbacher--Smith, F.1.1 and
F.1.11--12, printed pp. 259, 262--264, and 14.2.21, printed pp. 988--989.
-/

@[expose] public section

namespace Tits.ExceptionalParabolics

open Theory.GroupTheory

/-- The Sylow subgroup is the entire common overlap. -/
theorem overlap_eq_sylow : overlap = S := by
  have hd1 : Nat.card overlap ∣ 10240 := by
    rw [← first_card]
    exact Subgroup.card_dvd_of_le (show overlap ≤ first from inf_le_left)
  have hd2 : Nat.card overlap ∣ 6144 := by
    rw [← second_card]
    exact Subgroup.card_dvd_of_le (show overlap ≤ second from inf_le_right)
  have hd : Nat.card overlap ∣ 2048 := Nat.dvd_gcd hd1 hd2
  apply (Subgroup.eq_of_le_of_card_ge sylow_le_overlap _).symm
  rw [sylow_card]
  exact Nat.le_of_dvd (by decide) hd

private theorem prime_index_normalizer {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (hp : H.index.Prime) (hn : ¬ H.Normal) :
    Subgroup.normalizer (H : Set G) = H := by
  have hd := Subgroup.index_dvd_of_le H.le_normalizer
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · exact (hn (Subgroup.normalizer_eq_top_iff.mp (Subgroup.index_eq_one.mp h))).elim
  · have he := Subgroup.relIndex_mul_index H.le_normalizer
    rw [h] at he
    have hrel : H.relIndex (Subgroup.normalizer H) = 1 := by
      nlinarith [hp.pos]
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel) H.le_normalizer

private theorem sylow_not_normal (P : Subgroup Atlas1600Group) (r : Atlas1600Group)
    (hr : r ^ 2 = 1) (hP : S ⊔ Subgroup.closure {r} = P)
    (hSP : S ≤ P) (hcard : Nat.card P ≠ 2048) : ¬ (S.subgroupOf P).Normal := by
  intro hn
  have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hSP).mp hn
  have hs : IsPGroup 2 S := IsPGroup.of_card (n := 11) (by simpa using sylow_card)
  have hrp : IsPGroup 2 (Subgroup.closure ({r} : Set Atlas1600Group)) := by
    rw [← Subgroup.zpowers_eq_closure]
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers]
    simpa only [pow_one] using orderOf_dvd_of_pow_eq_one hr
  have hjoin : IsPGroup 2 (S ⊔ Subgroup.closure ({r} : Set Atlas1600Group) : Subgroup Atlas1600Group) :=
    hs.to_sup_of_normal_left' hrp (by rw [← hP] at hnorm; exact le_sup_right.trans hnorm)
  have hp : IsPGroup 2 P := hP ▸ hjoin
  have heq : P = S := by
    simpa only [atlas1600SylowTwo_coe] using
      atlas1600SylowTwo.is_maximal' hp (by simpa only [atlas1600SylowTwo_coe] using hSP)
  exact hcard (heq ▸ sylow_card)

/-- The normalizer in the first full parabolic is computed relatively. -/
theorem first_sylow_normalizer :
    Subgroup.normalizer (S.subgroupOf first : Set first) = S.subgroupOf first := by
  apply prime_index_normalizer
  · rw [first_sylow_index]; decide
  · apply sylow_not_normal first (atlas1600ParrottAssignment .r1)
    · simpa [parrottRelator] using atlas1600ParrottAssignment_relations .i_r1
    · rfl
    · exact sylow_le_first
    · rw [first_card]; decide

/-- The normalizer in the second full parabolic is computed relatively. -/
theorem second_sylow_normalizer :
    Subgroup.normalizer (S.subgroupOf second : Set second) = S.subgroupOf second := by
  apply prime_index_normalizer
  · rw [second_sylow_index]; decide
  · apply sylow_not_normal second (atlas1600ParrottAssignment .r8)
    · simpa [parrottRelator] using atlas1600ParrottAssignment_relations .i_r8
    · rfl
    · exact sylow_le_second
    · rw [second_card]; decide

/-- The actual common overlap has order 2048. -/
theorem overlap_card : Nat.card overlap = 2048 := by
  rw [overlap_eq_sylow, sylow_card]

/-- The same inclusion amalgam with the certified Sylow subgroup as its middle group. -/
def sylowAmalgam : RankTwoAmalgam first S second :=
  RankTwoAmalgam.ofSubgroups first S second sylow_le_first sylow_le_second

/-- Identifying the middle groups preserves both inclusion maps. -/
def sylowAmalgamIso : RankTwoAmalgam.Iso sylowAmalgam amalgam where
  left := MulEquiv.refl _
  middle := MulEquiv.subgroupCongr overlap_eq_sylow.symm
  right := MulEquiv.refl _
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

end Tits.ExceptionalParabolics
