module

public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Squares of quaternion automorphisms of two-power order

The square of an automorphism of two-power order of a quaternion group of
order eight is inner. The inner automorphism subgroup is normal and has
index six. In its quotient, the order of the given element divides both six
and a power of two, and hence divides two.

This is the factor-preserving case of the quaternion central-product action
in Janko–Thompson (1970), §4, pp.390–391.
-/

namespace QuaternionGroup

/-- The square of a quaternion automorphism of two-power order is inner. -/
public theorem exists_conj_sq_of_two_pow_eq_one_of_equiv
    {G : Type*} [Group G] (model : G ≃* QuaternionGroup 2)
    (e : MulAut G) (n : ℕ) (he : e ^ (2 ^ n) = 1) :
    ∃ q : G, e ^ 2 = MulAut.conj q := by
  let N := (MulAut.conj : G →* MulAut G).range
  have : N.Normal := by
    constructor
    rintro f ⟨x, rfl⟩ a
    refine ⟨a x, ?_⟩
    ext y
    simp [MulAut.conj_apply]
  let f := QuotientGroup.mk' N
  have hcard : Nat.card (MulAut G ⧸ N) = 6 :=
    N.index_eq_card.symm.trans (index_range_conj_of_equiv model)
  have hd : orderOf (f e) ∣ 6 := hcard ▸ orderOf_dvd_natCard (f e)
  have hp : orderOf (f e) ∣ 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, he, map_one]
  have hc : Nat.Coprime (orderOf (f e)) 3 :=
    ((show Nat.Coprime 2 3 by decide).pow_left n).of_dvd_left hp
  have hs : (f e) ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_right hd)
  have hm : e ^ 2 ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact (f.map_pow e 2).trans hs
  obtain ⟨q, hq⟩ := hm
  exact ⟨q, hq.symm⟩

end QuaternionGroup
