module
public import Theory.GroupTheory.SolvableSylowOvergroups.OrderActors
public import Theory.Mathieu.M12.SylowOvergroups.RankTwoCoverage
public import Theory.Mathieu.M12.ValueBoundParabolics.Supplement
public import Theory.Mathieu.M12.Properties.AutCover

/-!
# Quintic actors on a normal M₁₂

The actual actor-Sylow join has order dividing a power of two times five.
Its inner image contains a full Sylow of M₁₂ and has the same order bound.
It is proper because its order is prime to three. The native complete
Sylow-overgroup calculation then bounds its order by 192, excluding five.

Source: the final classifier exclusions in Aschbacher–Smith 6.1.4;
the native M₁₂ Sylow geometry is GLS3 Table 5.3b, implemented in
`SylowOvergroups.RankTwoCoverage`. The original actor and action kernel
are retained throughout the odd-actor transport.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M12QuinticSylowActors

private theorem native_bound (P : Sylow 2 M12) (J : Subgroup M12) {a : ℕ}
    (hc : Nat.card J ∣ 2^a * 5) (hPJ : (P : Subgroup M12) ≤ J) :
    ¬5 ∣ Nat.card J := by
  have hthree : ¬3 ∣ Nat.card J :=
    Nat.prime_three.coprime_iff_not_dvd.mp
      ((((by decide : Nat.Coprime 3 2).pow_right a).mul_right (by decide)).of_dvd_right hc)
  have hproper : J ≠ ⊤ := by
    intro he
    rw [he, card_top, m12_order] at hthree
    exact hthree (by decide)
  exact fun hfive => (by decide : ¬5 ∣ 192)
    (hfive.trans (M12SmallPair.SylowOvergroups.card_dvd_192_of_ne_top J hproper ⟨P,hPJ⟩))

variable {G : Type*} [Group G] [Finite G]

/-- A faithful order-five actor on a normal M₁₂ cannot have a join with
a full Sylow two-subgroup of order dividing a power of two times five. -/
theorem no_five_actor (K E : Subgroup G) [K.Normal] (S : Sylow 2 G) {a : ℕ}
    (hm : Nonempty (K ≃* M12))
    (hE : Nat.card E = 5) (hd : Disjoint E (centralizer (K : Set G)))
    (hc : Nat.card (E ⊔ (S : Subgroup G) : Subgroup G) ∣ 2^a * 5) : False := by
  obtain ⟨e⟩ := hm
  have hzK : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center M12 at hh
    rw [m12_center_eq_bot,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  apply no_odd_actor_of_sylow_order_bound K E S (by decide : Odd 5) hzK
    (M12SmallPair.ValueBoundParabolics.outer_isPGroup_two.of_equiv
      (MulAut.outerCongr e).symm) _ hE hd hc
  intro P J hJ hPJ
  have hh := native_bound (P.mapSurjective e.surjective) (J.map e.toMonoidHom)
    (by rwa [card_map_of_injective e.injective]) (map_mono hPJ)
  rwa [card_map_of_injective e.injective] at hh

end Sporadic.Mathieu.M12QuinticSylowActors
