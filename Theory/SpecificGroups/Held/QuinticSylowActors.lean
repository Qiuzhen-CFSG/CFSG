module
public import Theory.GroupTheory.SolvableSylowOvergroups.OrderActors
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups
public import Theory.SpecificGroups.Held.ComponentFacts

/-!
# Quintic actors on a normal Held group

The native graph calculation proves that a subgroup of Held containing a
full Sylow two-subgroup and of order prime to three is that Sylow subgroup.
Transport through the actual conjugation action excludes a faithful
order-five actor with an actor-Sylow join supported at two and five.

Source: Aschbacher–Smith 6.1.4; native Held graph and Sylow geometry from
GLS3 Table 5.3p and the checked ATLAS HeG1-p2058B0 carrier.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Held.QuinticSylowActors
variable {G : Type*} [Group G] [Finite G]

/-- The actual full-Sylow order bound excludes a faithful quintic actor
on a normal copy of Held. -/
theorem no_five_actor (K E : Subgroup G) [K.Normal] (S : Sylow 2 G) {a : ℕ}
    (hm : Nonempty (K ≃* He))
    (hE : Nat.card E = 5) (hd : Disjoint E (centralizer (K : Set G)))
    (hc : Nat.card (E ⊔ (S : Subgroup G) : Subgroup G) ∣ 2^a * 5) : False := by
  obtain ⟨e⟩ := hm
  have hzK : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center He at hh
    rw [LocalPairs.center_eq_bot,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  apply no_odd_actor_of_sylow_order_bound K E S (by decide : Odd 5) hzK
    (outer_isPGroup_two.of_equiv (MulAut.outerCongr e).symm) _ hE hd hc
  intro P J hJ hPJ
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let J' := J.map e.toMonoidHom
  have hthree : ¬3 ∣ Nat.card J' := by
    rw [card_map_of_injective e.injective]
    exact Nat.prime_three.coprime_iff_not_dvd.mp
      ((((by decide : Nat.Coprime 3 2).pow_right a).mul_right (by decide)).of_dvd_right hJ)
  have he := LocalPairs.SylowGeometry.ThreePrimeOvergroups.overgroup_eq P' J'
    (map_mono hPJ) hthree
  intro hfive
  have hfive' : 5 ∣ Nat.card J' := by rwa [card_map_of_injective e.injective]
  rw [he] at hfive'
  obtain ⟨n,hn⟩ := P'.isPGroup'.exists_card_eq
  rw [hn] at hfive'
  exact (by decide : ¬5 ∣ 2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hfive')

end Held.QuinticSylowActors
