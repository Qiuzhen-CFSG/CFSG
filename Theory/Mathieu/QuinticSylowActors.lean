module
public import Theory.GroupTheory.SolvableSylowOvergroups.OrderActors
public import Theory.Mathieu.M22.Properties.QuinticSylowOvergroups
public import Theory.Mathieu.M23.Properties.QuinticSylowOvergroups
public import Theory.Mathieu.M24.Properties.QuinticSylowOvergroups
public import Theory.Mathieu.M22.TripleCover.ScalarAutomorphisms
public import Theory.Mathieu.M23.Properties.OuterRestriction
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms

/-!
# Quintic actors on the three larger Mathieu groups

An actor whose join with a full Sylow has order dividing 2^a times five
is detected in the inner automorphism group of the normal Mathieu factor.
The native Sylow-overgroup order theorems for M₂₂, M₂₃ and M₂₄ exclude
that inner image. The original action kernel remains the centralizer of
the normal subgroup; the ambient action need not be faithful.

Source: Aschbacher–Smith 5.2.2, pp.648–649; native Mathieu Sylow geometry
from GLS3 Table 5.3c–e. All model isomorphisms and two-core kernels are
retained by the Chapter6 consumer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.QuinticSylowActors

private theorem three_free {c a : ℕ} (hc : c ∣ 2^a * 5) : ¬3 ∣ c :=
  Nat.prime_three.coprime_iff_not_dvd.mp
    ((((by decide : Nat.Coprime 3 2).pow_right a).mul_right (by decide)).of_dvd_right hc)

private theorem eleven_free {c a : ℕ} (hc : c ∣ 2^a * 5) : ¬11 ∣ c :=
  (by decide : Nat.Prime 11).coprime_iff_not_dvd.mp
    ((((by decide : Nat.Coprime 11 2).pow_right a).mul_right (by decide)).of_dvd_right hc)

variable {G : Type*} [Group G] [Finite G]

private theorem transport {M : Type*} [Group M] [Finite M]
    (K E : Subgroup G) [K.Normal] (S : Sylow 2 G) {a : ℕ}
    (e : K ≃* M) (hz : center M = ⊥) (hout : IsPGroup 2 (MulAut.Outer M))
    (hbound : ∀ (P : Sylow 2 M) (J : Subgroup M),
      Nat.card J ∣ 2^a * 5 → (P : Subgroup M) ≤ J → ¬5 ∣ Nat.card J)
    (hE : Nat.card E = 5) (hd : Disjoint E (centralizer (K : Set G)))
    (hc : Nat.card (E ⊔ (S : Subgroup G) : Subgroup G) ∣ 2^a * 5) : False := by
  have hzK : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center M at hh
    rw [hz,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  apply no_odd_actor_of_sylow_order_bound K E S (by decide : Odd 5) hzK
    (hout.of_equiv (MulAut.outerCongr e).symm) _ hE hd hc
  intro P J hJ hPJ
  have hh := hbound (P.mapSurjective e.surjective) (J.map e.toMonoidHom)
    (by rwa [card_map_of_injective e.injective]) (map_mono hPJ)
  rwa [card_map_of_injective e.injective] at hh

/-- The native M₂₂, M₂₃ and M₂₄ Sylow overgroups exclude a faithful quintic
actor when the actual actor-Sylow join has only two and five in its order. -/
theorem no_five_actor (K E : Subgroup G) [K.Normal] (S : Sylow 2 G) {a : ℕ}
    (hm : Nonempty (K ≃* M22) ∨ Nonempty (K ≃* M23) ∨ Nonempty (K ≃* M24))
    (hE : Nat.card E = 5) (hd : Disjoint E (centralizer (K : Set G)))
    (hc : Nat.card (E ⊔ (S : Subgroup G) : Subgroup G) ∣ 2^a * 5) : False := by
  rcases hm with e | e | e
  · apply transport K E S e.some m22_center_eq_bot
      (IsPGroup.of_card_dvd_pow (n := 1) (by
        simpa only [pow_one] using M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two))
      _ hE hd hc
    intro P J hJ hPJ
    rw [M22QuinticSylow.card_eq_128 P J hPJ (three_free hJ) (eleven_free hJ)]
    decide
  · apply transport K E S e.some M23Geometry.m23_center_eq_bot m23_outer_isTwoGroup _ hE hd hc
    intro P J hJ hPJ
    exact M23QuinticSylow.not_five_of_two_five_sylow_overgroup P J hPJ a 1
      (by simpa only [pow_one] using hJ)
  · apply transport K E S e.some M24InvolutionCentralizers.center_eq_bot
      M24OuterRestriction.outer_isPGroup_two _ hE hd hc
    intro P J hJ hPJ
    rw [M24QuinticSylow.card_eq_1024 P J hPJ (three_free hJ)]
    decide

end Sporadic.Mathieu.QuinticSylowActors
