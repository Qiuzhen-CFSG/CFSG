module
public import Theory.GroupTheory.SylowLayerNormalizerDivisor
public import Theory.SpecificGroups.SL2.SylowNormalizerCard
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.SpecificGroups.SL2.PairSylowNormalizer
public import Theory.GroupTheory.Hall.TwoClosedNormal
/-!
# Single and paired Borel divisors in proper Sylow overgroups

A normal SL2 layer contributes q(q-1), and a normal paired layer contributes
(q-1)^2, to any subgroup containing every proper overgroup of the prescribed
Sylow. We normalize the Sylow intersection with the layer, retaining possible
field automorphisms and a factor exchanger. In particular a field-sixteen
single layer is incompatible with an odd Hall three-group, while a paired
field-four layer forces nine to divide that Hall order.

Source: Aschbacher--Smith 10.2.3(4), printed p.746.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {G Q F : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
  [Field F] [Finite F] [CharP F 2]
set_option backward.isDefEq.respectTransparency false

theorem normal_layer_borel_card_dvd_of_proper_overgroups
    (S : Sylow 2 G) (q : G →* Q) (hq : Function.Surjective q)
    (L : Subgroup Q) [L.Normal] (e : L ≃* SL(2,F))
    (M : Subgroup G)
    (hM : ∀ J : Subgroup G, (S : Subgroup G) ≤ J → J ≠ ⊤ → J ≤ M) :
    Nat.card F * (Nat.card F - 1) ∣ Nat.card M := by
  obtain ⟨P,hP⟩ := (S.mapSurjective hq).exists_sylow_map_eq_inf_of_normal L
  have hd := layer_sylow_normalizer_card_dvd_of_proper_overgroups S q hq L P hP
    (sylow_normalizer_ne_top_of_surjective e.toMonoidHom e.surjective P) M hM
  have hcard : Nat.card (normalizer ((P : Subgroup L) : Set L)) = Nat.card F * (Nat.card F - 1) := by
    rw [←card_map_of_injective (K := normalizer ((P : Subgroup L) : Set L)) (f := e.toMonoidHom) e.injective,
      map_normalizer_eq_of_bijective (P : Subgroup L) (f := e.toMonoidHom) e.bijective]
    exact card_sylow_normalizer_even (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  rw [←hcard]
  simpa only [Sylow.coe_coe] using hd

theorem normal_pair_borel_odd_square_dvd_of_proper_overgroups
    (S : Sylow 2 G) (q : G →* Q) (hq : Function.Surjective q)
    (L : Subgroup Q) [L.Normal] (e : L ≃* (SL(2,F) × SL(2,F)))
    (M : Subgroup G)
    (hM : ∀ J : Subgroup G, (S : Subgroup G) ≤ J → J ≠ ⊤ → J ≤ M) :
    (Nat.card F - 1)^2 ∣ Nat.card M := by
  obtain ⟨P,hP⟩ := (S.mapSurjective hq).exists_sylow_map_eq_inf_of_normal L
  let r := (MonoidHom.fst SL(2,F) SL(2,F)).comp e.toMonoidHom
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨a,ha⟩ := e.surjective (x,1)
    exact ⟨a,congrArg Prod.fst ha⟩
  have hd := layer_sylow_normalizer_card_dvd_of_proper_overgroups S q hq L P hP
    (sylow_normalizer_ne_top_of_surjective r hr P) M hM
  have hodd := odd_square_dvd_card_pair_sylow_normalizer
    (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hcard := card_map_of_injective (K := normalizer ((P : Subgroup L) : Set L))
    (f := e.toMonoidHom) e.injective
  rw [map_normalizer_eq_of_bijective (P : Subgroup L) (f := e.toMonoidHom) e.bijective] at hcard
  have hodd' : (Nat.card F - 1)^2 ∣ Nat.card
      (normalizer (((P : Subgroup L).map e.toMonoidHom) : Set (SL(2,F) × SL(2,F)))) := by
    simpa only [Sylow.coe_mapSurjective] using hodd
  rw [hcard] at hodd'
  exact hodd'.trans (by simpa only [Sylow.coe_coe] using hd)

end Matrix.SpecialLinearGroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem five_not_dvd_card_of_odd_three_hall
    (B : Subgroup G) (hHall : IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} B)
    (hB : IsPGroup 3 B) : ¬ 5 ∣ Nat.card G := by
  intro hd
  rw [←B.index_mul_card] at hd
  rcases (by decide : Nat.Prime 5).dvd_mul.mp hd with hi | hc
  · exact hHall.p_in_pi_of_p_dvd_index ⟨5,by decide⟩ hi (show (5:ℕ) ≠ 2 by decide)
  · obtain ⟨k,hk⟩ := hB.exists_card_eq
    rw [hk] at hc
    exact (by decide : ¬ 5 ∣ 3) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hc)

omit [Finite G] in
theorem nine_dvd_odd_hall_card_of_dvd_card
    (B : Subgroup G) (hHall : IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} B)
    (h9 : 9 ∣ Nat.card G) : 9 ∣ Nat.card B := by
  have hc : Nat.Coprime 9 B.index := by
    have hn : ¬ 3 ∣ B.index := fun hi => hHall.p_in_pi_of_p_dvd_index ⟨3,by decide⟩ hi
      (show (3:ℕ) ≠ 2 by decide)
    have hh := ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr hn).pow_left 2
    norm_num at hh
    exact hh
  rw [←B.index_mul_card] at h9
  exact hc.dvd_of_dvd_mul_left h9
end Subgroup
