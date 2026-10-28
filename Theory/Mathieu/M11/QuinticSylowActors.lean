module
public import Theory.GroupTheory.SolvableSylowOvergroups.OrderActors
public import Theory.GroupTheory.TwoPrimeSolvable
public import Theory.GroupTheory.SolvableSmallOddCore
public import Theory.GroupTheory.SolvableSemidihedralInvolution
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.Mathieu.M11.Properties.SylowTwo
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers

/-!
# Quintic actors on a normal M₁₁

A full-Sylow overgroup supported at two and five would have order 80 if
its order were divisible by five. The small odd-core Fitting argument
forces a nontrivial two-core. The native semidihedral Sylow presentation
then gives a characteristic involution. Thus the overgroup lies in its
involution centralizer of order 48, a contradiction.

The ambient actor theorem transports this intrinsic argument through the
actual conjugation action, retaining the supplied Sylow and action kernel.
Source: Aschbacher–Smith 6.1.4; GLS3 Table 5.3a for the checked M₁₁ Sylow
and involution-centralizer structures.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M11QuinticSylowActors

private theorem twoCore_ne_bot (H : Subgroup M11) (hc : Nat.card H = 80) :
    pCore 2 H ≠ ⊥ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hprime (q : ℕ) (hq : q.Prime) (hd : q ∣ Nat.card H) : q = 2 ∨ q = 5 := by
    rw [hc,show 80 = 2^4 * 5 from rfl] at hd
    rcases hq.dvd_mul.mp hd with h2 | h5
    · exact .inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2))
    · exact .inr ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h5)
  have hs := isSolvable_of_prime_dvd_card_eq_two_or_prime H (by decide : Nat.Prime 5) hprime
  let P : Sylow 5 H := Classical.choice inferInstance
  have hP : Nat.card P = 5 := by rw [Sylow.card_eq_multiplicity,hc]; decide +kernel
  have hsmall : Nat.card (pCore 5 H) ≤ 5^1 := by
    have hh := card_le_of_le ((pCore_isPGroup (p := 5) (G := H)).le_sylow_of_normal P)
    simpa only [hP,pow_one] using hh
  apply twoCore_ne_bot_of_solvable_small_odd_core (p := 5) (d := 1) (t := 4)
    (by decide) hs hprime hsmall (by rw [hc]; decide)
  intro n hn
  interval_cases n <;> norm_num [Fin.prod_univ_succ]

private theorem no_order_eighty (P : Sylow 2 M11) (H : Subgroup M11)
    (hPH : (P : Subgroup M11) ≤ H) (hc : Nat.card H = 80) : False := by
  let S := P.subtype hPH
  obtain ⟨T,a,b,ha,hb,hab,hgen⟩ := m11_exists_semidihedral_sylow
  let e : T ≃* S := (T.equiv P).trans (subgroupOfEquivOfLe hPH).symm
  have hagen : closure ({e a,e b} : Set S) = ⊤ := by
    have hh := congrArg (Subgroup.map e.toMonoidHom) hgen
    rw [MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton,
      map_top_of_surjective _ e.surjective] at hh
    exact hh
  have hconj : e b * e a * (e b)⁻¹ = (e a)^3 := by
    rw [← map_inv,← map_mul,← map_mul,hab,map_pow]
  let z : H := (e a : H)^4
  have hz : orderOf z = 2 := by
    rw [orderOf_pow,orderOf_coe,(e.orderOf_eq a).trans ha]
    decide
  let : (zpowers z).Characteristic :=
    Semidihedral.characteristic_zpowers_fourth_of_twoCore_ne_bot S (e a) (e b)
      ((e.orderOf_eq a).trans ha) ((e.orderOf_eq b).trans hb) hconj hagen (twoCore_ne_bot H hc)
  have hzcenter : z ∈ center H := central_of_normal_card_two (zpowers z)
    (by rw [Nat.card_zpowers,hz]) (mem_zpowers z)
  have hHC : H ≤ centralizer ({(z : M11)} : Set M11) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg H.subtype ((mem_center_iff.mp hzcenter) ⟨x,hx⟩)
  have hcard : Nat.card (centralizer ({(z : M11)} : Set M11)) = 48 := by
    rw [card_centralizer_eq_of_isConj _ _
      (m11_involution_isConj_generatorA z ((orderOf_coe z).trans hz))]
    exact m11_involutionCentralizer_card
  have hd := card_dvd_of_le hHC
  rw [hc,hcard] at hd
  norm_num at hd

private theorem native_bound (P : Sylow 2 M11) (H : Subgroup M11) {a : ℕ}
    (hc : Nat.card H ∣ 2^a * 5) (hPH : (P : Subgroup M11) ≤ H) :
    ¬5 ∣ Nat.card H := by
  intro h5
  have hP : Nat.card P = 16 := by rw [Sylow.card_eq_multiplicity,m11_order]; decide +kernel
  have h16 : 16 ∣ Nat.card H := hP ▸ card_dvd_of_le hPH
  have hlo : 80 ∣ Nat.card H :=
    (by decide : Nat.Coprime 16 5).mul_dvd_of_dvd_of_dvd h16 h5
  have hcop : Nat.Coprime 99 (Nat.card H) :=
    ((((by decide : Nat.Coprime 99 2).pow_right a).mul_right (by decide))).of_dvd_right hc
  have hhi : Nat.card H ∣ 80 := by
    have hh := H.card_subgroup_dvd_card
    rw [m11_order,show 7920 = 80 * 99 from rfl] at hh
    exact hcop.symm.dvd_mul_right.mp hh
  exact no_order_eighty P H hPH (Nat.dvd_antisymm hhi hlo)

variable {G : Type*} [Group G] [Finite G]

/-- The actual full-Sylow order bound excludes a faithful quintic actor
on a normal copy of M₁₁. -/
theorem no_five_actor (K E : Subgroup G) [K.Normal] (S : Sylow 2 G) {a : ℕ}
    (hm : Nonempty (K ≃* M11))
    (hE : Nat.card E = 5) (hd : Disjoint E (centralizer (K : Set G)))
    (hc : Nat.card (E ⊔ (S : Subgroup G) : Subgroup G) ∣ 2^a * 5) : False := by
  obtain ⟨e⟩ := hm
  have hzK : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center M11 at hh
    rw [m11_center_eq_bot,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  apply no_odd_actor_of_sylow_order_bound K E S (by decide : Odd 5) hzK
    (m11_outer_isPGroup_two.of_equiv (MulAut.outerCongr e).symm) _ hE hd hc
  intro P J hJ hPJ
  have hh := native_bound (P.mapSurjective e.surjective) (J.map e.toMonoidHom)
    (by rwa [card_map_of_injective e.injective]) (map_mono hPJ)
  rwa [card_map_of_injective e.injective] at hh

end Sporadic.Mathieu.M11QuinticSylowActors
