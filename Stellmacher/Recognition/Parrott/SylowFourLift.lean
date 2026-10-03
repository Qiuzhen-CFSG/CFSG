module

public import Stellmacher.Recognition.Parrott.OuterInvolutionClasses

/-!
# Splitting order-four lifts in the five-normalizer

An outer involution in H = C_G(z) forces every order-four element of H/J
(where J = O₂(H)) to have an order-four lift. Work in the normalizer of a
Sylow-five subgroup. It surjects onto H/J with kernel contained in Z(J)=⟨z⟩.
Conjugate the outer involution so its quotient image is the square of the
prescribed quotient generator. The two lifts of that square differ by z;
squaring then proves that the generator's fourth power is one.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.674, final paragraph, and pp.677–678, Lemma 6 and equation (1).
-/

open Subgroup
open scoped commutatorElement
namespace Stellmacher.Recognition

private theorem normalizer_surjects
    {G : Type*} [Group G] [Finite G] (z : G)
    (h : ParrottCentralizerHypotheses z)
    (P : Sylow 5 (centralizer ({z} : Set G))) :
    (normalizer (P : Set (centralizer ({z} : Set G)))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) = ⊤ := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let q := QuotientGroup.mk' J
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective J)
  have hQcard : Nat.card (H ⧸ J) = 20 := by
    obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
    calc
      _ = Nat.card (SemidirectProduct (Multiplicative (ZMod 5))
        (Multiplicative (ZMod 4)) φ) := Nat.card_congr e.toEquiv
      _ = 20 := by rw [SemidirectProduct.card]; norm_num
  have hQc : Nat.card Q = 5 := by
    rw [Q.card_eq_multiplicity, hQcard]
    decide +kernel
  have hQi : Q.index = 4 := by
    have hh := Q.index_mul_card
    rw [hQc, hQcard] at hh
    omega
  have hcount : Nat.card (Sylow 5 (H ⧸ J)) = 1 := by
    have hdiv := Q.card_dvd_index
    rw [hQi] at hdiv
    have hle := Nat.le_of_dvd (by decide : 0 < 4) hdiv
    have hmod := card_sylow_modEq_one 5 (H ⧸ J)
    unfold Nat.ModEq at hmod
    omega
  let : Subsingleton (Sylow 5 (H ⧸ J)) :=
    (Nat.card_eq_one_iff_unique.mp hcount).1
  let : (Q : Subgroup (H ⧸ J)).Normal := Q.normal_of_subsingleton
  let : Fact (IsPGroup 5 (P : Subgroup H)) := ⟨P.isPGroup'⟩
  have hnorm : (normalizer (P : Set H)).map q = ⊤ := by
    change (normalizer ((P : Subgroup H) : Set H)).map (QuotientGroup.mk' J) = ⊤
    rw [← normalizer_map_quotient_eq_map_normalizer 5 (P : Subgroup H) J
      inferInstance (by rw [h.core_card]; decide)]
    change normalizer (Q : Set (H ⧸ J)) = ⊤
    exact normalizer_eq_top (H := (Q : Subgroup (H ⧸ J)))
  exact hnorm


private theorem normalizer_core_mem_zpowers
    {G : Type*} [Group G] [Finite G] (z : G)
    (h : ParrottCentralizerHypotheses z)
    (P : Sylow 5 (centralizer ({z} : Set G)))
    (hP : (centralizer (P : Set (centralizer ({z} : Set G)))).subgroupOf
      (pCore 2 (centralizer ({z} : Set G))) ≤
      center (pCore 2 (centralizer ({z} : Set G))))
    (d : centralizer ({z} : Set G))
    (hdN : d ∈ normalizer (P : Set (centralizer ({z} : Set G))))
    (hdJ : d ∈ pCore 2 (centralizer ({z} : Set G))) :
    (d : G) ∈ zpowers z := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hdis : Disjoint J (P : Subgroup H) :=
    IsPGroup.disjoint_of_ne 2 5 (by decide) _ _ pCore_isPGroup P.isPGroup'
  have hdC : d ∈ centralizer (P : Set H) := by
    intro p hp
    have hcJ : ⁅d, p⁆ ∈ J := commutator_le_left J (⊤ : Subgroup H)
      (commutator_mem_commutator hdJ (mem_top p))
    have hcP : ⁅d, p⁆ ∈ (P : Subgroup H) :=
      P.mul_mem ((mem_normalizer_iff.mp hdN p).mp hp) (P.inv_mem hp)
    have hone : ⁅d, p⁆ = 1 := (disjoint_def.mp hdis) hcJ hcP
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
  rw [← (parrott_centralizer_structure z h).1]
  exact mem_map_of_mem (H.subtype.comp J.subtype)
    (hP hdC : (⟨d, hdJ⟩ : J) ∈ center J)

/-- An outer involution eliminates the order-eight obstruction: every
prescribed order-four quotient element has a lift of fourth power one. -/
public theorem parrott_quotient_exists_lift_fourth_power_eq_one
    {G : Type*} [Group G] [Finite G] (z : G)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    (∃ u : H, u ∉ J ∧ orderOf u = 2) →
    ∀ v : H ⧸ J, orderOf v = 4 →
      ∃ x : H, QuotientGroup.mk' J x = v ∧ x ^ 4 = 1 := by
  intro H J hu v hv
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q := QuotientGroup.mk' J
  obtain ⟨P, hP⟩ := h.five_centralizer
  let N := normalizer (P : Set H)
  have hsurj : N.map q = ⊤ := normalizer_surjects z h P
  obtain ⟨x, hxN, hx⟩ := hsurj.symm ▸ mem_top v
  obtain ⟨u, huJ, hu2⟩ := hu
  obtain ⟨a, haN⟩ := parrott_outer_involution_conjugate_into_five_normalizer
    z h P u huJ hu2
  let y := a * u * a⁻¹
  have hy2 : orderOf y = 2 := (MulAut.conj a).orderOf_eq u |>.trans hu2
  have hyJ : y ∉ J := by
    intro hy
    have hh := (inferInstance : J.Normal).conj_mem _ hy a⁻¹
    exact huJ (by simpa [y, mul_assoc] using hh)
  have hyq : orderOf (q y) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, show y ^ 2 = 1 from hy2 ▸ pow_orderOf_eq_one y, map_one]
    · exact fun hh => hyJ ((QuotientGroup.eq_one_iff _).mp hh)
  have hv2 : orderOf (v ^ 2) = 2 := by rw [orderOf_pow, hv]; decide
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  obtain ⟨b, hb⟩ := faithful_five_four_involutions_conjugate φ hφ
    (e (v ^ 2)) (e (q y)) ((e.orderOf_eq _).trans hv2)
    ((e.orderOf_eq _).trans hyq)
  obtain ⟨c, hcN, hc⟩ := hsurj.symm ▸ mem_top (e.symm b)
  let k := c * y * c⁻¹
  have hk2 : k ^ 2 = 1 := by
    have hh := (MulAut.conj c).orderOf_eq y |>.trans hy2
    exact hh ▸ pow_orderOf_eq_one k
  have hkN : k ∈ N := N.mul_mem (N.mul_mem hcN haN) (N.inv_mem hcN)
  have hkq : q k = v ^ 2 := by
    apply e.injective
    change e (q (c * y * c⁻¹)) = e (v ^ 2)
    simpa only [map_mul, map_inv, hc, e.apply_symm_apply] using hb
  let d := (x ^ 2)⁻¹ * k
  have hdN : d ∈ N := N.mul_mem (N.inv_mem (N.pow_mem hxN 2)) hkN
  have hdJ : d ∈ J := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((x ^ 2)⁻¹ * k) = 1
    rw [map_mul, map_inv, map_pow, hx, hkq, inv_mul_cancel]
  have hdZ := normalizer_core_mem_zpowers z h P hP d hdN hdJ
  have hd2 : (d : G) ^ 2 = 1 := by
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hdZ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      show z ^ 2 = 1 from h.involution ▸ pow_orderOf_eq_one z, one_zpow]
  have hdC : Commute (x : G) (d : G) := by
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hdZ
    rw [← hm]
    exact (show Commute (x : G) z from
      mem_centralizer_singleton_iff.mp x.property).zpow_right m
  refine ⟨x, hx, ?_⟩
  apply H.subtype_injective
  have heq : (k : G) = (x : G) ^ 2 * (d : G) := by
    change (k : G) = (x : G) ^ 2 * (((x : G) ^ 2)⁻¹ * (k : G))
    group
  have hk2G := congrArg H.subtype hk2
  simp only [map_pow, map_one] at hk2G
  change (k : G) ^ 2 = 1 at hk2G
  change (x : G) ^ 4 = 1
  rw [heq, (hdC.pow_left 2).mul_pow, hd2, mul_one, ← pow_mul] at hk2G
  exact hk2G

end Stellmacher.Recognition
