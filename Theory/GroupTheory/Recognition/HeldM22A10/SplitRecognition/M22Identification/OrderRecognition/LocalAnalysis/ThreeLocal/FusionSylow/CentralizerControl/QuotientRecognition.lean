module

public import GorensteinWalter.BrauerSuzukiWallCardTwoA5

/-!
# A central quotient with four-group involution centralizers

Suppose the center of a finite group has order three, its involutions are
conjugate, and an involution centralizer has order twelve and exponent dividing
six. Its central quotient is isomorphic to A₄ or A₅.

Involutions lift uniquely through the central subgroup of order three.
Consequently their centralizers in the quotient are four-groups. The proved
order-two case of Brauer–Suzuki–Wall then supplies the actual alternating-group
isomorphism. This provides the special consequence needed in Janko's Lemma 8
without invoking the general Suzuki characterization.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 3, pp.7–8. The recognition step uses the
source-faithful Brauer–Suzuki–Wall development in `GorensteinWalter`.
-/

open Subgroup
open scoped Pointwise

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CentralizerControl

private theorem mem_zpowers_two {A : Type*} [Group A] [Finite A]
    (t x : A) (ht : orderOf t = 2) : x ∈ zpowers t ↔ x = 1 ∨ x = t := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ht]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    interval_cases n <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, by simp⟩
    · exact ⟨1, by decide, by simp⟩

private theorem four_recognition {A : Type*} [Group A] [Finite A]
    (t : A) (ht : orderOf t = 2)
    (hcard : Nat.card (centralizer ({t} : Set A)) = 4)
    (hpow : ∀ x : centralizer ({t} : Set A), x ^ 2 = 1)
    (hfusion : ∀ x : A, orderOf x = 2 → IsConj x t) :
    Nonempty (A ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (A ≃* alternatingGroup (Fin 5)) := by
  classical
  let C := centralizer ({t} : Set A)
  let T := zpowers t
  have htC : t ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hTC : T ≤ C := zpowers_le.mpr htC
  have hTcard : Nat.card T = 2 := by simp [T, Nat.card_zpowers, ht]
  have hCT : ¬C ≤ T := by
    intro hh
    have he := le_antisymm hh hTC
    have hc : Nat.card C = 4 := hcard
    rw [he, hTcard] at hc
    omega
  obtain ⟨s, hsC, hsT⟩ := SetLike.not_le_iff_exists.mp hCT
  have hs2 : s ^ 2 = 1 := congrArg Subtype.val (hpow ⟨s, hsC⟩)
  have hsne : s ≠ 1 := fun h => hsT (h ▸ T.one_mem)
  have hjoin : C = T ⊔ zpowers s := by
    apply le_antisymm
    · have hle : T ⊔ zpowers s ≤ C := sup_le hTC (zpowers_le.mpr hsC)
      have hsJ : s ∈ T ⊔ zpowers s := (show zpowers s ≤ T ⊔ zpowers s from le_sup_right) (mem_zpowers s)
      have hJcard : 2 < Nat.card ↥(T ⊔ zpowers s) := by
        have hlt : T < T ⊔ zpowers s := lt_of_le_of_ne le_sup_left (by
          intro h
          exact hsT (h ▸ hsJ))
        have h := Set.ncard_lt_ncard (show (T : Set A) ⊂ (T ⊔ zpowers s : Subgroup A) from hlt) (Set.toFinite _)
        change Nat.card T < Nat.card ↥(T ⊔ zpowers s) at h
        rwa [hTcard] at h
      have hd := card_dvd_of_le hle
      rw [hcard] at hd
      have hh : Nat.card ↥(T ⊔ zpowers s) = 4 := by
        have := Nat.le_of_dvd (by decide : 0 < 4) hd
        have hd2 : Nat.card ↥(T ⊔ zpowers s) ∈ Nat.divisors 4 :=
          Nat.mem_divisors.mpr ⟨hd, by decide⟩
        have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
        rw [hdiv] at hd2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd2
        omega
      exact (eq_of_le_of_card_ge hle (by rw [hcard, hh])).ge
    · exact sup_le hTC (zpowers_le.mpr hsC)
  let h := ({
    t := t
    K := T
    H := C
    s := s
    t_involution := ⟨by intro h; simp [h] at ht, ht ▸ pow_orderOf_eq_one t⟩
    t_mem_K := mem_zpowers t
    H_eq_centralizer := rfl
    K_commutative := inferInstance
    s_involution := ⟨hsne, hs2⟩
    s_not_mem_K := hsT
    H_eq_join := hjoin
    fixed_subgroup_eq := inf_eq_left.mpr (by
      apply zpowers_le.mpr
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hsC).symm)
    s_inverts_K := by
      intro x hx
      rcases (mem_zpowers_two t x ht).mp hx with hx | hx
      · simp [hx]
      · rw [hx]
        rw [mul_inv_eq_iff_eq_mul]
        have hi : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by
          simpa [pow_two, ht] using pow_orderOf_eq_one t)
        rw [hi]
        exact mem_centralizer_singleton_iff.mp hsC
    conjugate_disjoint := by
      intro g hg
      apply Subgroup.disjoint_def.mpr
      intro x hx hxg
      rcases (mem_zpowers_two t x ht).mp hx with hx | hx
      · exact hx
      · rw [hx] at hxg ⊢
        obtain ⟨y, hy, hyx⟩ := mem_map.mp hxg
        rcases (mem_zpowers_two t y ht).mp hy with hy | hy
        · rw [hy] at hyx
          have ht1 : t = 1 := by simpa using hyx.symm
          simp [ht1] at ht
        · rw [hy] at hyx
          exact (hg (mem_centralizer_singleton_iff.mpr
            (mul_inv_eq_iff_eq_mul.mp hyx))).elim
    involutions_conjugate := by
      intro x hx
      exact isConj_iff.mp (hfusion x (orderOf_eq_prime hx.2 hx.1))
    } : GorensteinWalter.BrauerSuzukiWallHypotheses A)
  by_cases hn : normalizer (C : Set A) = ⊤
  · left
    have he := h.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hTcard
    change Nonempty ((normalizer (C : Set A)) ≃* alternatingGroup (Fin 4)) at he
    rw [hn] at he
    exact ⟨topEquiv.symm.trans he.some⟩
  · exact Or.inr (h.mulEquiv_alternatingGroup_five_of_card_K_eq_two_of_normalizer_ne_top hTcard hn)

/-- The order formula for the image of a subgroup containing the kernel. -/
public theorem card_map_mul_kernel {A B : Type*} [Group A] [Group B]
    (f : A →* B) (U : Subgroup A) (hker : f.ker ≤ U) :
    Nat.card (U.map f) * Nat.card f.ker = Nat.card U := by
  have h := (f.ker.subgroupOf U).index_mul_card
  change f.ker.relIndex U * Nat.card (f.ker.subgroupOf U) = Nat.card U at h
  rw [relIndex_ker, Nat.card_congr (subgroupOfEquivOfLe hker).toEquiv] at h
  exact h

private theorem center_cube {A : Type*} [Group A]
    (hz : Nat.card (center A) = 3) (x : A) (hx : x ∈ center A) : x ^ 3 = 1 := by
  have hh := pow_card_eq_one' (x := (⟨x, hx⟩ : center A))
  rw [hz] at hh
  exact congrArg Subtype.val hh

private theorem involution_lift_center_three {A : Type*} [Group A]
    (hz : Nat.card (center A) = 3) (b : A ⧸ center A) (hb : orderOf b = 2) :
    ∃ a : A, orderOf a = 2 ∧ QuotientGroup.mk' (center A) a = b := by
  let q := QuotientGroup.mk' (center A)
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (center A) b
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  have ha2 : a ^ 2 ∈ center A := (QuotientGroup.eq_one_iff _).mp (by
    change q (a ^ 2) = 1
    rw [map_pow, ha, hb2])
  have ha6 : a ^ 6 = 1 := by simpa only [← pow_mul] using center_cube hz (a ^ 2) ha2
  have ha3q : q (a ^ 3) = b := by
    rw [map_pow, ha, show 3 = 2 + 1 by rfl, pow_succ, hb2, one_mul]
  refine ⟨a ^ 3, orderOf_eq_prime (by simpa only [← pow_mul] using ha6) ?_, ha3q⟩
  intro hh
  have hb1 : b = 1 := by rw [← ha3q, hh, map_one]
  simp [hb1] at hb

private theorem involution_eq_of_center_three {A : Type*} [Group A]
    (hz : Nat.card (center A) = 3) (a b : A) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : QuotientGroup.mk' (center A) a = QuotientGroup.mk' (center A) b) : a = b := by
  let d := a / b
  have hdZ : d ∈ center A := QuotientGroup.eq_iff_div_mem.mp hab
  have hd3 : d ^ 3 = 1 := center_cube hz d hdZ
  have hdb : Commute d b := (mem_center_iff.mp hdZ b).symm
  have habc : Commute a b := by
    simpa [d, div_eq_mul_inv, mul_assoc] using hdb.mul_left (Commute.refl b)
  have hd2 : d ^ 2 = 1 := by
    change (a / b) ^ 2 = 1
    rw [div_eq_mul_inv, (habc.inv_right).mul_pow, ha, inv_pow, hb]
    simp
  have hd1 : d = 1 := by
    have hh := hd3
    rw [pow_succ, hd2, one_mul] at hh
    exact hh
  exact div_eq_one.mp hd1

private theorem centralizer_comap_center_three {A : Type*} [Group A]
    (hz : Nat.card (center A) = 3) (t : A) (ht : orderOf t = 2) :
    (centralizer ({QuotientGroup.mk' (center A) t} : Set (A ⧸ center A))).comap
      (QuotientGroup.mk' (center A)) = centralizer ({t} : Set A) := by
  let q := QuotientGroup.mk' (center A)
  ext a
  simp only [mem_comap, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hc : a * t * a⁻¹ = t := by
      apply involution_eq_of_center_three hz
      · change (MulAut.conj a t) ^ 2 = 1
        have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
        rw [← map_pow, ht2, map_one]
      · exact ht ▸ pow_orderOf_eq_one t
      · change q (a * t * a⁻¹) = q t
        rw [map_mul, map_mul, map_inv, h, mul_assoc, mul_inv_cancel, mul_one]
    exact mul_inv_eq_iff_eq_mul.mp hc
  · intro h
    simpa only [map_mul] using congrArg q h

private theorem quotient_involution_data {A : Type*} [Group A] [Finite A]
    (hz : Nat.card (center A) = 3) (t : A) (ht : orderOf t = 2)
    (hc : Nat.card (centralizer ({t} : Set A)) = 12)
    (hp : ∀ x : centralizer ({t} : Set A), x ^ 6 = 1)
    (hf : ∀ x : A, orderOf x = 2 → IsConj x t) :
    orderOf (QuotientGroup.mk' (center A) t) = 2 ∧
    Nat.card (centralizer ({QuotientGroup.mk' (center A) t} : Set (A ⧸ center A))) = 4 ∧
    (∀ x : centralizer ({QuotientGroup.mk' (center A) t} : Set (A ⧸ center A)), x ^ 2 = 1) ∧
    (∀ x : A ⧸ center A, orderOf x = 2 → IsConj x (QuotientGroup.mk' (center A) t)) := by
  let q := QuotientGroup.mk' (center A)
  let C := centralizer ({t} : Set A)
  let B := centralizer ({q t} : Set (A ⧸ center A))
  have hBC : B.comap q = C := centralizer_comap_center_three hz t ht
  have hCB : C.map q = B := by
    rw [← hBC, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hker : q.ker ≤ C := by
    rw [QuotientGroup.ker_mk']
    exact center_le_centralizer _
  have hBcard : Nat.card B = 4 := by
    have hh := card_map_mul_kernel q C hker
    rw [hCB, QuotientGroup.ker_mk', hz, hc] at hh
    omega
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htq2 : orderOf (q t) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ht2, map_one]
    · intro heq
      have hh := involution_eq_of_center_three hz t 1 ht2 (by simp) (by
        simpa only [map_one] using heq)
      simp [hh] at ht
  refine ⟨htq2, hBcard, ?_, ?_⟩
  · intro x
    have hxB : (x : A ⧸ center A) ∈ C.map q := by rw [hCB]; exact x.property
    obtain ⟨y, hy, hyx⟩ := mem_map.mp hxB
    have hx6 : x ^ 6 = 1 := by
      apply Subtype.ext
      change (x : A ⧸ center A) ^ 6 = 1
      rw [← hyx, ← map_pow]
      have hh : y ^ 6 = 1 := congrArg Subtype.val (hp ⟨y, hy⟩)
      rw [hh, map_one]
    have hd4 : orderOf x ∣ 4 := by
      have hh := orderOf_dvd_natCard x
      change orderOf x ∣ Nat.card B at hh
      rwa [hBcard] at hh
    have hd6 := orderOf_dvd_of_pow_eq_one hx6
    exact orderOf_dvd_iff_pow_eq_one.mp (show orderOf x ∣ 2 from Nat.dvd_gcd hd4 hd6)
  · intro x hx
    obtain ⟨a, ha, haq⟩ := involution_lift_center_three hz x hx
    obtain ⟨g, hg⟩ := isConj_iff.mp (hf a ha)
    refine isConj_iff.mpr ⟨q g, ?_⟩
    rw [← haq]
    simpa only [map_mul, map_inv] using congrArg q hg

/-- The involution-centralizer hypotheses identify the actual quotient by the
center with one of the two small alternating groups. -/
public theorem alternating_four_or_five_of_center_three
    {A : Type*} [Group A] [Finite A]
    (hz : Nat.card (center A) = 3) (t : A) (ht : orderOf t = 2)
    (hc : Nat.card (centralizer ({t} : Set A)) = 12)
    (hp : ∀ x : centralizer ({t} : Set A), x ^ 6 = 1)
    (hf : ∀ x : A, orderOf x = 2 → IsConj x t) :
    Nonempty ((A ⧸ center A) ≃* alternatingGroup (Fin 4)) ∨
      Nonempty ((A ⧸ center A) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨hqt, hqc, hqp, hqf⟩ := quotient_involution_data hz t ht hc hp hf
  exact four_recognition (QuotientGroup.mk' (center A) t) hqt hqc hqp hqf

end Theory.GroupTheory.HeldM22A10.M22Identification.CentralizerControl
