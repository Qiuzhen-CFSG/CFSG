module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.OddCore.FiveCentralizer.CoreCalculation
public import GorensteinWalter.BrauerSuzukiWallCardTwoOrderCases

/-!
# Recognition of Held's five-element centralizer quotient

A finite group with central odd core of order five, one class of involutions,
and an involution centralizer of order twenty and exponent dividing ten has
order not divisible by nine. Involutions lift uniquely through the central
five-subgroup. Their quotient centralizers are four-groups, so the order-two
case of Brauer–Suzuki–Wall gives quotient order twelve or sixty.

The final theorem applies this argument to the literal centralizer of an
order-five element in Held's marked A6. The intersection order, centralizer
exponent and involution fusion remain explicit local premises; the odd-core
calculation supplies all other inputs.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.3, printed p.236.
The lifting and four-group arguments adapt the central-order-three proofs in
M22Identification/OrderRecognition/LocalAnalysis/ThreeLocal/FusionSylow/
CentralizerControl/QuotientRecognition.lean.
-/

open Subgroup
open scoped Pointwise

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.OddCore.FiveCentralizer

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

private theorem four_centralizer_order_cases {A : Type*} [Group A] [Finite A]
    (t : A) (ht : orderOf t = 2)
    (hcard : Nat.card (centralizer ({t} : Set A)) = 4)
    (hpow : ∀ x : centralizer ({t} : Set A), x ^ 2 = 1)
    (hfusion : ∀ x : A, orderOf x = 2 → IsConj x t) :
    Nat.card A = 12 ∨ Nat.card A = 60 := by
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
  exact h.card_eq_twelve_or_sixty_of_card_K_eq_two hTcard

/-- The order formula for the image of a subgroup containing the kernel. -/
private theorem card_map_mul_kernel {A B : Type*} [Group A] [Group B]
    (f : A →* B) (U : Subgroup A) (hker : f.ker ≤ U) :
    Nat.card (U.map f) * Nat.card f.ker = Nat.card U := by
  have h := (f.ker.subgroupOf U).index_mul_card
  change f.ker.relIndex U * Nat.card (f.ker.subgroupOf U) = Nat.card U at h
  rw [relIndex_ker, Nat.card_congr (subgroupOfEquivOfLe hker).toEquiv] at h
  exact h

private theorem central_fifth_power {A : Type*} [Group A]
    (K : Subgroup A) (hK : Nat.card K = 5) (x : A) (hx : x ∈ K) :
    x ^ 5 = 1 := by
  have hh := pow_card_eq_one' (x := (⟨x, hx⟩ : K))
  rw [hK] at hh
  exact congrArg Subtype.val hh

private theorem involution_lift_central_five {A : Type*} [Group A]
    (K : Subgroup A) [K.Normal] (hK : Nat.card K = 5)
    (b : A ⧸ K) (hb : orderOf b = 2) :
    ∃ a : A, orderOf a = 2 ∧ QuotientGroup.mk' K a = b := by
  let q := QuotientGroup.mk' K
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective K b
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  have ha2 : a ^ 2 ∈ K := (QuotientGroup.eq_one_iff _).mp (by
    change q (a ^ 2) = 1
    rw [map_pow, ha, hb2])
  have ha10 : a ^ 10 = 1 := by simpa only [← pow_mul] using central_fifth_power K hK (a ^ 2) ha2
  have ha5q : q (a ^ 5) = b := by
    rw [map_pow, ha, show 5 = 2 * 2 + 1 by rfl, pow_succ, pow_mul, hb2, one_pow, one_mul]
  refine ⟨a ^ 5, orderOf_eq_prime (by simpa only [← pow_mul] using ha10) ?_, ha5q⟩
  intro hh
  have hb1 : b = 1 := by rw [← ha5q, hh, map_one]
  simp [hb1] at hb

private theorem involution_eq_of_central_five {A : Type*} [Group A]
    (K : Subgroup A) [K.Normal] (hKZ : K ≤ center A) (hK : Nat.card K = 5)
    (a b : A) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : QuotientGroup.mk' K a = QuotientGroup.mk' K b) : a = b := by
  let d := a / b
  have hdZ : d ∈ K := QuotientGroup.eq_iff_div_mem.mp hab
  have hd5 : d ^ 5 = 1 := central_fifth_power K hK d hdZ
  have hdb : Commute d b := (mem_center_iff.mp (hKZ hdZ) b).symm
  have habc : Commute a b := by
    simpa [d, div_eq_mul_inv, mul_assoc] using hdb.mul_left (Commute.refl b)
  have hd2 : d ^ 2 = 1 := by
    change (a / b) ^ 2 = 1
    rw [div_eq_mul_inv, (habc.inv_right).mul_pow, ha, inv_pow, hb]
    simp
  have hd1 : d = 1 := by
    have hh := hd5
    rw [show 5 = 2 * 2 + 1 by rfl, pow_succ, pow_mul, hd2, one_pow, one_mul] at hh
    exact hh
  exact div_eq_one.mp hd1

private theorem centralizer_comap_central_five {A : Type*} [Group A]
    (K : Subgroup A) [K.Normal] (hKZ : K ≤ center A) (hK : Nat.card K = 5)
    (t : A) (ht : orderOf t = 2) :
    (centralizer ({QuotientGroup.mk' K t} : Set (A ⧸ K))).comap
      (QuotientGroup.mk' K) = centralizer ({t} : Set A) := by
  let q := QuotientGroup.mk' K
  ext a
  simp only [mem_comap, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hc : a * t * a⁻¹ = t := by
      apply involution_eq_of_central_five K hKZ hK
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
    (K : Subgroup A) [K.Normal] (hKZ : K ≤ center A) (hK : Nat.card K = 5)
    (t : A) (ht : orderOf t = 2)
    (hc : Nat.card (centralizer ({t} : Set A)) = 20)
    (hp : ∀ x : centralizer ({t} : Set A), x ^ 10 = 1)
    (hf : ∀ x : A, orderOf x = 2 → IsConj x t) :
    orderOf (QuotientGroup.mk' K t) = 2 ∧
    Nat.card (centralizer ({QuotientGroup.mk' K t} : Set (A ⧸ K))) = 4 ∧
    (∀ x : centralizer ({QuotientGroup.mk' K t} : Set (A ⧸ K)), x ^ 2 = 1) ∧
    (∀ x : A ⧸ K, orderOf x = 2 → IsConj x (QuotientGroup.mk' K t)) := by
  let q := QuotientGroup.mk' K
  let C := centralizer ({t} : Set A)
  let B := centralizer ({q t} : Set (A ⧸ K))
  have hBC : B.comap q = C := centralizer_comap_central_five K hKZ hK t ht
  have hCB : C.map q = B := by
    rw [← hBC, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hker : q.ker ≤ C := by
    rw [QuotientGroup.ker_mk']
    exact hKZ.trans (center_le_centralizer _)
  have hBcard : Nat.card B = 4 := by
    have hh := card_map_mul_kernel q C hker
    rw [hCB, QuotientGroup.ker_mk', hK, hc] at hh
    omega
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htq2 : orderOf (q t) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ht2, map_one]
    · intro heq
      have hh := involution_eq_of_central_five K hKZ hK t 1 ht2 (by simp) (by
        simpa only [map_one] using heq)
      simp [hh] at ht
  refine ⟨htq2, hBcard, ?_, ?_⟩
  · intro x
    have hxB : (x : A ⧸ K) ∈ C.map q := by rw [hCB]; exact x.property
    obtain ⟨y, hy, hyx⟩ := mem_map.mp hxB
    have hx10 : x ^ 10 = 1 := by
      apply Subtype.ext
      change (x : A ⧸ K) ^ 10 = 1
      rw [← hyx, ← map_pow]
      have hh : y ^ 10 = 1 := congrArg Subtype.val (hp ⟨y, hy⟩)
      rw [hh, map_one]
    have hd4 : orderOf x ∣ 4 := by
      have hh := orderOf_dvd_natCard x
      change orderOf x ∣ Nat.card B at hh
      rwa [hBcard] at hh
    have hd10 := orderOf_dvd_of_pow_eq_one hx10
    exact orderOf_dvd_iff_pow_eq_one.mp (show orderOf x ∣ 2 from Nat.dvd_gcd hd4 hd10)
  · intro x hx
    obtain ⟨a, ha, haq⟩ := involution_lift_central_five K hK x hx
    obtain ⟨g, hg⟩ := isConj_iff.mp (hf a ha)
    refine isConj_iff.mpr ⟨q g, ?_⟩
    rw [← haq]
    simpa only [map_mul, map_inv] using congrArg q hg

/-- The central odd-core and involution-centralizer hypotheses exclude a
factor nine in the ambient order. No simplicity or model identification is
assumed. -/
public theorem not_nine_dvd_card_of_central_oddCore
    {H : Type*} [Group H] [Finite H]
    (hKZ : pPrimeCore 2 H ≤ center H) (hK : Nat.card (pPrimeCore 2 H) = 5)
    (t : H) (ht : orderOf t = 2)
    (hc : Nat.card (centralizer ({t} : Set H)) = 20)
    (hp : ∀ x : centralizer ({t} : Set H), x ^ 10 = 1)
    (hf : ∀ x : H, orderOf x = 2 → IsConj x t) :
    ¬ 9 ∣ Nat.card H := by
  let K := pPrimeCore 2 H
  obtain ⟨hqt, hqc, hqp, hqf⟩ := quotient_involution_data K hKZ hK t ht hc hp hf
  have hcases := four_centralizer_order_cases (QuotientGroup.mk' K t) hqt hqc hqp hqf
  have hcard := card_eq_card_quotient_mul_card_subgroup K
  rcases hcases with h12 | h60
  · rw [h12, hK] at hcard
    rw [hcard]
    decide
  · rw [h60, hK] at hcard
    rw [hcard]
    decide

/-- The three local premises in Held's Lemma 5.3 imply that nine does not
divide the order of the actual five-element centralizer. The odd-core
hypotheses are discharged by the marked four-group calculation. -/
public theorem not_nine_dvd_card_of_intersection_card
    {G : Type*} [Group G] [Finite G] (D : LocalData G)
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
    (L : Source.SixLocalData D e) (w : G) (hwA : w ∈ L.A) (hw : orderOf w = 5)
    (h20 : Nat.card (centralizer ({mu D e} : Set G) ⊓ ambient w : Subgroup G) = 20)
    (hp : ∀ x : centralizer ({first D e L w hwA} : Set (ambient w)), x ^ 10 = 1)
    (hf : ∀ x : ambient w, orderOf x = 2 → IsConj x (first D e L w hwA)) :
    ¬ 9 ∣ Nat.card (ambient w) := by
  apply not_nine_dvd_card_of_central_oddCore
    (t := first D e L w hwA)
  · rw [oddCore_eq_kernel_of_intersection_card D e L w hwA hw h20]
    exact kernel_le_center w
  · exact oddCore_card_of_intersection_card D e L w hwA hw h20
  · exact first_order D e L w hwA
  · exact (Nat.card_congr (firstCentralizerEquiv D e L w hwA).toEquiv).trans h20
  · exact hp
  · exact hf

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.OddCore.FiveCentralizer
