module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.ExceptionalNormalizer.Preparation
public import Theory.GroupAction.KleinFourAbelianCardinality
public import Theory.GroupTheory.Involution.Counting

/-!
# Local fusion in the exceptional normalizer action

For an elementary odd centralizer complement A of order 27, the literal
image of N_G(A) in Aut(A) has order divisible by four, elementary Sylow
two-subgroups, and one conjugacy class of involutions.

The normalizing four-group supplies divisibility, and Sylow lifting transports
the ambient exponent-two bound. Every normalizer involution lies in a
four-group. Brauer–Wielandt and the bounds on involution fixed subgroups then
force its fixed subgroup on A to have order three. After conjugating the
involution to z, Sylow conjugacy in C_G(z) moves this fixed subgroup to ⟨x⟩.
The odd-element characterization of A inside C_G(x) shows that the adjusted
conjugator normalizes A. Finally, involutions lift through the odd action
kernel, and their normalizer conjugacy descends to the actual action image.

This supplies the local fusion step in the exceptional branch cited by Bender,
*Finite groups with large subgroups* (1974), proof of (4.1), printed p.225,
from Janko (1966), proof of Lemma 3.1, DOI 10.1016/0021-8693(66)90010-X.
It does not use the automizer classification or the order-27 exclusion.
-/

open Subgroup
open BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)
include h

private theorem two_subgroup_square (B : Subgroup G) (hB : IsPGroup 2 B)
    (y : B) : y ^ 2 = 1 := by
  obtain ⟨S, hS⟩ := hB.exists_le_sylow
  exact Subtype.ext (congrArg (fun w : S => (w : G)) (h.any_sylow_square S ⟨y, hS y.property⟩))

private theorem relative_two_subgroup_square (N : Subgroup G)
    (P : Subgroup N) (hP : IsPGroup 2 P) (y : P) : y ^ 2 = 1 := by
  have hy := h.two_subgroup_square (P.map N.subtype) (hP.map N.subtype)
    ⟨y, mem_map_of_mem _ y.property⟩
  exact Subtype.ext (Subtype.ext (congrArg (fun w : P.map N.subtype => (w : G)) hy))

private theorem four_dvd_normalizer {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A) (hc : Nat.card A = 27)
    [IsSimpleGroup G] (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    4 ∣ Nat.card (normalizer (A : Set G)) := by
  obtain ⟨V, _, hVc, _, hVN, _⟩ :=
    a.exists_normalizing_four_of_card_twentySeven hc p hp hxC hx
  have hd := (V.subgroupOf (normalizer (A : Set G))).card_subgroup_dvd_card
  rwa [Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv, hVc] at hd

private theorem automizer_sylow_elementary (A : Subgroup G)
    (P : Sylow 2 A.normalizerMonoidHom.range) : IsElementaryAbelian 2 P := by
  let f := A.normalizerMonoidHom.rangeRestrict
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective
    A.normalizerMonoidHom.rangeRestrict_surjective 2 P
  have hsq (y : P) : y ^ 2 = 1 := by
    have hy : (y : A.normalizerMonoidHom.range) ∈ (Q : Subgroup _).map f := by
      rw [← Sylow.coe_mapSurjective A.normalizerMonoidHom.rangeRestrict_surjective, hQ]
      exact y.property
    obtain ⟨z, hz, heq⟩ := hy
    have hz2 := h.relative_two_subgroup_square _ Q Q.isPGroup' ⟨z, hz⟩
    apply Subtype.ext
    change (y : A.normalizerMonoidHom.range) ^ 2 = 1
    rw [← heq, ← map_pow, show z ^ 2 = 1 from congrArg Subtype.val hz2, map_one]
  exact {
    toIsMulCommutative := ⟨⟨fun u v =>
      (Commute.of_orderOf_dvd_two (fun y => orderOf_dvd_of_pow_eq_one (hsq y)) u v).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }

private theorem involution_partner (N : Subgroup G) (hN : 4 ∣ Nat.card N)
    (t : N) (ht : orderOf t = 2) :
    ∃ u : N, orderOf u = 2 ∧ orderOf (t * u) = 2 ∧ Commute t u := by
  have htp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht]; rfl)
  obtain ⟨P, hP⟩ := htp.exists_le_sylow
  have htP := hP (mem_zpowers t)
  have hPc : 4 ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos
    (P.pow_dvd_card_of_pow_dvd_card (n := 2) hN)
  have hnle : ¬ (P : Subgroup N) ≤ zpowers t := by
    intro hle
    have := Nat.le_of_dvd Nat.card_pos (card_dvd_of_le hle)
    rw [Nat.card_zpowers, ht] at this
    omega
  obtain ⟨u, huP, hu⟩ := Set.not_subset.mp hnle
  have hsq (v : P) : v ^ 2 = 1 := h.relative_two_subgroup_square N P P.isPGroup' v
  have hu2 : u ^ 2 = 1 := congrArg Subtype.val (hsq ⟨u, huP⟩)
  have htu2 : (t * u) ^ 2 = 1 :=
    congrArg Subtype.val (hsq ⟨t * u, P.mul_mem htP huP⟩)
  have hu1 : u ≠ 1 := by intro he; exact hu (he ▸ (zpowers t).one_mem)
  have htu1 : t * u ≠ 1 := by
    intro he
    have heq : u = t⁻¹ := by
      apply mul_left_cancel (a := t)
      simpa only [mul_inv_cancel] using he
    exact hu (heq ▸ (zpowers t).inv_mem (mem_zpowers t))
  refine ⟨u, orderOf_eq_prime hu2 hu1, orderOf_eq_prime htu2 htu1, ?_⟩
  exact congrArg Subtype.val
    (Commute.of_orderOf_dvd_two (fun v => orderOf_dvd_of_pow_eq_one (hsq v))
      (⟨t, htP⟩ : P) ⟨u, huP⟩).eq

omit h [Finite G] in
private theorem action_fixed_card (A : Subgroup G) (t : normalizer (A : Set G)) :
    Nat.card (A.normalizerMonoidHom t).fixedSubgroup =
      Nat.card (A ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) := by
  have he : (A.normalizerMonoidHom t).fixedSubgroup =
      (centralizer ({(t : G)} : Set G)).subgroupOf A := by
    ext y
    rw [MulAut.mem_fixedSubgroup, mem_subgroupOf, mem_centralizer_singleton_iff,
      Subtype.ext_iff]
    change (t : G) * (y : G) * (t : G)⁻¹ = y ↔ (y : G) * t = t * y
    rw [mul_inv_eq_iff_eq_mul, eq_comm]
  rw [he, ← card_map_of_injective (f := A.subtype) Subtype.val_injective,
    subgroupOf_map_subtype, inf_comm]

omit h [Finite G] in
private theorem action_involutive (A : Subgroup G) (t : normalizer (A : Set G))
    (ht : orderOf t = 2) : Function.Involutive (A.normalizerMonoidHom t) := by
  have he : A.normalizerMonoidHom t ^ 2 = 1 := by
    rw [← map_pow, show t ^ 2 = 1 from ht ▸ pow_orderOf_eq_one t, map_one]
  exact fun y => congrArg (fun f : MulAut A => f y) he

private theorem fixed_card_three [IsSimpleGroup G] (A : Subgroup G)
    (he : IsElementaryAbelian 3 A) (hc : Nat.card A = 27)
    (hN : 4 ∣ Nat.card (normalizer (A : Set G)))
    (t : normalizer (A : Set G)) (ht : orderOf t = 2) :
    Nat.card (A ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) = 3 := by
  let _ := he
  obtain ⟨u, hu, htu, hcomm⟩ := h.involution_partner _ hN t ht
  have hbound (v : normalizer (A : Set G)) (hv : orderOf v = 2) :
      Nat.card (A.normalizerMonoidHom v).fixedSubgroup ∣ 3 := by
    rw [action_fixed_card]
    exact h.elementary_twentySeven_involution_fixed_card_dvd A hc v
      ((orderOf_injective (normalizer (A : Set G)).subtype Subtype.val_injective v).trans hv)
  have hformula := Theory.GroupAction.brauerWielandt_fixedSubgroup_card_of_isMulCommutative
    (show Odd (Nat.card A) by rw [hc]; decide) (A.normalizerMonoidHom t)
    (A.normalizerMonoidHom u) (action_involutive A t ht) (action_involutive A u hu)
    (hcomm.map A.normalizerMonoidHom)
  rw [hc, ← map_mul] at hformula
  have hbdt := hbound t ht
  have hbdu := Nat.le_of_dvd (by decide : 0 < 3) (hbound u hu)
  have hbdtu := Nat.le_of_dvd (by decide : 0 < 3) (hbound (t * u) htu)
  have hpos : 0 < Nat.card ↥((A.normalizerMonoidHom t).fixedSubgroup ⊓
    (A.normalizerMonoidHom u).fixedSubgroup) := Nat.card_pos
  rw [← action_fixed_card]
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hbdt with hone | hthree
  · rw [hone, one_mul] at hformula
    nlinarith
  · exact hthree

private theorem normalizer_involution_conjugate [IsSimpleGroup G]
    {x : G} {A : Subgroup G} (a : OddCentralizerComplement h x A)
    (he : IsElementaryAbelian 3 A) (hc : Nat.card A = 27)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = 3)
    (hN : 4 ∣ Nat.card (normalizer (A : Set G)))
    (t : normalizer (A : Set G)) (ht : orderOf t = 2) :
    IsConj t (⟨h.z, a.z_mem_normalizer⟩ : normalizer (A : Set G)) := by
  let _ := he
  let F := A ⊓ centralizer ({(t : G)} : Set G)
  have hF : Nat.card F = 3 := h.fixed_card_three A he hc hN t ht
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := F) 3 (by rw [hF])
  have hyG : orderOf (y : G) = 3 :=
    (orderOf_injective F.subtype Subtype.val_injective y).trans hy
  have htG : orderOf (t : G) = 2 :=
    (orderOf_injective (normalizer (A : Set G)).subtype Subtype.val_injective t).trans ht
  obtain ⟨g, hg⟩ := h.involutions_conjugate t htG
  let e := MulAut.conj g
  have het : e (t : G) = h.z := hg
  let C := centralizer ({h.z} : Set G)
  have hey : e (y : G) ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← het, ← map_mul, ← map_mul]
    exact congrArg e (mem_centralizer_singleton_iff.mp y.property.2)
  let yC : C := ⟨e y, hey⟩
  let xC : C := ⟨x, hxC⟩
  have hyC : orderOf yC = 3 :=
    (orderOf_injective C.subtype Subtype.val_injective yC).symm.trans
      ((e.orderOf_eq _).trans hyG)
  have hxC3 : orderOf xC = 3 :=
    (orderOf_injective C.subtype Subtype.val_injective xC).symm.trans hx
  have hP (P : Sylow 3 C) : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, h.centralizer_card]
    decide +kernel
  obtain ⟨k, hk⟩ := exists_conj_mem_of_sylow_card_eq_prime
    (zpowers xC) xC (mem_zpowers xC) hxC3 hP yC hyC
  let v : C := k * yC * k⁻¹
  have hv3 : orderOf v = 3 := ((MulAut.conj k).orderOf_eq yC).trans hyC
  have hvline : zpowers v = zpowers xC := eq_of_le_of_card_ge
    (zpowers_le.mpr hk) (by rw [Nat.card_zpowers, Nat.card_zpowers, hv3, hxC3])
  have hxv : xC ∈ zpowers v := hvline.symm ▸ mem_zpowers xC
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hxv
  let d : G := (k : G) * g
  let f := MulAut.conj d
  have hv : (v : G) = f (y : G) := by
    change (k : G) * (g * (y : G) * g⁻¹) * (k : G)⁻¹ =
      ((k : G) * g) * (y : G) * ((k : G) * g)⁻¹
    simp only [mul_inv_rev, mul_assoc]
  have hfn : (f (y : G)) ^ n = x := by
    rw [← hv]
    exact congrArg (fun w : C => (w : G)) hn
  have hfA : A.map f.toMonoidHom ≤ A := by
    rintro _ ⟨b, hb, rfl⟩
    apply (a.mem_iff_odd_orderOf ?_).mpr
    · change Odd (orderOf (f b))
      rw [f.orderOf_eq]
      exact a.odd_orderOf hb
    · apply mem_centralizer_singleton_iff.mpr
      rw [← hfn]
      have hby : Commute b (y : G) :=
        congrArg (fun w : A => (w : G))
          (mul_comm (⟨b, hb⟩ : A) (⟨y, y.property.1⟩ : A))
      exact ((hby.map f.toMonoidHom).zpow_right n).eq
  have hfAe : A.map f.toMonoidHom = A :=
    eq_of_le_of_card_ge hfA (by rw [card_map_of_injective f.injective])
  have hd : d ∈ normalizer (A : Set G) := mem_normalizer_iff_map_conj_eq.mpr hfAe
  apply isConj_iff.mpr
  refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
  change d * (t : G) * d⁻¹ = h.z
  calc
    d * (t : G) * d⁻¹ = (k : G) * (g * (t : G) * g⁻¹) * (k : G)⁻¹ := by
      dsimp [d]
      simp only [mul_inv_rev, mul_assoc]
    _ = (k : G) * h.z * (k : G)⁻¹ := by rw [hg]
    _ = h.z := by
      rw [mem_centralizer_singleton_iff.mp k.property, mul_inv_cancel_right]

/-- The literal exceptional normalizer action has a four-divisible order,
elementary Sylow two-subgroups, and a single conjugacy class of involutions. -/
public theorem exceptional_automizer_local_conditions [IsSimpleGroup G]
    (p : ℕ) (hp : p = 3 ∨ p = 5) (x : G)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (A : Subgroup G) (a : OddCentralizerComplement h x A)
    (he : IsElementaryAbelian 3 A) (hc : Nat.card A = 27) :
    (4 ∣ Nat.card A.normalizerMonoidHom.range) ∧
      (∀ P : Sylow 2 A.normalizerMonoidHom.range, IsElementaryAbelian 2 P) ∧
      (∀ t u : A.normalizerMonoidHom.range,
        orderOf t = 2 → orderOf u = 2 → IsConj t u) := by
  have hN := h.four_dvd_normalizer a hc p hp hxC hx
  have hK : 4 ∣ Nat.card A.normalizerMonoidHom.range := by
    rw [a.normalizer_card_of_elementary_twentySeven he hc] at hN
    exact (by decide : Nat.Coprime 4 27).dvd_of_dvd_mul_left hN
  refine ⟨hK, h.automizer_sylow_elementary A, ?_⟩
  have hx3 : orderOf x = 3 := hx.trans
    (a.prime_eq_three_of_card_twentySeven hc p hp hx)
  let f := A.normalizerMonoidHom.rangeRestrict
  have hf : Function.Surjective f := A.normalizerMonoidHom.rangeRestrict_surjective
  have hodd : Odd (Nat.card f.ker) := by
    change Odd (Nat.card A.normalizerMonoidHom.rangeRestrict.ker)
    rw [MonoidHom.ker_rangeRestrict,
      a.normalizer_action_ker_of_elementary_twentySeven he hc,
      Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv]
    exact a.odd_card
  intro t u ht hu
  have hinv {v : A.normalizerMonoidHom.range} (hv : orderOf v = 2) :
      IsInvolution v :=
    ⟨by intro heq; simp [heq] at hv, hv ▸ pow_orderOf_eq_one v⟩
  obtain ⟨s, hs, hst⟩ := Theory.GroupTheory.exists_involution_lift_of_odd_kernel
    f hf hodd (hinv ht)
  obtain ⟨v, hv, hvu⟩ := Theory.GroupTheory.exists_involution_lift_of_odd_kernel
    f hf hodd (hinv hu)
  have hsv := (h.normalizer_involution_conjugate a he hc hxC hx3 hN s
    (orderOf_eq_prime hs.2 hs.1)).trans
      (h.normalizer_involution_conjugate a he hc hxC hx3 hN v
        (orderOf_eq_prime hv.2 hv.1)).symm
  simpa only [hst, hvu] using f.map_isConj hsv

end CFSG.Quasithin.Janko1CentralizerData
