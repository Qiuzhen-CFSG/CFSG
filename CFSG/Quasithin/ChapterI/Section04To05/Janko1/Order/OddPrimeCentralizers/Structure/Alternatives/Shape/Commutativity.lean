module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.FourAction
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Commutativity of the actual odd centralizer complement

Let A be the normal odd complement in C_G(x), with x of order three or
five in C_G(z). Its commutator subgroup lies in the central subgroup ⟨x⟩.
If A is nonabelian, three-fixed-subgroup factorization supplies a noncentral
y in A centralized by an involution. A nontrivial commutator with y generates
⟨x⟩, so a suitable conjugation sends y to xy and fixes x. Preservation of
element orders, and the orders of odd subgroups in involution centralizers,
force y to have the same prime order as x.

Involution fusion and Sylow conjugacy in the centralizer of order 120
conjugate ⟨x⟩ to ⟨y⟩. The resulting conjugate B of A contains x, since its
members are exactly the odd-order elements of C_G(y). The element x cannot
centralize B: otherwise B ≤ A, equality of orders gives B = A, and y would
centralize A. The commutator bound transported to B now gives an opposite
shear. The product of the two shears sends x to y⁻¹ and y to x. Its action
on x has period four, contradicting the elementary abelian Sylow two-subgroups.

This reconstructs the commutativity step needed in Bender, *Finite groups
with large subgroups* (1974), proof of (4.1), printed p.225, which cites
Janko, *A new finite simple group with abelian Sylow 2-subgroups and its
characterization* (1966), proof of Lemma 3.1. No bound on |A|, Sylow status,
recognition theorem, or exceptional-normalizer construction is assumed.
-/

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

include h in
private theorem no_four_dvd (g : G) : ¬ 4 ∣ orderOf g := by
  intro hd
  let u := g ^ (orderOf g / 4)
  have hu : orderOf u = 4 := orderOf_pow_orderOf_div (orderOf_pos g).ne' hd
  have hp : IsPGroup 2 (zpowers u) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers, hu]; rfl)
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hu2 : u ^ 2 = 1 := congrArg Subtype.val
    (h.any_sylow_square S ⟨u, hS (mem_zpowers u)⟩)
  have hd2 := orderOf_dvd_of_pow_eq_one hu2
  rw [hu] at hd2
  norm_num at hd2

include h in
private theorem opposite_shears (x y a b : G) (hxy : Commute x y) (hx : x ≠ x⁻¹)
    (hax : MulAut.conj a x = x) (hay : MulAut.conj a y = x * y)
    (hbx : MulAut.conj b x = x * y⁻¹) (hby : MulAut.conj b y = y) : False := by
  let c := a * b * a
  let f : MulAut G := MulAut.conj c
  have hfx : f x = y⁻¹ := by
    change MulAut.conj (a * b * a) x = y⁻¹
    simp only [map_mul, MulAut.mul_apply, hax, hbx, map_inv, hay]
    rw [mul_inv_rev, ← mul_assoc, hxy.inv_right.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hfy : f y = x := by
    change MulAut.conj (a * b * a) y = x
    simp only [map_mul, MulAut.mul_apply, hay, hbx, hby, mul_assoc,
      inv_mul_cancel, mul_one, hax]
  have h2 : ¬ Function.IsPeriodicPt f 2 x := by
    change f (f x) ≠ x
    rw [hfx, map_inv, hfy]
    exact hx.symm
  have h4 : Function.IsPeriodicPt f 4 x := by
    change f (f (f (f x))) = x
    rw [hfx, map_inv, hfy, map_inv, hfx, inv_inv, hfy]
  have hm : Function.minimalPeriod f x = 4 :=
    Function.minimalPeriod_eq_prime_pow (p := 2) (k := 1) h2 h4
  have hn : Function.IsPeriodicPt f (orderOf c) x := by
    have hi (n : ℕ) : (f : G → G)^[n] x = MulAut.conj (c ^ n) x := by
      induction n with
      | zero => simp
      | succ n ih =>
        simp only [Function.iterate_succ_apply', ih, pow_succ', map_mul, MulAut.mul_apply]
        rfl
    change (f : G → G)^[orderOf c] x = x
    rw [hi, pow_orderOf_eq_one, map_one]
    rfl
  exact h.no_four_dvd c (hm ▸ hn.minimalPeriod_dvd)

omit [Finite G] in
private theorem exists_shear {A : Subgroup G} {x y : G} {p : ℕ}
    (hp : p.Prime) (hx : orderOf x = p) (hxC : x ∈ centralizer (A : Set G))
    (hd : ⁅A, A⁆ ≤ zpowers x) (hy : y ∈ A) (hyn : y ∉ centralizer (A : Set G)) :
    ∃ u ∈ A, MulAut.conj u x = x ∧ MulAut.conj u y = x * y := by
  have hn : ∃ u ∈ A, ¬ Commute u y := by
    by_contra! hh
    exact hyn (fun u hu => (hh u hu).eq)
  obtain ⟨u, hu, huy⟩ := hn
  let d := ⁅u, y⁆
  have hdmem : d ∈ zpowers x := hd (commutator_mem_commutator hu hy)
  have hdne : d ≠ 1 := fun he => huy (commutatorElement_eq_one_iff_mul_comm.mp he)
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := mem_powers_of_prime_card
    (show Nat.card (zpowers x) = p by rw [Nat.card_zpowers, hx])
    (g := (⟨d, hdmem⟩ : zpowers x)) (g' := (⟨x, mem_zpowers x⟩ : zpowers x))
    (fun he => hdne (congrArg Subtype.val he))
  have hdn : d ^ n = x := congrArg Subtype.val hn
  have hux : MulAut.conj u x = x := by
    rw [MulAut.conj_apply, hxC u hu, mul_assoc, mul_inv_cancel, mul_one]
  have hud : MulAut.conj u d = d := by
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hdmem
    rw [← hm, map_zpow, hux]
  have hpow (k : ℕ) : MulAut.conj (u ^ k) y = d ^ k * y := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', map_mul, MulAut.mul_apply, ih, map_mul, map_pow, hud,
        conj_eq_commutatorElement_mul, ← mul_assoc, ← pow_succ]
  refine ⟨u ^ n, A.pow_mem hu n, ?_, ?_⟩
  · rw [MulAut.conj_apply, hxC _ (A.pow_mem hu n), mul_assoc, mul_inv_cancel, mul_one]
  · rw [hpow, hdn]

/-- A noncentral fixed element must have the marked prime order. -/
private theorem fixed_noncentral_order [IsSimpleGroup G] {A : Subgroup G} {x y t : G}
    (a : OddCentralizerComplement h x A) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (hy : y ∈ A) (hyn : y ∉ centralizer (A : Set G))
    (ht : orderOf t = 2) (hyt : y ∈ centralizer ({t} : Set G)) :
    orderOf y = p := by
  have hxA : x ∈ centralizer (A : Set G) :=
    fun v hv => mem_centralizer_singleton_iff.mp (a.le_centralizer h hv)
  have hp' : p.Prime := by rcases hp with rfl | rfl <;> decide
  obtain ⟨u, _, _, hus⟩ := exists_shear hp' hx hxA
    (a.commutator_le_zpowers p hp hxC hx) hy hyn
  have he : (x * y) ^ orderOf y = 1 := by
    rw [← hus, ← map_pow, pow_orderOf_eq_one, map_one]
  have hxy : Commute x y := (hxA y hy).symm
  rw [hxy.mul_pow, pow_orderOf_eq_one, mul_one] at he
  have hd : p ∣ orderOf y := hx ▸ orderOf_dvd_of_pow_eq_one he
  have hord := h.odd_subgroup_centralizing_involution_card (zpowers y)
    (by rw [Nat.card_zpowers]; exact a.odd_orderOf hy) t ht (zpowers_le.mpr hyt)
  rw [Nat.card_zpowers] at hord
  rcases hord with hone | hthree | hfive
  · exact (hp'.not_dvd_one (hone ▸ hd)).elim
  · exact hthree.trans (((Nat.dvd_prime (by decide : Nat.Prime 3)).mp
      (hthree ▸ hd)).resolve_left hp'.ne_one).symm
  · exact hfive.trans (((Nat.dvd_prime (by decide : Nat.Prime 5)).mp
      (hfive ▸ hd)).resolve_left hp'.ne_one).symm

private theorem exists_fixed_noncentral [IsSimpleGroup G] {A : Subgroup G} {x : G}
    (a : OddCentralizerComplement h x A) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (hnab : ¬ IsMulCommutative A) :
    ∃ y t : G, y ∈ A ∧ orderOf y = p ∧ y ∉ centralizer (A : Set G) ∧
      orderOf t = 2 ∧ y ∈ centralizer ({t} : Set G) := by
  obtain ⟨t, htC, ht, htz, hti⟩ := h.exists_local_inverter p hp x hxC hx
  have hzt : orderOf (h.z * t) = 2 := by
    have hc : Commute h.z t := (mem_centralizer_singleton_iff.mp htC).symm
    apply orderOf_eq_prime_iff.mpr
    constructor
    · rw [hc.mul_pow, show h.z ^ 2 = 1 from h.involution ▸ pow_orderOf_eq_one h.z,
        show t ^ 2 = 1 from ht ▸ pow_orderOf_eq_one t, mul_one]
    · intro he
      apply htz
      have he' : t = h.z⁻¹ := by simpa using congrArg (h.z⁻¹ * ·) he
      rw [he']
      exact (zpowers h.z).inv_mem (mem_zpowers h.z)
  have hnot : ¬ A ≤ centralizer (A : Set G) :=
    fun hc => hnab (le_centralizer_iff_isMulCommutative.mp hc)
  obtain ⟨w, hw, hwn⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨u, v, w', hu, hv, hw', he⟩ :=
    a.four_fixed_factorization p hp hxC hx t htC ht hti w hw
  have huc : u ∈ centralizer (A : Set G) := by
    apply (zpowers_le.mpr (show x ∈ centralizer (A : Set G) from ?_)) hu
    exact fun s hs => mem_centralizer_singleton_iff.mp (a.le_centralizer h hs)
  have hn : v ∉ centralizer (A : Set G) ∨ w' ∉ centralizer (A : Set G) := by
    by_contra! hh
    exact hwn (he ▸ (centralizer (A : Set G)).mul_mem
      ((centralizer (A : Set G)).mul_mem huc hh.1) hh.2)
  rcases hn with hvn | hwn'
  · exact ⟨v, t, hv.1, fixed_noncentral_order h a p hp hxC hx hv.1 hvn ht hv.2,
      hvn, ht, hv.2⟩
  · exact ⟨w', h.z * t, hw'.1,
      fixed_noncentral_order h a p hp hxC hx hw'.1 hwn' hzt hw'.2, hwn', hzt, hw'.2⟩

/-- Prime-order subgroups of involution centralizers fuse through C_G(z). -/
private theorem prime_conjugate [IsSimpleGroup G] (h : Janko1CentralizerData G)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x : G) (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (X : Subgroup G) (hX : Nat.card X = p)
    (ht : ∃ t : G, orderOf t = 2 ∧ X ≤ centralizer ({t} : Set G)) :
    ∃ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom = X := by
  let _ : Fact (Nat.Prime p) := ⟨by rcases hp with rfl | rfl <;> decide⟩
  obtain ⟨t, ht, hXt⟩ := ht
  obtain ⟨s, hs⟩ := h.involutions_conjugate t ht
  let f := MulAut.conj s
  let C := centralizer ({h.z} : Set G)
  let X' := X.map f.toMonoidHom
  have hX'C : X' ≤ C := by
    rintro w ⟨v, hv, rfl⟩
    rw [mem_centralizer_singleton_iff]
    change f v * h.z = h.z * f v
    rw [← show f t = h.z from hs, ← map_mul, ← map_mul]
    exact congrArg f (mem_centralizer_singleton_iff.mp (hXt hv))
  have hUC : zpowers x ≤ C := zpowers_le.mpr hxC
  have sylow_of_prime (D : Subgroup G) (hDC : D ≤ C) (hD : Nat.card D = p) :
      ∃ P : Sylow p C, (P : Subgroup C) = D.subgroupOf C := by
    have hc : Nat.card (D.subgroupOf C) = p :=
      (Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv).trans hD
    have hi := (D.subgroupOf C).card_mul_index
    rw [hc, show Nat.card C = 120 from h.centralizer_card] at hi
    have hpD : IsPGroup p (D.subgroupOf C) :=
      IsPGroup.of_card (n := 1) (by simpa using hc)
    exact ⟨hpD.toSylow (by rcases hp with rfl | rfl <;> omega), rfl⟩
  obtain ⟨P, hP⟩ := sylow_of_prime X' hX'C (by
    rw [card_map_of_injective f.injective, hX])
  obtain ⟨Q, hQ⟩ := sylow_of_prime (zpowers x) hUC (by rw [Nat.card_zpowers, hx])
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq C P Q
  have hmap : X.map (MulAut.conj ((n : G) * s)).toMonoidHom = zpowers x := by
    apply eq_of_le_of_card_ge
    · rintro w ⟨v, hv, rfl⟩
      have hv' : f v ∈ X' := mem_map.mpr ⟨v, hv, rfl⟩
      let vC : C := ⟨f v, hX'C hv'⟩
      have hvP : vC ∈ (P : Subgroup C) := by rw [hP]; exact hv'
      have hnQ : n * vC * n⁻¹ ∈ (Q : Subgroup C) := by
        rw [← hn]
        exact ⟨vC, hvP, rfl⟩
      rw [hQ] at hnQ
      change (n : G) * (s * v * s⁻¹) * (n : G)⁻¹ ∈ zpowers x at hnQ
      simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        MulAut.conj_apply, mul_inv_rev, mul_assoc] using hnQ
    · rw [card_map_of_injective (MulAut.conj _).injective, hX, Nat.card_zpowers, hx]
  refine ⟨((n : G) * s)⁻¹, ?_⟩
  rw [← hmap, map_map]
  have he : (MulAut.conj ((n : G) * s)⁻¹).toMonoidHom.comp
      (MulAut.conj ((n : G) * s)).toMonoidHom = MonoidHom.id G := by
    ext v
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_id]

omit [Finite G] in
private theorem map_centralizer (D : Subgroup G) (f : G ≃* G) :
    (centralizer (D : Set G)).map f.toMonoidHom =
      centralizer (D.map f.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro y hy
    rw [mem_map_equiv]
    intro d hd
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using
      hy (f d) (mem_map.mpr ⟨d, hd, rfl⟩)

/-- Transporting the actual complement produces the second, opposite shear. -/
private theorem no_conjugate_noncentral {A : Subgroup G} {x y : G}
    (a : OddCentralizerComplement h x A) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (hy : y ∈ A) (hyord : orderOf y = p) (hyn : y ∉ centralizer (A : Set G))
    (f : G ≃* G) (hf : (zpowers x).map f.toMonoidHom = zpowers y) : False := by
  have hp' : p.Prime := by rcases hp with rfl | rfl <;> decide
  have hxA : x ∈ centralizer (A : Set G) :=
    fun w hw => mem_centralizer_singleton_iff.mp (a.le_centralizer h hw)
  have hxy : Commute x y := (hxA y hy).symm
  obtain ⟨u, _, hux, huy⟩ := exists_shear hp' hx hxA
    (a.commutator_le_zpowers p hp hxC hx) hy hyn
  let B := A.map f.toMonoidHom
  have hC : (centralizer ({x} : Set G)).map f.toMonoidHom =
      centralizer ({y} : Set G) := by
    have he := map_centralizer (zpowers x) f
    rw [hf, zpowers_eq_closure, centralizer_closure,
      zpowers_eq_closure, centralizer_closure] at he
    exact he
  have hBC : B ≤ centralizer ({y} : Set G) := by
    rw [← hC]
    exact map_mono (a.le_centralizer h)
  have oddmem {w : G} (hwC : w ∈ centralizer ({y} : Set G))
      (hwodd : Odd (orderOf w)) : w ∈ B := by
    rw [← hC, mem_map_equiv] at hwC
    change w ∈ A.map f.toMonoidHom
    rw [mem_map_equiv]
    apply (a.mem_iff_odd_orderOf hwC).mpr
    rwa [f.symm.orderOf_eq]
  have hBodd {w : G} (hw : w ∈ B) : Odd (orderOf w) := by
    obtain ⟨v, hv, rfl⟩ := hw
    change Odd (orderOf (f v))
    rw [f.orderOf_eq]
    exact a.odd_orderOf hv
  have hxB : x ∈ B := oddmem (mem_centralizer_singleton_iff.mpr hxy.eq)
    (a.odd_orderOf a.x_mem)
  have hxn : x ∉ centralizer (B : Set G) := by
    intro hxc
    have hBA : B ≤ A := by
      intro w hw
      exact (a.mem_iff_odd_orderOf (mem_centralizer_singleton_iff.mpr
        (hxc w hw))).mpr (hBodd hw)
    have he : B = A := eq_of_le_of_card_ge hBA (by
      dsimp only [B]
      rw [card_map_of_injective f.injective])
    apply hyn
    intro w hw
    exact mem_centralizer_singleton_iff.mp (hBC (he.symm ▸ hw))
  have hyd : y ∈ centralizer (B : Set G) :=
    fun w hw => mem_centralizer_singleton_iff.mp (hBC hw)
  have hBd : ⁅B, B⁆ ≤ zpowers y := by
    rw [← hf]
    dsimp only [B]
    rw [← map_commutator]
    exact map_mono (a.commutator_le_zpowers p hp hxC hx)
  obtain ⟨v, _, hvy, hvx⟩ := exists_shear hp' hyord hyd hBd hxB hxn
  have hvi (w : G) : MulAut.conj v (MulAut.conj v⁻¹ w) = w := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hviy : MulAut.conj v⁻¹ y = y := by
    apply (MulAut.conj v).injective
    rw [hvi, hvy]
  have hvix : MulAut.conj v⁻¹ x = x * y⁻¹ := by
    apply (MulAut.conj v).injective
    rw [hvi, map_mul, map_inv, hvx, hvy]
    rw [← hxy.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hxne : x ≠ x⁻¹ := by
    intro he
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      calc x * x = x⁻¹ * x := congrArg (· * x) he
           _ = 1 := inv_mul_cancel x
    have hd := orderOf_dvd_of_pow_eq_one hx2
    rw [hx] at hd
    rcases hp with rfl | rfl <;> norm_num at hd
  exact h.opposite_shears x y u v⁻¹ hxy hxne hux huy hvix hviy

/-- The actual odd complement in the marked odd-prime centralizer is abelian. -/
public theorem OddCentralizerComplement.isMulCommutative [IsSimpleGroup G]
    {h : Janko1CentralizerData G}
    {A : Subgroup G} {x : G} (a : OddCentralizerComplement h x A)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    IsMulCommutative A := by
  by_contra hnab
  obtain ⟨y, t, hy, hyord, hyn, ht, hyt⟩ :=
    exists_fixed_noncentral h a p hp hxC hx hnab
  obtain ⟨g, hg⟩ := prime_conjugate h p hp x hxC hx (zpowers y)
    (by rw [Nat.card_zpowers, hyord]) ⟨t, ht, zpowers_le.mpr hyt⟩
  exact no_conjugate_noncentral h a p hp hxC hx hy hyord hyn (MulAut.conj g) hg

end CFSG.Quasithin.Janko1CentralizerData
