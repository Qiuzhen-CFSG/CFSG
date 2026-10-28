module

public import Theory.GroupTheory.PGroup.NormalEightCriticalSubgroup
public import Theory.GroupTheory.PGroup.AbelianRankTwoHomocyclic
public import Theory.GroupTheory.PGroup.CriticalSubgroupAutomorphisms
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Cubic action on a critical quaternion extension

Suppose a critical subgroup C of a finite two-group has a quaternion-eight
supplement to its nonelementary center. In the central-four, no-normal-eight
setting, a non-two-group ambient automorphism group contains an automorphism
of order three fixing the center of C pointwise and moving a central coset.

The square of a noncentral quaternion element is not a square in the center:
otherwise dividing by a central square root would give a noncentral involution.
The center has two cyclic factors. If their orders were equal, nonelementarity
would make every involution a square. Thus the factors have unequal orders,
and the center's automorphism group is a two-group. The quaternion supplement
identifies the central quotient as a group of order four. Restriction to C and
then action on this quotient has two-group kernel. Its image has order dividing
six, so Cauchy's theorem gives an ambient automorphism of order three. Coprime
kernel detection makes its quotient action nontrivial, while its center action
is trivial.

Source: MacWilliams, Trans. AMS 150 (1970), §3(i)–(iv), pp.366–368,
DOI 10.1090/S0002-9947-1970-0276324-3. No normality of the quaternion
supplement in the ambient group is required.
-/

open Subgroup
open scoped IsMulCommutative

namespace IsCriticalPSubgroup

private theorem cyclic_square_root {A : Type*} [Group A] [Finite A] [IsCyclic A]
    (hfour : 4 ∣ Nat.card A) (x : A) (hx : x ^ 2 = 1) : ∃ y : A, y ^ 2 = x := by
  by_cases hx1 : x = 1
  · exact ⟨1, by simp [hx1]⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
  let y := g ^ (orderOf g / 4)
  have hy : orderOf y = 4 := orderOf_pow_orderOf_div (orderOf_pos g).ne'
    (hg.symm ▸ hfour)
  refine ⟨y, IsCyclic.eq_of_orderOf_eq_two ?_ (orderOf_eq_prime hx hx1)⟩
  rw [orderOf_pow, hy]
  decide

private theorem quaternion_nonsquare
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (R : Subgroup C) (eR : R ≃* QuaternionGroup 2) :
    ∃ d : center C, d ^ 2 = 1 ∧ ¬ ∃ z : center C, z ^ 2 = d := by
  let f : QuaternionGroup 2 →* C := R.subtype.comp eR.symm.toMonoidHom
  have hf : Function.Injective f := R.subtype_injective.comp eR.symm.injective
  let x : C := f (QuaternionGroup.a 1)
  let y : C := f (QuaternionGroup.xa 0)
  have hxy : x * y ≠ y * x := by
    intro he
    have he' : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 := hf (by simpa only [map_mul] using he)
    exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1) he'
  have hx4 : x ^ 4 = 1 := by
    change f (QuaternionGroup.a 1) ^ 4 = 1
    rw [← map_pow, show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 by decide, map_one]
  have hd2 : (x ^ 2) ^ 2 = 1 := by simpa only [← pow_mul] using hx4
  have hd : x ^ 2 ∈ center C := hC.square_one_mem_center hno hZ _ hd2
  refine ⟨⟨x ^ 2, hd⟩, Subtype.ext hd2, ?_⟩
  rintro ⟨z, hz⟩
  have hz' : (z : C) ^ 2 = x ^ 2 := congrArg Subtype.val hz
  have hxz : Commute x (z : C)⁻¹ :=
    (show Commute x (z : C) from mem_center_iff.mp z.property x).inv_right
  have hw2 : (x * (z : C)⁻¹) ^ 2 = 1 := by
    rw [hxz.mul_pow, inv_pow, hz', mul_inv_cancel]
  have hw : x * (z : C)⁻¹ ∈ center C := hC.square_one_mem_center hno hZ _ hw2
  have hx : x ∈ center C := by
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using (center C).mul_mem hw z.property
  exact hxy (mem_center_iff.mp hx y).symm

private theorem center_aut_isPGroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (hbad : ¬ IsElementaryAbelian 2 (center C))
    (R : Subgroup C) (eR : R ≃* QuaternionGroup 2) :
    IsPGroup 2 (MulAut (center C)) := by
  have hfour : Nat.card (omega₁ (center C) (p := 2)) = 4 :=
    IsPGroup.card_omega_center_eq_four_of_three_central_involutions
      (hC.square_one_mem_center hno hZ) (hC.card_involutions_eq_three hno hZ)
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ :=
    ((hP.to_subgroup C).to_subgroup (center C)).equiv_two_cyclic_factors_of_card_omega_one_eq_four hfour
  have hne : n ≠ m := by
    intro heq
    subst m
    have hn2 : 2 ≤ n := by
      by_contra hh
      have hn1 : n = 1 := by omega
      apply hbad
      refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
      intro z
      apply e.injective
      rw [map_pow, map_one]
      apply Prod.ext
      · have hp := pow_card_eq_one' (x := (e z).1)
        simpa [hn1] using hp
      · have hp := pow_card_eq_one' (x := (e z).2)
        simpa [hn1] using hp
    obtain ⟨d, hd2, hd⟩ := quaternion_nonsquare hC hno hZ R eR
    have hdiv : 4 ∣ Nat.card (Multiplicative (ZMod (2 ^ n))) := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      exact pow_dvd_pow 2 hn2
    have hpow : (e d) ^ 2 = 1 := by rw [← map_pow, hd2, map_one]
    obtain ⟨u, hu⟩ := cyclic_square_root hdiv (e d).1 (congrArg Prod.fst hpow)
    obtain ⟨v, hv⟩ := cyclic_square_root hdiv (e d).2 (congrArg Prod.snd hpow)
    apply hd
    refine ⟨e.symm (u, v), ?_⟩
    apply e.injective
    simpa only [map_pow, e.apply_symm_apply] using Prod.ext hu hv
  exact (abelian_unequal_two_factors_aut_isPGroup n m hne).of_equiv (MulAut.congr e).symm

private theorem card_central_quotient {G : Type*} [Group G] [Finite G]
    (R : Subgroup G) (eR : R ≃* QuaternionGroup 2)
    (hgen : R ⊔ center G = ⊤) : Nat.card (G ⧸ center G) = 4 := by
  let f : R →* G ⧸ center G := (QuotientGroup.mk' (center G)).comp R.subtype
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center G) q
    obtain ⟨r, hr, z, hz, rfl⟩ := mem_sup_of_normal_right.mp (hgen ▸ mem_top g)
    refine ⟨⟨r, hr⟩, ?_⟩
    change QuotientGroup.mk' (center G) r = QuotientGroup.mk' (center G) (r * z)
    have hzq : QuotientGroup.mk' (center G) z = 1 :=
      (QuotientGroup.eq_one_iff (N := center G) z).mpr hz
    rw [map_mul, hzq, mul_one]
  have hker : f.ker = center R := by
    ext r
    change QuotientGroup.mk' (center G) (r : G) = 1 ↔ r ∈ center R
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hr
      exact mem_center_iff.mpr fun s => Subtype.ext (mem_center_iff.mp hr s)
    · intro hr
      apply mem_center_iff.mpr
      intro g
      obtain ⟨s, hs, z, hz, rfl⟩ := mem_sup_of_normal_right.mp (hgen ▸ mem_top g)
      have hscomm := congrArg Subtype.val (mem_center_iff.mp hr (⟨s, hs⟩ : R))
      change s * (r : G) = (r : G) * s at hscomm
      have hzcomm := (mem_center_iff.mp hz (r : G)).symm
      calc
        (s * z) * r = s * ((r : G) * z) := by rw [mul_assoc, hzcomm]
        _ = (r : G) * (s * z) := by rw [← mul_assoc, hscomm, mul_assoc]
  have hcardR : Nat.card R = 8 := by
    rw [Nat.card_congr eR.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcenter : Nat.card (center R) = 2 := by
    rw [Nat.card_congr (centerCongr eR).toEquiv]
    let predicate : QuaternionGroup 2 → Prop := fun x => ∀ y, y * x = x * y
    have hc : Fintype.card {x // predicate x} = 2 := by decide
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun _ => mem_center_iff)), Nat.card_eq_fintype_card]
    exact hc
  have hcard := f.ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv,
    hker, hcenter, hcardR] at hcard
  omega

private theorem exists_cubic_of_center_aut {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hAut : ¬ IsPGroup 2 (MulAut P)) {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hcenterAut : IsPGroup 2 (MulAut (center C)))
    (hfour : Nat.card (C ⧸ center C) = 4) :
    ∃ a : MulAut P, orderOf a = 3 ∧
      (∀ z ∈ (center C).map C.subtype, a z = z) ∧
      ∃ c : C, a (c : P) * (c : P)⁻¹ ∉ (center C).map C.subtype := by
  let : C.Characteristic := hC.characteristic
  let : IsElementaryAbelian 2 (C ⧸ center C) := hC.quotient_elementary
  let : Nontrivial (C ⧸ center C) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour (C ⧸ center C) := ⟨hfour, IsElementaryAbelian.exponent_eq_prime⟩
  let r := MulAut.characteristic C
  let q := quotientAut (center C)
  let f := q.comp r
  have hr : IsPGroup 2 r.ker :=
    C.isPGroup_characteristic_restriction_kernel_of_centralizer_le
      (hP.to_subgroup C) (by rw [hC.centralizer_eq]; exact map_subtype_le _)
  have hk : IsPGroup 2 f.ker :=
    (isPGroup_quotientAut_kernel_of_mulAut (center C)
      ((hP.to_subgroup C).to_subgroup (center C)) hcenterAut).comap_of_ker_isPGroup r hr
  have hn : ¬ IsPGroup 2 f.range := by
    intro hh
    have ht := hh.comap_of_ker_isPGroup f hk
    rw [MonoidHom.comap_range_self] at ht
    exact hAut (ht.of_equiv Subgroup.topEquiv)
  have hd : Nat.card f.range ∣ 6 := by
    rw [← IsKleinFour.card_mulAut (C ⧸ center C)]
    exact card_subgroup_dvd_card _
  have hle : Nat.card f.range ≤ 6 := Nat.le_of_dvd (by decide) hd
  have h3 : 3 ∣ Nat.card f.range := by
    by_contra hh
    have heq : Nat.card f.range = 1 ∨ Nat.card f.range = 2 := by
      interval_cases Nat.card f.range <;> omega
    rcases heq with h | h
    · exact hn (IsPGroup.of_card (n := 0) h)
    · exact hn (IsPGroup.of_card (n := 1) h)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 (h3.trans (Subgroup.card_range_dvd f))
  have hfa : orderOf (f a) = 3 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hk a (by rw [ha]; decide)).trans ha
  let s := (MulAut.characteristic (center C)).comp r
  have hsa : s a = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (hcenterAut.orderOf_coprime (by decide : Nat.Coprime 2 3) (s a)) dvd_rfl
    exact ha ▸ orderOf_map_dvd s a
  refine ⟨a, ha, ?_, ?_⟩
  · rintro z ⟨c, hc, rfl⟩
    have hh := congrArg (fun b : MulAut (center C) => b ⟨c, hc⟩) hsa
    exact congrArg (fun x : center C => ((x : C) : P)) hh
  · by_contra! hall
    have he : f a = 1 := by
      apply MulEquiv.ext
      intro x
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (center C) x
      change quotientAut (center C) (r a) (QuotientGroup.mk' (center C) c) =
        QuotientGroup.mk' (center C) c
      rw [quotientAut_apply_mk]
      apply mul_inv_eq_one.mp
      rw [← map_inv, ← map_mul]
      apply (QuotientGroup.eq_one_iff (N := center C) _).mpr
      obtain ⟨z, hz, he⟩ := hall c
      have he' : z = r a c * c⁻¹ := Subtype.ext he
      exact he' ▸ hz
    simp [he] at hfa

/-- A critical quaternion extension with nonelementary center detects a cubic
ambient automorphism fixing its center pointwise and moving a central coset. -/
public theorem exists_order_three_fixing_center_of_quaternion_supplement
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hAut : ¬ IsPGroup 2 (MulAut P)) {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (hbad : ¬ IsElementaryAbelian 2 (center C))
    (R : Subgroup C) (eR : R ≃* QuaternionGroup 2)
    (hRgen : R ⊔ center C = ⊤) :
    ∃ a : MulAut P, orderOf a = 3 ∧
      (∀ z ∈ (center C).map C.subtype, a z = z) ∧
      ∃ c : C, a (c : P) * (c : P)⁻¹ ∉ (center C).map C.subtype := by
  exact exists_cubic_of_center_aut hP hAut hC
    (center_aut_isPGroup hP hC hno hZ hbad R eR)
    (card_central_quotient R eR hRgen)

end IsCriticalPSubgroup
