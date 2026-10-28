module
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Theory.GroupTheory.UniqueCentralInvolutionSylow

/-!
# Involution centralizers in a central cubic quotient

Cubing lifts involutions through a kernel of order three. Centrality makes
these lifts unique and identifies the full quotient involution centralizer
with the image of the original one. An actual complement therefore gives
an isomorphism, with the quotient map and its kernel retained.

If all involution centralizers are D₈, their unique central involutions make
them self-normalizing Sylow two-subgroups. Sylow conjugacy then fuses all
involutions. This supplies the conjugacy premise of the existing dihedral
recognition API, without a supplied fusion hypothesis.

Source: Baumeister, *A geometry for groups of J₃-type* (2007), Lemma 2.4,
printed p.495; Bender, *Finite groups with large subgroups* (1974), §3.
The lifting argument adapts `Theory.GroupTheory.CentralFiveQuotientInvolutions`.
-/

public section

open Subgroup

namespace Sporadic.Janko3.SourceRecognition.CentralCubicQuotient

private theorem central_cube {A : Type*} [Group A]
    (K : Subgroup A) (hK : Nat.card K = 3) (x : A) (hx : x ∈ K) :
    x ^ 3 = 1 := by
  have hh := pow_card_eq_one' (x := (⟨x, hx⟩ : K))
  rw [hK] at hh
  exact congrArg Subtype.val hh

/-- Taking the third power lifts every quotient involution. Centrality is not needed. -/
theorem exists_involution_lift {A : Type*} [Group A]
    (K : Subgroup A) [K.Normal] (hK : Nat.card K = 3)
    (b : A ⧸ K) (hb : orderOf b = 2) :
    ∃ a : A, orderOf a = 2 ∧ QuotientGroup.mk' K a = b := by
  let q := QuotientGroup.mk' K
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective K b
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  have ha2 : a ^ 2 ∈ K := (QuotientGroup.eq_one_iff _).mp (by
    change q (a ^ 2) = 1
    rw [map_pow, ha, hb2])
  have ha6 : a ^ 6 = 1 := by simpa only [← pow_mul] using central_cube K hK (a ^ 2) ha2
  have ha3q : q (a ^ 3) = b := by
    rw [map_pow, ha, show 3 = 2 * 1 + 1 by rfl, pow_succ, pow_mul, hb2, one_pow, one_mul]
  refine ⟨a ^ 3, orderOf_eq_prime (by simpa only [← pow_mul] using ha6) ?_, ha3q⟩
  intro hh
  have hb1 : b = 1 := by rw [← ha3q, hh, map_one]
  simp [hb1] at hb

/-- Involutions with the same image modulo a central three-subgroup are equal. -/
theorem involution_eq_of_image_eq {A : Type*} [Group A]
    (K : Subgroup A) [K.Normal] (hKZ : K ≤ center A) (hK : Nat.card K = 3)
    (a b : A) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : QuotientGroup.mk' K a = QuotientGroup.mk' K b) : a = b := by
  let d := a / b
  have hdZ : d ∈ K := QuotientGroup.eq_iff_div_mem.mp hab
  have hd3 : d ^ 3 = 1 := central_cube K hK d hdZ
  have hdb : Commute d b := (mem_center_iff.mp (hKZ hdZ) b).symm
  have habc : Commute a b := by
    simpa [d, div_eq_mul_inv, mul_assoc] using hdb.mul_left (Commute.refl b)
  have hd2 : d ^ 2 = 1 := by
    change (a / b) ^ 2 = 1
    rw [div_eq_mul_inv, (habc.inv_right).mul_pow, ha, inv_pow, hb]
    simp
  have hd1 : d = 1 := by
    have hh := hd3
    rw [show 3 = 2 * 1 + 1 by rfl, pow_succ, pow_mul, hd2, one_pow, one_mul] at hh
    exact hh
  exact div_eq_one.mp hd1

/-- The full centralizer of an involution is the inverse image of its quotient centralizer. -/
theorem centralizer_comap {A : Type*} [Group A]
    (K : Subgroup A) [K.Normal] (hKZ : K ≤ center A) (hK : Nat.card K = 3)
    (t : A) (ht : orderOf t = 2) :
    (centralizer ({QuotientGroup.mk' K t} : Set (A ⧸ K))).comap
      (QuotientGroup.mk' K) = centralizer ({t} : Set A) := by
  let q := QuotientGroup.mk' K
  ext a
  simp only [mem_comap, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hc : a * t * a⁻¹ = t := by
      apply involution_eq_of_image_eq K hKZ hK
      · change (MulAut.conj a t) ^ 2 = 1
        have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
        rw [← map_pow, ht2, map_one]
      · exact ht ▸ pow_orderOf_eq_one t
      · change q (a * t * a⁻¹) = q t
        rw [map_mul, map_mul, map_inv, h, mul_assoc, mul_inv_cancel, mul_one]
    exact mul_inv_eq_iff_eq_mul.mp hc
  · intro h
    simpa only [map_mul] using congrArg q h


/-- A complement maps isomorphically onto the full quotient involution centralizer. -/
theorem centralizer_equiv {A : Type*} [Group A]
    (K : Subgroup A) [K.Normal] (hKZ : K ≤ center A) (hK : Nat.card K = 3)
    (t : A) (ht : orderOf t = 2)
    (U : Subgroup A) (hd : Disjoint U K)
    (hgen : U ⊔ K = centralizer ({t} : Set A)) :
    Nonempty (centralizer ({QuotientGroup.mk' K t} : Set (A ⧸ K)) ≃* U) := by
  let q := QuotientGroup.mk' K
  have hmap : U.map q = centralizer ({q t} : Set (A ⧸ K)) := by
    have hm := congrArg (Subgroup.map q) hgen
    have hKmap : K.map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [Subgroup.map_sup, hKmap, sup_bot_eq] at hm
    rw [← centralizer_comap K hKZ hK t ht,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hm
    exact hm
  have hi : Function.Injective (q.comp U.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro u hu
    apply Subtype.ext
    exact disjoint_def.mp hd u.property ((QuotientGroup.eq_one_iff _).mp hu)
  have hr : (q.comp U.subtype).range = U.map q := by
    rw [MonoidHom.range_comp, range_subtype]
  exact ⟨(MulEquiv.subgroupCongr (hr.trans hmap)).symm.trans
    (MonoidHom.ofInjective hi).symm⟩
private theorem unique_dihedral_central_involution {B : Type*} [Group B]
    (e : B ≃* DihedralGroup 4) (x y : B) (hx : x ∈ center B) (hy : y ∈ center B)
    (hxo : orderOf x = 2) (hyo : orderOf y = 2) : x = y := by
  apply e.injective
  exact (show ∀ a b : DihedralGroup 4, a ∈ center (DihedralGroup 4) →
    b ∈ center (DihedralGroup 4) → a ≠ 1 → b ≠ 1 → a = b from
      by decide +kernel) (e x) (e y)
    (centerCongr e ⟨x,hx⟩).property (centerCongr e ⟨y,hy⟩).property
    (by intro he; have hh := (e.orderOf_eq x).trans hxo; simp [he] at hh)
    (by intro he; have hh := (e.orderOf_eq y).trans hyo; simp [he] at hh)

private theorem dihedral_centralizer_sylow {B : Type*} [Group B] [Finite B]
    (t : B) (ht : orderOf t = 2)
    (e : centralizer ({t} : Set B) ≃* DihedralGroup 4) :
    ∃ S : Sylow 2 B, (S : Subgroup B) = centralizer ({t} : Set B) := by
  let C := centralizer ({t} : Set B)
  let tC : C := ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩
  have htC : orderOf tC = 2 := (orderOf_coe tC).symm.trans ht
  have htc : tC ∈ center C := mem_center_iff.mpr (fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.mp x.property))
  have hc : Nat.card C = 8 := (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  apply exists_sylow_of_unique_central_involution C (IsPGroup.of_card (p := 2) (n := 3) hc)
    tC htC htc (fun x hx hxo => unique_dihedral_central_involution e x tC hx htc hxo htC)
  change ¬ 2 ∣ C.relIndex C
  simp

/-- Full D₈ involution centralizers force a single involution class. -/
theorem dihedral_centralizers_fusion {B : Type*} [Group B] [Finite B]
    (h : ∀ t : B, orderOf t = 2 → Nonempty (centralizer ({t} : Set B) ≃* DihedralGroup 4))
    (t u : B) (ht : orderOf t = 2) (hu : orderOf u = 2) : IsConj t u := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨S,hS⟩ := dihedral_centralizer_sylow t ht (h t ht).some
  obtain ⟨T,hT⟩ := dihedral_centralizer_sylow u hu (h u hu).some
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq B S T
  let f : S ≃* T := (S.equivSMul g).trans
    (MulEquiv.subgroupCongr (congrArg Sylow.toSubgroup hg))
  have htS : t ∈ (S : Subgroup B) := hS.symm ▸ mem_centralizer_singleton_iff.mpr rfl
  have huT : u ∈ (T : Subgroup B) := hT.symm ▸ mem_centralizer_singleton_iff.mpr rfl
  let tS : S := ⟨t,htS⟩
  let uT : T := ⟨u,huT⟩
  have htc : tS ∈ center S := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hS ▸ x.property)
  have huc : uT ∈ center T := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hT ▸ x.property)
  have he : f tS = uT := unique_dihedral_central_involution
    ((MulEquiv.subgroupCongr hT).trans (h u hu).some) (f tS) uT
    (centerCongr f ⟨tS,htc⟩).property huc
    ((f.orderOf_eq tS).trans ((orderOf_coe tS).symm.trans ht))
    ((orderOf_coe uT).symm.trans hu)
  exact isConj_iff.mpr ⟨g,congrArg (fun x : T => (x : B)) he⟩

end Sporadic.Janko3.SourceRecognition.CentralCubicQuotient
