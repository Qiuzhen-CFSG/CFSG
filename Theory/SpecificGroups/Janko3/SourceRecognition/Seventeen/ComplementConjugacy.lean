module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.LocalAction
public import Mathlib.GroupTheory.Sylow

/-!
# Conjugacy of the faithful overlap actions on the two-core

An automorphism of order five on a group of order sixteen has centralizer
of order at most fifteen: evaluation at a nonidentity element is injective.
A central element of a Sylow five-subgroup then bounds that Sylow subgroup
by five. Sylow conjugacy aligns the order-five subgroups of two faithful
copies of 3 × D₁₀.

Once an order-five subgroup is shared, its full automorphism centralizer
is the cyclic order-fifteen subgroup already contained in either copy.
Each copy acts on the five-subgroup by identity or inversion, forcing the
two copies to coincide. This proves the conjugacy in the normalizer of the
regular two-core used in Baumeister 2.9. The final theorem applies it to the
literal overlap conjugation action on O₂(H₁).

Source: Baumeister, *A geometry for groups of J₃-type* (2007),
Lemma 2.9, printed p.498.
-/

public noncomputable section
open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Janko3.SourceRecognition.Seventeen

private theorem centralizer_five_bound {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V = 16) (r : MulAut V) (hr : orderOf r = 5) :
    Nat.card (centralizer ({r} : Set (MulAut V))) ≤ 15 := by
  classical
  let C := centralizer ({r} : Set (MulAut V))
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV]; decide)
  obtain ⟨v, hv⟩ := exists_ne (1 : V)
  let f : C → {x : V // x ≠ 1} := fun a => ⟨(a : MulAut V) v, by
    intro he
    exact hv ((a : MulAut V).injective (he.trans (map_one _).symm))⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have he : (a : MulAut V) v = (b : MulAut V) v := congrArg Subtype.val hab
    have hc : Commute r ((b : MulAut V)⁻¹ * a) := by
      have hh := C.mul_mem (C.inv_mem b.property) a.property
      exact (mem_centralizer_singleton_iff.mp hh).symm
    have ht : (b : MulAut V)⁻¹ * a = 1 :=
      MulAut.eq_one_of_commute_five_of_fixed hV r _ hr hc v hv (by
        change (b : MulAut V).symm ((a : MulAut V) v) = v
        rw [he, MulEquiv.symm_apply_apply])
    exact Subtype.ext (inv_mul_eq_one.mp ht).symm
  have hc : Nat.card {x : V // x ≠ 1} = 15 := by
    let : Fintype V := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      ← Nat.card_eq_fintype_card, hV]
    simp
  exact hc ▸ Nat.card_le_card_of_injective f hinj

private theorem five_subgroup_sylow {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V = 16) (r : MulAut V) (hr : orderOf r = 5) :
    ∃ P : Sylow 5 (MulAut V), P.toSubgroup = zpowers r := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hR : Nat.card (zpowers r) = 5 := (Nat.card_zpowers r).trans hr
  have hp : IsPGroup 5 (zpowers r) := IsPGroup.of_card (n := 1) (by simpa using hR)
  obtain ⟨P, hRP⟩ := hp.exists_le_sylow
  have hlow : 5 ≤ Nat.card P := by
    calc
      5 = Nat.card (zpowers r) := hR.symm
      _ ≤ Nat.card P := card_le_of_le hRP
  let : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Nontrivial (center P) := P.isPGroup'.center_nontrivial
  have hd : 5 ∣ Nat.card (center P) :=
    ((P.isPGroup'.to_subgroup (center P)).card_eq_or_dvd).resolve_left (by
      intro he
      have hlt := Finite.one_lt_card (α := center P)
      omega)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center P) 5 hd
  let a : MulAut V := z.val.val
  have ha : orderOf a = 5 := by
    rw [show orderOf a = orderOf z by simp only [a, Subgroup.orderOf_coe]]
    exact hz
  have hPC : P.toSubgroup ≤ centralizer ({a} : Set (MulAut V)) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    have hh := (mem_center_iff.mp z.property) (⟨x, hx⟩ : P)
    exact congrArg (fun y : P => (y : MulAut V)) hh
  have hbound : Nat.card P ≤ 15 :=
    (card_le_of_le hPC).trans (centralizer_five_bound hV a ha)
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  change Nat.card P = 5 ^ n at hn
  have hnle : n ≤ 1 := by
    by_contra! h
    have hh := Nat.pow_le_pow_right (by decide : 0 < 5) (show 2 ≤ n by omega)
    rw [← hn] at hh
    omega
  have hn1 : n = 1 := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hn
    omega
  have hcard : Nat.card P = 5 := by simpa only [hn1, pow_one] using hn
  exact ⟨P, (eq_of_le_of_card_ge hRP (by rw [hR, hcard])).symm⟩

private theorem complement_five_conjugation :
    ∀ r c : Complement, r ^ 5 = 1 →
      c * r * c⁻¹ = r ∨ c * r * c⁻¹ = r⁻¹ := by decide +kernel

private theorem complement_five_inversion :
    ∀ r : Complement, r ^ 5 = 1 →
      (1, DihedralGroup.sr 0) * r * (1, DihedralGroup.sr 0)⁻¹ = r⁻¹ := by decide +kernel

private theorem complement_fifteen_commutes_five :
    ∀ r : Complement, r ^ 5 = 1 →
      (Multiplicative.ofAdd (1 : ZMod 3), DihedralGroup.r 1) * r =
        r * (Multiplicative.ofAdd (1 : ZMod 3), DihedralGroup.r 1) := by decide +kernel

private theorem complement_five_centralizer_le {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V = 16) (C : Subgroup (MulAut V)) (eC : C ≃* Complement)
    (r : MulAut V) (hr : orderOf r = 5) (hrC : r ∈ C) :
    centralizer ({r} : Set (MulAut V)) ≤ C := by
  let t : C := eC.symm (Multiplicative.ofAdd (1 : ZMod 3), DihedralGroup.r 1)
  have ht : orderOf t = 15 := by
    rw [← orderOf_injective eC.toMonoidHom eC.injective t]
    change orderOf (eC (eC.symm _)) = 15
    rw [MulEquiv.apply_symm_apply, Prod.orderOf_mk, orderOf_ofAdd_eq_addOrderOf,
      ZMod.addOrderOf_one, DihedralGroup.orderOf_r_one]
    decide
  have hr5 : (⟨r, hrC⟩ : C) ^ 5 = 1 := by
    apply Subtype.ext
    change r ^ 5 = 1
    simpa only [hr] using pow_orderOf_eq_one r
  have hcomm : Commute (t : MulAut V) r := by
    have hh := complement_fifteen_commutes_five (eC ⟨r, hrC⟩) (by
      rw [← map_pow, hr5, map_one])
    have hh' : t * (⟨r, hrC⟩ : C) = ⟨r, hrC⟩ * t := by
      apply eC.injective
      simpa only [map_mul, t, MulEquiv.apply_symm_apply] using hh
    exact congrArg Subtype.val hh'
  have hTC : zpowers (t : MulAut V) ≤ centralizer ({r} : Set (MulAut V)) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hcomm)
  have hcard : Nat.card (zpowers (t : MulAut V)) = 15 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht]
  have he := eq_of_le_of_card_ge hTC (by
    rw [hcard]
    exact centralizer_five_bound hV r hr)
  rw [← he]
  exact zpowers_le.mpr t.property

/-- Two faithful copies of 3 × D₁₀ acting on sixteen elements are equal once
an order-five subgroup is shared. -/
theorem complement_eq_of_common_five {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V = 16) (A B : Subgroup (MulAut V))
    (eA : A ≃* Complement) (eB : B ≃* Complement)
    (r : MulAut V) (hr : orderOf r = 5) (hrA : r ∈ A) (hrB : r ∈ B) : A = B := by
  have hcent := complement_five_centralizer_le hV B eB r hr hrB
  let b : B := eB.symm (1, DihedralGroup.sr 0)
  have hrB5 : (⟨r, hrB⟩ : B) ^ 5 = 1 := by
    apply Subtype.ext
    change r ^ 5 = 1
    simpa only [hr] using pow_orderOf_eq_one r
  have hbr : (b : MulAut V) * r * (b : MulAut V)⁻¹ = r⁻¹ := by
    have hh := complement_five_inversion (eB ⟨r, hrB⟩) (by
      rw [← map_pow, hrB5, map_one])
    have hh' : b * (⟨r, hrB⟩ : B) * b⁻¹ = (⟨r, hrB⟩ : B)⁻¹ := by
      apply eB.injective
      simpa only [map_mul, map_inv, b, MulEquiv.apply_symm_apply] using hh
    exact congrArg Subtype.val hh'
  have hAB : A ≤ B := by
    intro a ha
    have hrA5 : (⟨r, hrA⟩ : A)^5 = 1 := by
      apply Subtype.ext
      change r ^ 5 = 1
      simpa only [hr] using pow_orderOf_eq_one r
    have hh := complement_five_conjugation (eA ⟨r, hrA⟩) (eA ⟨a, ha⟩) (by
      rw [← map_pow, hrA5, map_one])
    have hh' : a * r * a⁻¹ = r ∨ a * r * a⁻¹ = r⁻¹ := by
      rcases hh with hh | hh
      · left
        have he : (⟨a, ha⟩ : A) * ⟨r, hrA⟩ * (⟨a, ha⟩ : A)⁻¹ = ⟨r, hrA⟩ := by
          apply eA.injective
          simpa only [map_mul, map_inv] using hh
        exact congrArg Subtype.val he
      · right
        have he : (⟨a, ha⟩ : A) * ⟨r, hrA⟩ * (⟨a, ha⟩ : A)⁻¹ = (⟨r, hrA⟩ : A)⁻¹ := by
          apply eA.injective
          simpa only [map_mul, map_inv] using hh
        exact congrArg Subtype.val he
    rcases hh' with hc | hi
    · apply hcent
      apply mem_centralizer_singleton_iff.mpr
      calc
        a * r = (a * r * a⁻¹) * a := by group
        _ = r * a := by rw [hc]
    · have hc : (b : MulAut V)⁻¹ * a ∈ centralizer ({r} : Set (MulAut V)) := by
        apply mem_centralizer_singleton_iff.mpr
        calc
          (b : MulAut V)⁻¹ * a * r = (b : MulAut V)⁻¹ * (a * r * a⁻¹) * a := by group
          _ = (b : MulAut V)⁻¹ * ((b : MulAut V) * r * (b : MulAut V)⁻¹) * a := by rw [hi, hbr]
          _ = r * ((b : MulAut V)⁻¹ * a) := by group
      have hm := B.mul_mem b.property (hcent hc)
      simpa only [mul_inv_cancel_left] using hm
  exact eq_of_le_of_card_ge hAB (by rw [Nat.card_congr eA.toEquiv, Nat.card_congr eB.toEquiv])


private theorem exists_five_in_complement {K : Type*} [Group K]
    (C : Subgroup K) (eC : C ≃* Complement) :
    ∃ r : K, r ∈ C ∧ orderOf r = 5 := by
  let r : C := eC.symm (1, DihedralGroup.r 1)
  refine ⟨r, r.property, ?_⟩
  rw [Subgroup.orderOf_coe, ← orderOf_injective eC.toMonoidHom eC.injective r]
  change orderOf (eC (eC.symm _)) = 5
  rw [MulEquiv.apply_symm_apply, Prod.orderOf_mk, orderOf_one, DihedralGroup.orderOf_r_one]
  decide

/-- The faithful 3 × D₁₀ actions on a fixed group of order sixteen are conjugate
by an automorphism of that group. This is the linear-normalizer step of 2.9. -/
theorem complement_subgroups_conjugate {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V = 16) (A B : Subgroup (MulAut V))
    (eA : A ≃* Complement) (eB : B ≃* Complement) :
    ∃ u : MulAut V, A.map (MulAut.conj u).toMonoidHom = B := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a, haA, ha⟩ := exists_five_in_complement A eA
  obtain ⟨b, hbB, hb⟩ := exists_five_in_complement B eB
  obtain ⟨P, hP⟩ := five_subgroup_sylow hV a ha
  obtain ⟨Q, hQ⟩ := five_subgroup_sylow hV b hb
  obtain ⟨u, hu⟩ := exists_smul_eq (MulAut V) P Q
  have hmap : (zpowers a).map (MulAut.conj u).toMonoidHom = zpowers b := by
    have hh := congrArg Sylow.toSubgroup hu
    change MulAut.conj u • P.toSubgroup = Q.toSubgroup at hh
    rw [Subgroup.pointwise_smul_def, hP, hQ] at hh
    exact hh
  let A' := A.map (MulAut.conj u).toMonoidHom
  let eA' : A' ≃* Complement :=
    (equivMapOfInjective A (MulAut.conj u).toMonoidHom (MulAut.conj u).injective).symm.trans eA
  have hbA' : b ∈ A' := by
    have hh : zpowers b ≤ A' := by
      rw [← hmap]
      exact map_mono (zpowers_le.mpr haA)
    exact hh (mem_zpowers b)
  exact ⟨u, complement_eq_of_common_five hV A' B eA' eB b hb hbA' hbB⟩

namespace SourceData
variable {G : Type*} [Group G] (S : SourceData G)

/-- Apply linear-normalizer conjugacy to the actual faithful action of H₁ ∩ H₂
on O₂(H₁). This retains the source core and its original conjugation map. -/
theorem overlap_actions_conjugate
    (ψ : Complement →* MulAut (pCore 2 S.H1)) (hψ : Function.Injective ψ) :
    ∃ u : MulAut (pCore 2 S.H1),
      S.overlapAction.range.map (MulAut.conj u).toMonoidHom = ψ.range := by
  let : Finite (pCore 2 S.H1) := Nat.finite_of_card_ne_zero (by rw [S.core_card]; decide)
  let eA : S.overlapAction.range ≃* Complement :=
    (MonoidHom.ofInjective S.overlapAction_injective).symm.trans S.overlapEquiv
  let eB : ψ.range ≃* Complement := (MonoidHom.ofInjective hψ).symm
  exact complement_subgroups_conjugate S.core_card _ _ eA eB

end SourceData
end Sporadic.Janko3.SourceRecognition.Seventeen
