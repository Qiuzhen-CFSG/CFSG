module
public import Theory.GroupTheory.Fitting.Core
public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction
import Mathlib.Tactic.Group

/-!
# Coprime automorphisms detected on primary Frattini quotients

An automorphism fixing a self-centralizing normal subgroup displaces each
ambient element into that subgroup. If the automorphism has order coprime
to the ambient group, the displacement has coprime orders and is trivial.
When the Fitting subgroup is self-centralizing, its primary factors detect
a nonidentity coprime automorphism. The Burnside basis-kernel theorem then
detects it on one of their actual Frattini quotients.

This argument allows arbitrary primary exponents and a mixed-prime Fitting
subgroup. Source application: Aschbacher--Smith A.3.6(4), pp.43--45, in the
component-action argument of 11.5.6(3), pp.780--781.
-/

public section
open Subgroup

namespace MulAut

/-- Pointwise fixation of a self-centralizing normal subgroup detects a coprime actor. -/
theorem eq_one_of_coprime_of_fixes_selfCentralizing
    {G : Type*} [Group G] [Finite G] (C : Subgroup G) [C.Normal]
    (hself : centralizer (C : Set G) ≤ C) (a : MulAut G)
    (hcop : Nat.Coprime (orderOf a) (Nat.card G))
    (hfix : ∀ c ∈ C, a c = c) : a = 1 := by
  apply MulEquiv.ext
  intro x
  let d := x⁻¹ * a x
  have hd : d ∈ C := by
    apply hself
    intro c hc
    have h := hfix (x * c * x⁻¹) ((inferInstance : C.Normal).conj_mem c hc x)
    simp only [map_mul, map_inv, hfix c hc] at h
    have hh := congrArg (fun z : G => x⁻¹ * z * a x) h
    group at hh
    simpa only [d, mul_assoc, zpow_neg_one] using hh.symm
  have hp (n : ℕ) : (a ^ n) x = x * d ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix d hd, pow_succ']
        rw [← mul_assoc]
        have hx : x * d = a x := by simp [d]
        rw [hx]
  have hpow : d ^ orderOf a = 1 := by
    have hh := hp (orderOf a)
    rw [pow_orderOf_eq_one] at hh
    exact mul_left_cancel (hh.symm.trans (mul_one x).symm)
  have hd1 : d = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_natCard d))
  exact (inv_mul_eq_one.mp hd1).symm

/-- A nonidentity coprime actor moves the Frattini quotient of an actual prime core. -/
theorem exists_moved_primary_frattini_of_coprime
    {G : Type*} [Group G] [Finite G]
    (hself : centralizer (fittingSubgroup G : Set G) ≤ fittingSubgroup G)
    (a : MulAut G) (hcop : Nat.Coprime (orderOf a) (Nat.card G)) (hne : a ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card (fittingSubgroup G) ∧
      quotientAut (frattini (pCore p G)) (MulAut.characteristic (pCore p G) a) ≠ 1 := by
  classical
  by_contra! h
  apply hne
  apply eq_one_of_coprime_of_fixes_selfCentralizing (fittingSubgroup G) hself a hcop
  have hall : fittingSubgroup G ≤ a.toMonoidHom.eqLocus (MonoidHom.id G) := by
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    let : Fact p.val.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.val.property⟩
    by_cases hb : pCore p.val.val G = ⊥
    · rw [hb]; exact bot_le
    have hd : p.val.val ∣ Nat.card (fittingSubgroup G) := by
      let : Nontrivial (pCore p.val.val G) := (nontrivial_iff_ne_bot _).mpr hb
      obtain ⟨n, hn, hc⟩ := (pCore_isPGroup (p := p.val.val) (G := G)).nontrivial_iff_card.mp inferInstance
      exact (show p.val.val ∣ Nat.card (pCore p.val.val G) by
        rw [hc]; exact dvd_pow_self _ (by omega)).trans
        (card_dvd_of_le (pCore_le_fitting G p.val.val))
    let b := MulAut.characteristic (pCore p.val.val G) a
    let k : (quotientAut (frattini (pCore p.val.val G))).ker :=
      ⟨b, h p.val.val (Fact.out : p.val.val.Prime) hd⟩
    have hk : IsPGroup p.val.val (quotientAut (frattini (pCore p.val.val G))).ker :=
      isPGroup_quotientAut_frattini_kernel pCore_isPGroup
    have hka : orderOf k ∣ orderOf a :=
      (Subgroup.orderOf_coe k) ▸ orderOf_map_dvd (MulAut.characteristic (pCore p.val.val G)) a
    have hcp : Nat.Coprime (orderOf a) p.val.val :=
      hcop.of_dvd_right (Nat.dvd_of_mem_primeFactors p.val.property)
    have hk1 : k = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (hk.orderOf_coprime hcp.symm k) dvd_rfl hka)
    have hb1 : b = 1 := congrArg Subtype.val hk1
    intro x hx
    exact congrArg Subtype.val (DFunLike.congr_fun hb1 (⟨x,hx⟩ : pCore p.val.val G))
  exact fun c hc => hall hc

end MulAut
