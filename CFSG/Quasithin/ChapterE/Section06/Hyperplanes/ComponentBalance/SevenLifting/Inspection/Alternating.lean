module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection
public import Theory.Alternating.Aut
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# The alternating case of the seven-component inspection

Both A₇ and its perfect central three-cover have order divisible by seven.
An element of order seven in Aₙ, for n ≤ 8, is a seven-cycle, so n ≥ 7
and its centralizer in Sₙ has order seven. Every automorphism of A₇ or A₈
is induced faithfully by Sₙ. Consequently, a two-subgroup of automorphisms
fixing this element is trivial, element by element.

This proves the published inspection for the entire acting two-subgroup and
both component models. In fact, only the component's inclusion in the common
fixed subgroup is needed. No passage from a common-fixed component to an
involution-fixed component is made. The degree bound and actual model suffice;
simplicity and strong quasithinness need not be used separately.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18,
printed p.252 (PDF p.263), and Theorem C, printed p.33. The automorphism
identification is GLS vol. 3, Theorem 5.2.1, proved in `Theory.Alternating.Aut`.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance

private theorem seven_dvd_card {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsSeven L) : 7 ∣ Nat.card L := by
  have hA : 7 ∣ Nat.card (alternatingGroup (Fin 7)) := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rcases hL with ha | hc
  · obtain ⟨e⟩ := ha
    rwa [Nat.card_congr e.toEquiv]
  · obtain ⟨_, _, ⟨e⟩⟩ := hc
    have hq : 7 ∣ Nat.card (L ⧸ center L) := by
      rwa [Nat.card_congr e.toEquiv]
    exact hq.trans (center L).card_quotient_dvd_card

private theorem seven_cycle_centralizer {n : ℕ} (hn : n ≤ 8)
    (c : Equiv.Perm (Fin n)) (hc : orderOf c = 7) :
    7 ≤ n ∧ Nat.card (centralizer ({c} : Set (Equiv.Perm (Fin n)))) = 7 := by
  have hcycle : c.IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by rw [hc]; decide) (by simp only [Fintype.card_fin, hc]; omega)
  have hs : c.support.card = 7 := hcycle.orderOf.symm.trans hc
  have h7n : 7 ≤ n := by
    simpa only [hs, Fintype.card_fin] using c.support.card_le_univ
  refine ⟨h7n, ?_⟩
  rw [Equiv.Perm.nat_card_centralizer, hcycle.cycleType, hs]
  have hd : n - 7 ≤ 1 := by omega
  interval_cases h : n - 7 <;> simp [Fintype.card_fin, h]

private theorem two_subgroup_eq_bot_of_fixed_seven {S : Type*} [Group S] {n : ℕ}
    (e : S ≃* alternatingGroup (Fin n)) (hn : n ≤ 8)
    (P : Subgroup (MulAut S)) (hP : IsPGroup 2 P)
    (x : S) (hx : orderOf x = 7) (hfix : ∀ a : P, (a : MulAut S) x = x) : P = ⊥ := by
  let c : Equiv.Perm (Fin n) := (e x).val
  have hc : orderOf c = 7 := by
    rw [Subgroup.orderOf_coe, e.orderOf_eq, hx]
  obtain ⟨h7n, hcard⟩ := seven_cycle_centralizer hn c hc
  let f : Equiv.Perm (Fin n) →* MulAut (alternatingGroup (Fin n)) := MulAut.conjNormal
  have hf : Function.Bijective f :=
    GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n (by omega) (by omega)
  apply eq_bot_iff.mpr
  intro a ha
  let aP : P := ⟨a, ha⟩
  obtain ⟨s, hs⟩ := hf.surjective ((MulAut.congr e) a)
  have hfixed : f s (e x) = e x := by
    rw [hs]
    simpa [MulAut.congr_apply] using congrArg e (hfix aP)
  have hsc : s ∈ centralizer ({c} : Set (Equiv.Perm (Fin n))) := by
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg Subtype.val hfixed
    change s * c * s⁻¹ = c at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hord : orderOf s = orderOf aP := by
    rw [← orderOf_injective f hf.injective s, hs, (MulAut.congr e).orderOf_eq]
    exact Subgroup.orderOf_coe aP
  have hd : orderOf aP ∣ 7 := by
    have hd := orderOf_dvd_natCard (⟨s, hsc⟩ : centralizer ({c} : Set (Equiv.Perm (Fin n))))
    rwa [Subgroup.orderOf_mk, hcard, hord] at hd
  have hcop := hP.orderOf_coprime (by decide : Nat.Coprime 2 7) aP
  have hone : aP = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hd)
  exact congrArg Subtype.val hone

/-- The alternating branch of the E.6.18 automorphism inspection, retaining
the whole two-subgroup and both A₇ and its perfect central three-cover.
The concrete model and degree bound already imply the result. -/
theorem sevenActionInspection_of_isAlternating {S : Type*} [Group S] [Finite S] {n : ℕ}
    (hm : Chapter1.Section02.LocalModels.IsAlternating S n)
    (hn : n ≤ 8) : SevenActionInspection S := by
  obtain ⟨e⟩ := hm
  intro P hP L hLF _ hL
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 7 (seven_dvd_card hL)
  apply two_subgroup_eq_bot_of_fixed_seven e hn P hP x (by rwa [Subgroup.orderOf_coe])
  intro a
  exact hLF x.property a

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
