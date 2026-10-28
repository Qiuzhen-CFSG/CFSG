module
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.OddCyclicThreeNormalizer
public import Theory.GroupTheory.Commutator.CentralSylowTransfer
public import Mathlib.GroupTheory.IsPerfect

/-!
# Cubic inner actions in groups with cubic center and three-rank two

A cubic inside a perfect subgroup whose order is not divisible by nine
has nontrivial inner action: otherwise central Sylow transfer places it
in the derived subgroup of a cyclic Sylow three-subgroup.

In a group of three-rank at most two with cubic center, two cubics that
normalize one another cannot have independent nontrivial inner actions.
They commute, and adjoining the center would otherwise give an elementary
subgroup of order twenty-seven. The statements retain the actual inner
conjugation map and impose no model or splitting assumptions.

Source: the central-transfer argument in Aschbacher--Smith I.1.2 and the
cubic-cover step of 5.1.13, printed pp.407,637, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup

namespace Theory.GroupTheory.CubicCenterRankTwo
variable {Q : Type*} [Group Q] [Finite Q]

/-- A cubic in a perfect subgroup with no factor nine acts faithfully by inner conjugation. -/
theorem inner_card_three (R B : Subgroup Q) [Group.IsPerfect R]
    (hR : ¬ 9 ∣ Nat.card R) (hBR : B ≤ R) (hB : Nat.card B = 3) :
    Nat.card (B.map MulAut.conj) = 3 := by
  have hd : Nat.card (B.map MulAut.conj) ∣ 3 := hB ▸ card_map_dvd B MulAut.conj
  apply ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left
  intro hc
  have hb : B.map MulAut.conj = ⊥ := card_eq_one.mp hc
  have hz : B ≤ center Q := by
    intro b hbB
    have hh : MulAut.conj b = 1 := by
      simpa only [hb,mem_bot] using mem_map_of_mem MulAut.conj hbB
    exact mem_center_iff.mpr fun x =>
      ((mul_inv_eq_iff_eq_mul).mp (DFunLike.congr_fun hh x)).symm
  let D := B.subgroupOf R
  have hDc : Nat.card D = 3 := by rw [Nat.card_congr (subgroupOfEquivOfLe hBR).toEquiv,hB]
  have hDz : D ≤ center R := fun x hx => mem_center_iff.mpr fun y =>
    Subtype.ext (mem_center_iff.mp (hz hx) y)
  let : D.Normal := ⟨fun x hx y => by
    rw [mem_center_iff.mp (hDz hx) y,mul_inv_cancel_right]
    exact hx⟩
  have hDp : IsPGroup 3 D := IsPGroup.of_card (n := 1) (by simpa using hDc)
  let P : Sylow 3 R := default
  have hDP : D ≤ (P : Subgroup R) := hDp.le_sylow_of_normal P
  have hPcyc : IsCyclic P := by
    obtain ⟨k,hk⟩ := P.isPGroup'.exists_card_eq
    have hk1 : k ≤ 1 := by
      by_contra hn
      apply hR
      exact (pow_dvd_pow 3 (by omega : 2 ≤ k)).trans
        (hk ▸ (P : Subgroup R).card_subgroup_dvd_card)
    apply isCyclic_of_card_dvd_prime (p := 3)
    rw [hk]
    exact pow_dvd_pow 3 hk1
  have hDcomm : D ≤ ⁅(P : Subgroup R),(P : Subgroup R)⁆ := by
    intro d hd
    exact center_inf_commutator_inf_sylow_le_commutator P
      ⟨⟨hDz hd,Group.IsPerfect.mem_commutator⟩,hDP hd⟩
  let : IsCyclic P := hPcyc
  rw [commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative P)] at hDcomm
  have hd0 := congrArg (fun N : Subgroup R => Nat.card N) (le_bot_iff.mp hDcomm)
  rw [hDc,card_bot] at hd0
  omega

/-- In three-rank at most two, two normalized cubics with a cubic center
cannot have independent nontrivial inner actions. -/
theorem inner_le_of_normalized_cubics (E B : Subgroup Q)
    (hZ : Nat.card (center Q) = 3) (hr : primeRank 3 Q ≤ 2)
    (hE : Nat.card E = 3) (hB : Nat.card B = 3)
    (hEi : Nat.card (E.map MulAut.conj) = 3)
    (hBi : Nat.card (B.map MulAut.conj) = 3)
    (hn : B ≤ normalizer (E : Set Q)) :
    E.map MulAut.conj ≤ B.map MulAut.conj := by
  by_contra hnot
  let : IsCyclic E := isCyclic_of_prime_card hE
  let : IsCyclic B := isCyclic_of_prime_card hB
  obtain ⟨d,hd⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  obtain ⟨b,hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := B)
  have hd3 : orderOf (d : Q) = 3 := (orderOf_coe d).trans (hd.trans hE)
  have hb3 : orderOf (b : Q) = 3 := (orderOf_coe b).trans (hb.trans hB)
  have hEd : zpowers (d : Q) = E := eq_of_le_of_card_ge (zpowers_le.mpr d.property)
    (by rw [Nat.card_zpowers,hd3,hE])
  have hBb : zpowers (b : Q) = B := eq_of_le_of_card_ge (zpowers_le.mpr b.property)
    (by rw [Nat.card_zpowers,hb3,hB])
  let : IsCyclic (center Q) := isCyclic_of_prime_card hZ
  let : IsElementaryAbelian 3 (center Q) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun x => by rw [←hZ]; exact pow_card_eq_one') }
  have hdn : (d : Q) ∉ center Q := by
    intro hz
    have hEc : E ≤ center Q := hEd ▸ zpowers_le.mpr hz
    have he : E.map MulAut.conj = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      intro x hx
      ext y
      change x*y*x⁻¹=y
      rw [(mem_center_iff.mp (hEc hx) y).symm,mul_inv_cancel_right]
    rw [he,card_bot] at hEi
    omega
  obtain ⟨hJ,hJc⟩ := IsElementaryAbelian.fixed_join_card (center Q) (d : Q) hd3
    ((center Q).disjoint_zpowers_of_prime_order_not_mem d hd3 hdn)
    (center_le_centralizer _) (show Nat.card (center Q) = 3 ^ 1 by simpa using hZ)
  rw [hEd] at hJ hJc
  let J := center Q ⊔ E
  let : IsElementaryAbelian 3 J := hJ
  have hmap : J.map MulAut.conj = E.map MulAut.conj := by
    rw [Subgroup.map_sup]
    have hz : (center Q).map MulAut.conj = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      intro x hx
      ext y
      change x*y*x⁻¹=y
      rw [(mem_center_iff.mp hx y).symm,mul_inv_cancel_right]
    rw [hz,bot_sup_eq]
  have hbJ : (b : Q) ∉ J := by
    intro hbJ
    have hBJ : B ≤ J := hBb ▸ zpowers_le.mpr hbJ
    have hi : B.map MulAut.conj ≤ E.map MulAut.conj := by
      simpa only [hmap] using map_mono (f := MulAut.conj) hBJ
    exact hnot (eq_of_le_of_card_ge hi (by rw [hBi,hEi])).ge
  have hcomm := commutator_eq_bot_of_odd_normalizes_card_three E B hE
    (by rw [hB]; decide) hn
  have hfix : J ≤ centralizer ({(b : Q)} : Set Q) := by
    apply sup_le (center_le_centralizer _) ?_
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((commutator_eq_bot_iff_le_centralizer.mp hcomm) hx b b.property).symm
  have h3 := IsElementaryAbelian.primeRank_ge_of_fixed_join J (b : Q) hb3 hbJ hfix hJc
  omega
end Theory.GroupTheory.CubicCenterRankTwo
