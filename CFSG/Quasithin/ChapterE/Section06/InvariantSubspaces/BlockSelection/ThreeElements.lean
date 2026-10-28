module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Mathlib.Tactic.FinCases

/-!
# Three-elements in the actual chi-zero blocks

Each permitted block contains an element of order three. For a rank-one
block this follows from the explicit cubic matrix in its special-linear
quotient; for an alternating block it follows from the order of its actual
alternating quotient. The center of a short group is a two-group because
it lies in the generalized Fitting subgroup.

Consequently, order-three elements in two commuting blocks are independent.
They generate an elementary subgroup of order nine, which excludes two
blocks when the containing group has three-rank at most one.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the first
reduction in the proof of E.6.14, printed p.251 (PDF p.262), using the
block definitions C.1.7 and C.1.12, printed pp.123–124.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups

private theorem sl2_has_three (F : Type*) [Field F] :
    ∃ x : Matrix.SpecialLinearGroup (Fin 2) F, orderOf x = 3 := by
  let x : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩
  refine ⟨x, orderOf_eq_prime ?_ ?_⟩
  · apply Subtype.ext
    change (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have h01 := congrArg (fun a : Matrix.SpecialLinearGroup (Fin 2) F => a.val 1 0) h
    simp [x] at h01

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection

theorem center_isTwoGroup {L : Type*} [Group L] (h : ChapterC.IsShort L) :
    IsPGroup 2 (center L) := by
  let : CommGroup (center L) := IsMulCommutative.instCommGroup
  have hc : center L ≤ fittingSubgroup L :=
    le_sSup ⟨inferInstance, inferInstance⟩
  have hc2 : center L ≤ pCore 2 L :=
    h.fitting ▸ hc.trans (fitting_le_generalizedFitting L)
  exact (pCore_isPGroup (p := 2) (G := L)).to_le hc2

theorem not_mem_center_of_order_three {L : Type*} [Group L] (h : ChapterC.IsShort L)
    {x : L} (hx : orderOf x = 3) : x ∉ center L := by
  intro hc
  have ho : orderOf (⟨x, hc⟩ : center L) = 3 :=
    (orderOf_injective (center L).subtype Subtype.val_injective _).symm.trans hx
  have hco := (center_isTwoGroup h).orderOf_coprime (show Nat.Coprime 2 3 by decide)
    (⟨x, hc⟩ : center L)
  rw [ho] at hco
  norm_num at hco

theorem exists_order_three {L : Type*} [Group L] (h : ChapterC.IsChiZeroBlock L) :
    ∃ x : L, orderOf x = 3 := by
  let : Finite L := h.chi.short.finite
  suffices hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) from
    exists_prime_orderOf_dvd_card' 3 (hd.trans
      (Subgroup.card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 L))
        (QuotientGroup.mk'_surjective _)))
  rcases h with ⟨n, _, _, F, _, _, _, _, hm⟩ | h | h
  · obtain ⟨e⟩ := hm.quotient_iso
    obtain ⟨x, hx⟩ := sl2_has_three F
    rw [Nat.card_congr e.toEquiv]
    exact hx ▸ orderOf_dvd_natCard x
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    rw [Nat.card_congr e.toEquiv]
    rw [nat_card_alternatingGroup]
    norm_num
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    rw [Nat.card_congr e.toEquiv]
    rw [nat_card_alternatingGroup]
    norm_num

variable {G : Type*} [Group G] [Finite G]

theorem nine_of_commuting_threes {L₁ L₂ : Subgroup G}
    (hL₁ : ChapterC.IsShort L₁) (hc : L₂ ≤ centralizer (L₁ : Set G))
    {a b : G} (haL : a ∈ L₁) (hbL : b ∈ L₂)
    (ha : orderOf a = 3) (hb : orderOf b = 3) :
    IsElementaryAbelian 3 (zpowers a ⊔ zpowers b : Subgroup G) ∧
      Nat.card (zpowers a ⊔ zpowers b : Subgroup G) = 9 := by
  have hb₁ : b ∉ L₁ := by
    intro hm
    apply not_mem_center_of_order_three hL₁ (x := ⟨b, hm⟩)
      ((orderOf_injective L₁.subtype Subtype.val_injective ⟨b, hm⟩).symm.trans hb)
    apply mem_center_iff.mpr
    intro l
    exact Subtype.ext (mem_centralizer_iff.mp (hc hbL) l l.property)
  have ha₁ : zpowers a ≤ L₁ := zpowers_le.mpr haL
  have hfix : zpowers a ≤ centralizer ({b} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (hc hbL) x (ha₁ hx))
  let : IsElementaryAbelian 3 (zpowers a) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (ha ▸ pow_orderOf_eq_one a)
  exact IsElementaryAbelian.fixed_join_card (n := 1) (zpowers a) b hb
    ((zpowers a).disjoint_zpowers_of_prime_order_not_mem b hb (fun hm => hb₁ (ha₁ hm)))
    hfix ((Nat.card_zpowers a).trans ha)

theorem nine_of_commuting_blocks {L₁ L₂ : Subgroup G}
    (hL₁ : ChapterC.IsChiZeroBlock L₁) (hL₂ : ChapterC.IsChiZeroBlock L₂)
    (hc : L₂ ≤ centralizer (L₁ : Set G)) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧ E ≤ L₁ ⊔ L₂ := by
  obtain ⟨a, ha⟩ := exists_order_three hL₁
  obtain ⟨b, hb⟩ := exists_order_three hL₂
  have haG : orderOf (a : G) = 3 :=
    (orderOf_injective L₁.subtype Subtype.val_injective a).trans ha
  have hbG : orderOf (b : G) = 3 :=
    (orderOf_injective L₂.subtype Subtype.val_injective b).trans hb
  obtain ⟨he, hcard⟩ := nine_of_commuting_threes hL₁.chi.short hc
    a.property b.property haG hbG
  exact ⟨_, he, hcard, sup_le_sup (zpowers_le.mpr a.property) (zpowers_le.mpr b.property)⟩

/-- Two fixed three-elements in commuting blocks give the literal fixed
nine needed by the normalizer rank obstruction. Constructing these two
elements from the block automorphisms is the remaining model step. -/
theorem fixed_nine_of_commuting_threes {L₁ L₂ : Subgroup G}
    (hL₁ : ChapterC.IsShort L₁) (hc : L₂ ≤ centralizer (L₁ : Set G))
    {a b x : G} (haL : a ∈ L₁) (hbL : b ∈ L₂)
    (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hax : a ∈ centralizer ({x} : Set G)) (hbx : b ∈ centralizer ({x} : Set G)) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      E ≤ L₁ ⊔ L₂ ∧ E ≤ centralizer ({x} : Set G) := by
  obtain ⟨he, hcard⟩ := nine_of_commuting_threes hL₁ hc haL hbL ha hb
  exact ⟨_, he, hcard, sup_le_sup (zpowers_le.mpr haL) (zpowers_le.mpr hbL),
    sup_le (zpowers_le.mpr hax) (zpowers_le.mpr hbx)⟩

theorem two_le_threeRank_of_commuting_blocks {H L₁ L₂ : Subgroup G}
    (hL₁ : ChapterC.IsChiZeroBlock L₁) (hL₂ : ChapterC.IsChiZeroBlock L₂)
    (hc : L₂ ≤ centralizer (L₁ : Set G)) (h₁H : L₁ ≤ H) (h₂H : L₂ ≤ H) :
    2 ≤ primeRank 3 H := by
  obtain ⟨E, he, hcard, hEL⟩ := nine_of_commuting_blocks hL₁ hL₂ hc
  let := he
  have hEH := hEL.trans (sup_le h₁H h₂H)
  let : IsElementaryAbelian 3 (E.subgroupOf H) := IsElementaryAbelian.subgroupOf hEH
  apply IsElementaryAbelian.primeRank_ge_of_card (E.subgroupOf H)
  exact (Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv).trans hcard

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
